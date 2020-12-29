use crate::smallvm::ParsedInstr;
use crate::{partial_execution::*, FILES_PROCESSED};
use anyhow::Result;
use bitflags::bitflags;
use cpython::{PyBytes, PyDict, PyList, PyModule, PyObject, PyResult, Python, PythonObject};
use log::{debug, trace};
use num_bigint::ToBigInt;
use petgraph::algo::astar;
use petgraph::algo::dijkstra;
use petgraph::graph::{EdgeIndex, Graph, NodeIndex};
use petgraph::visit::{Bfs, EdgeRef};
use petgraph::Direction;
use petgraph::IntoWeightedEdge;
use py_marshal::{Code, Obj};
use pydis::prelude::*;
use std::collections::{BTreeSet, HashMap};
use std::fmt;
use std::path::Path;
use std::rc::Rc;
use std::sync::Arc;

type TargetOpcode = pydis::opcode::Python27;

bitflags! {
    #[derive(Default)]
    pub struct BasicBlockFlags: u32 {
        /// Offsets have already been updated on this node
        const OFFSETS_UPDATED = 0b00000001;

        /// Branch target has already been updated on this node
        const BRANCHES_UPDATED = 0b00000010;

        /// Bytecode has been written for this node
        const BYTECODE_WRITTEN = 0b00000100;

        /// This node contains a condition which could be statically asserted
        const CONSTEXPR_CONDITION = 0b00001000;

        /// This node must be kept (in some capacity) as it's
        const USED_IN_EXECUTION = 0b00010000;

        /// This node has already been checked for constexpr conditions which may be removed
        const CONSTEXPR_CHECKED = 0b00100000;

        /// This node has already had a JUMP_FORWARD 0 inserted
        const JUMP0_INSERTED = 0b01000000;
    }
}

#[derive(Debug, Copy, Clone, Ord, PartialOrd, Eq, PartialEq)]
pub enum EdgeWeight {
    NonJump,
    Jump,
}
impl fmt::Display for EdgeWeight {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        writeln!(f, "{:?}", self)
    }
}

/// Represents a single block of code up until its next branching point
#[derive(Debug, Default)]
pub struct BasicBlock {
    /// Offset of the first instruction in this BB
    pub start_offset: u64,
    /// Offset of the last instruction in this BB (note: this is the START of the last instruction)
    pub end_offset: u64,
    /// Instructions contained within this BB
    pub instrs: Vec<ParsedInstr>,
    /// Whether this BB contains invalid instructions
    pub has_bad_instrs: bool,
    /// Flags used for internal purposes
    pub flags: BasicBlockFlags,
}

impl fmt::Display for BasicBlock {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let mut offset = self.start_offset;
        for (i, instr) in self.instrs.iter().enumerate() {
            match instr {
                ParsedInstr::Good(instr) => {
                    writeln!(f, "{} @ {} {}", i, offset, instr)?;
                    offset += instr.len() as u64;
                }
                ParsedInstr::Bad => {
                    writeln!(f, "BAD_INSTR")?;
                }
            }
        }

        Ok(())
    }
}

impl BasicBlock {
    /// Splits a basic block at the target absolute offset. The instruction index is calculated
    /// on-demand, walking the instructions and adding their length until the desired offset is found.
    pub fn split(&mut self, offset: u64) -> (u64, BasicBlock) {
        // It does indeed land in the middle of this block. Let's figure out which
        // instruction it lands on
        let mut ins_offset = self.start_offset;
        let mut ins_index = None;
        trace!("splitting at {:?}, {:#?}", offset, self);
        for (i, ins) in self.instrs.iter().enumerate() {
            if offset == ins_offset {
                ins_index = Some(i);
                break;
            }

            ins_offset += match ins {
                ParsedInstr::Good(i) => i.len() as u64,
                _ => 1,
            }
        }

        let ins_index = ins_index.unwrap();

        let (new_bb_ins, curr_ins) = self.instrs.split_at(ins_index);

        let split_bb = BasicBlock {
            start_offset: self.start_offset,
            end_offset: ins_offset - new_bb_ins.last().unwrap().unwrap().len() as u64,
            instrs: new_bb_ins.to_vec(),
            ..Default::default()
        };

        self.start_offset = ins_offset;
        self.instrs = curr_ins.to_vec();

        (ins_offset, split_bb)
    }
}

/// A code object represented as a graph
pub struct CodeGraph {
    pub(crate) root: NodeIndex,
    code: Arc<Code>,
    pub(crate) graph: Graph<BasicBlock, EdgeWeight>,
}

impl CodeGraph {
    /// Converts bytecode to a graph. Returns the root node index and the graph.
    pub fn from_code(code: Arc<Code>) -> Result<CodeGraph> {
        let debug = false;

        let analyzed_instructions = crate::smallvm::const_jmp_instruction_walker(
            code.code.as_slice(),
            Arc::clone(&code.consts),
            |_instr, _offset| {
                // We don't care about instructions that are executed
                crate::smallvm::WalkerState::Continue
            },
        )?;

        let copy = analyzed_instructions.clone();
        if true || debug {
            trace!("analyzed\n{:#?}", analyzed_instructions);
        }

        let mut curr_basic_block = BasicBlock::default();
        let mut code_graph = petgraph::Graph::<BasicBlock, EdgeWeight>::new();
        let mut edges = vec![];
        let mut root_node_id = None;
        let mut has_invalid_jump_sites = false;

        let mut join_at_queue = Vec::new();

        for (offset, instr) in analyzed_instructions {
            if curr_basic_block.instrs.is_empty() {
                curr_basic_block.start_offset = offset;
            }

            // If this is a bad opcode let's abort this BB immediately
            let instr = match instr {
                ParsedInstr::Good(instr) => {
                    // valid instructions always get added to the previous bb
                    curr_basic_block
                        .instrs
                        .push(ParsedInstr::Good(instr.clone()));
                    instr
                }
                ParsedInstr::Bad => {
                    // calculate the current position in this bb for this opcode
                    let mut block_end_offset = curr_basic_block.start_offset;
                    for instr in &curr_basic_block.instrs {
                        block_end_offset += instr.unwrap().len() as u64;
                    }

                    // something jumped us into the middle of a bb -- we need to
                    // not add this bad instruction here
                    if block_end_offset > offset {
                        // we are not adding this instruction -- it's a bad target site
                        continue;
                    }
                    curr_basic_block.end_offset = offset;
                    curr_basic_block.instrs.push(ParsedInstr::Bad);
                    curr_basic_block.has_bad_instrs = true;
                    let node_idx = code_graph.add_node(curr_basic_block);
                    if root_node_id.is_none() {
                        root_node_id = Some(node_idx);
                    }

                    curr_basic_block = BasicBlock::default();
                    continue;
                }
            };

            if matches!(
                instr.opcode,
                TargetOpcode::RETURN_VALUE | TargetOpcode::RAISE_VARARGS
            ) {
                curr_basic_block.end_offset = offset;
                // We need to see if a previous BB landed in the middle of this block.
                // If so, we should split it
                for (_from, to, weight) in &edges {
                    let _weight = *weight;
                    // Check if the target site was to a bad opcode...
                    if let ParsedInstr::Bad = &copy[to] {
                        // ignore this one
                        continue;
                    }

                    if *to > curr_basic_block.start_offset && *to <= curr_basic_block.end_offset {
                        let (ins_offset, split_bb) = curr_basic_block.split(*to);
                        edges.push((split_bb.end_offset, ins_offset, EdgeWeight::NonJump));
                        code_graph.add_node(split_bb);

                        break;
                    }
                }
                let node_idx = code_graph.add_node(curr_basic_block);
                if root_node_id.is_none() {
                    root_node_id = Some(node_idx);
                }

                curr_basic_block = BasicBlock::default();
                continue;
            }

            let next_instr = offset + instr.len() as u64;
            // whether or not this next instruction is where a different code path
            // joins
            let next_is_join = join_at_queue
                .last()
                .map_or(false, |next_join| next_instr == *next_join);
            // If this is the end of this basic block...
            if instr.opcode.is_jump() || next_is_join {
                if next_is_join {
                    join_at_queue.pop();
                }

                curr_basic_block.end_offset = offset;

                // We need to see if a previous BB landed in the middle of this block.
                // If so, we should split it
                let mut split_at = BTreeSet::new();
                for (_from, to, weight) in &edges {
                    if curr_basic_block.start_offset == 755 {}
                    let _weight = *weight;
                    if *to > curr_basic_block.start_offset && *to <= curr_basic_block.end_offset {
                        split_at.insert(*to);
                    }
                }

                // Push the next instruction
                if instr.opcode.is_conditional_jump()
                    || instr.opcode.is_other_conditional_jump()
                    || (!instr.opcode.is_jump())
                {
                    edges.push((curr_basic_block.end_offset, next_instr, EdgeWeight::NonJump));
                }

                let mut next_bb_end = None;
                if instr.opcode.is_jump() {
                    let target = if instr.opcode.is_absolute_jump() {
                        instr.arg.unwrap() as u64
                    } else {
                        offset + instr.len() as u64 + instr.arg.unwrap() as u64
                    };

                    let bad_jump_target =
                        matches!(&copy.get(&target), Some(ParsedInstr::Bad) | None);
                    has_invalid_jump_sites |= bad_jump_target;

                    let edge_weight = if matches!(
                        instr.opcode,
                        TargetOpcode::JUMP_FORWARD | TargetOpcode::JUMP_ABSOLUTE,
                    ) {
                        EdgeWeight::NonJump
                    } else {
                        EdgeWeight::Jump
                    };
                    if bad_jump_target {
                        // we land on a bad instruction. we should just make an edge to
                        // our known "invalid jump site"
                        edges.push((curr_basic_block.end_offset, 0xFFFF, edge_weight));
                    } else {
                        edges.push((curr_basic_block.end_offset, target, edge_weight));
                    }

                    // Check if this block is self-referencing
                    if target > curr_basic_block.start_offset
                        && target <= curr_basic_block.end_offset
                    {
                        println!("overriding split at?");
                        split_at.insert(target);
                    } else if !bad_jump_target {
                        // Check if this jump lands us in the middle of a block that's already
                        // been parsed
                        if let Some(root) = root_node_id.as_ref() {
                            // Special case for splitting up an existing node we're pointing to
                            for nx in code_graph.node_indices() {
                                let target_node = &mut code_graph[nx];
                                if target > target_node.start_offset
                                    && target <= target_node.end_offset
                                {
                                    let (ins_offset, split_bb) = target_node.split(target);
                                    edges.push((
                                        split_bb.end_offset,
                                        ins_offset,
                                        EdgeWeight::NonJump,
                                    ));
                                    let new_node_id = code_graph.add_node(split_bb);
                                    if nx == *root {
                                        root_node_id = Some(new_node_id);
                                    }
                                    break;
                                }
                            }
                        }
                    }

                    if instr.opcode.is_conditional_jump() {
                        // We use this to force the "else" basic block to end
                        // at a set position
                        next_bb_end = Some(target);
                    }
                }

                for split_at in split_at {
                    let (ins_offset, split_bb) = curr_basic_block.split(split_at);
                    println!("{}", ins_offset);
                    edges.push((split_bb.end_offset, ins_offset, EdgeWeight::NonJump));
                    code_graph.add_node(split_bb);
                }

                let node_idx = code_graph.add_node(curr_basic_block);
                if root_node_id.is_none() {
                    root_node_id = Some(node_idx);
                }

                curr_basic_block = BasicBlock::default();
                if let Some(next_bb_end) = next_bb_end {
                    join_at_queue.push(next_bb_end);
                }
            }
        }

        if has_invalid_jump_sites {
            let _invalid_jump_site = code_graph.add_node(BasicBlock {
                start_offset: 0xFFFF,
                end_offset: 0xFFFF,
                instrs: vec![ParsedInstr::Bad],
                has_bad_instrs: true,
                ..Default::default()
            });
        }

        let edges = edges
            .iter()
            .filter_map(|(from, to, weight)| {
                let new_edge = (
                    code_graph
                        .node_indices()
                        .find(|i| code_graph[*i].end_offset == *from),
                    code_graph
                        .node_indices()
                        .find(|i| code_graph[*i].start_offset == *to),
                );

                if new_edge.0.is_some() && new_edge.1.is_some() {
                    Some((new_edge.0.unwrap(), new_edge.1.unwrap(), weight).into_weighted_edge())
                } else {
                    None
                }
            })
            .collect::<Vec<_>>();

        code_graph.extend_with_edges(edges.as_slice());

        Ok(CodeGraph {
            root: root_node_id.unwrap(),
            graph: code_graph,
            code: Arc::clone(&code),
        })
    }

    /// Write out the current graph in dot format. The file will be output to current directory, named
    /// $FILENUMBER_$FILENAME_$NAME_$STAGE.dot. This function will check global args to see if
    /// dot writing was enabled
    pub fn write_dot(&self, stage: &str) {
        if cfg!(test) || !crate::ARGS.get().unwrap().graphs {
            return;
        }

        self.force_write_dot(
            crate::FILES_PROCESSED
                .get()
                .unwrap()
                .load(std::sync::atomic::Ordering::Relaxed),
            stage,
        );
    }

    /// Write out the current graph in dot format. The file will be output to current directory, named
    /// $FILENUMBER_$FILENAME_$NAME_$STAGE.dot
    pub fn force_write_dot(&self, file_num: usize, stage: &str) {
        use petgraph::dot::{Config, Dot};

        let filename = format!(
            "{}_{}_{}_{}.dot",
            file_num, stage, self.code.filename, self.code.name,
        );

        std::fs::write(
            &filename,
            format!("{}", Dot::with_config(&self.graph, &[Config::EdgeNoLabel])),
        )
        .unwrap_or_else(|e| panic!("failed to write dot file to {}: {}", filename, e));
    }

    /// Removes conditions that can be statically evaluated to be constant.
    pub(crate) fn remove_const_conditions(
        &mut self,
        mapped_function_names: &mut HashMap<String, String>,
    ) {
        let mut execution_path = ExecutionPath::default();

        let completed_paths = perform_partial_execution(
            self.root,
            self,
            &mut execution_path,
            mapped_function_names,
            Arc::clone(&self.code),
        );

        self.write_dot("after_dead");

        let mut nodes_to_remove = std::collections::BTreeSet::<NodeIndex>::new();
        let mut insns_to_remove = HashMap::<NodeIndex, std::collections::BTreeSet<usize>>::new();

        // We want to pre-compute which nodes were used by each path. This will allow us to determine the
        // set of paths not taken which can be removed.
        let mut node_branch_direction = HashMap::<NodeIndex, EdgeWeight>::new();
        let mut potentially_unused_nodes = BTreeSet::<NodeIndex>::new();

        // TODO: high runtime complexity
        for path in &completed_paths {
            let conditions_reached = path.condition_results.iter().filter_map(|(node, result)| {
                if result.is_some() {
                    Some((node, result.as_ref().unwrap()))
                } else {
                    None
                }
            });

            'conditions: for (node, result) in conditions_reached {
                self.graph[*node].flags |= BasicBlockFlags::USED_IN_EXECUTION;

                // we already did the work for this node
                if node_branch_direction.contains_key(&node) {
                    continue;
                }

                let branch_taken = result.0;

                let mut path_instructions = vec![];

                for other_path in &completed_paths {
                    match other_path.condition_results.get(&node) {
                        Some(Some(current_path_value)) => {
                            // we have a mismatch -- we cannot safely remove this
                            if branch_taken != current_path_value.0 {
                                continue 'conditions;
                            } else {
                                // these match!
                                path_instructions
                                    .extend_from_slice(current_path_value.1.as_slice());
                            }
                        }
                        Some(None) => {
                            // this path was unable to evaluate this condition
                            // and therefore we cannot safely remove this value
                            continue 'conditions;
                        }
                        None => {
                            // this branch never hit this bb -- this is safe to remove
                        }
                    }
                }

                // We've found that all nodes agree on this value. Let's add the
                // related instructions to our list of instructions to remove
                for (node, idx) in path_instructions {
                    insns_to_remove.entry(node).or_default().insert(idx);
                }

                node_branch_direction.insert(*node, branch_taken);

                // We know which branch all of these nodes took, so therefore we also know
                // which branch they *did not* take. Let's remove the edge
                // for the untaken paths.
                let unused_path = self
                    .graph
                    .edges_directed(*node, Direction::Outgoing)
                    .find_map(|e| {
                        if *e.weight() != branch_taken {
                            Some((e.id(), e.target()))
                        } else {
                            None
                        }
                    })
                    .unwrap();

                potentially_unused_nodes.insert(unused_path.1);
                self.graph.remove_edge(unused_path.0);
            }
        }

        if node_branch_direction.is_empty() {
            // no obfuscation?
            return;
        }

        self.write_dot("unused_partially_removed_edges");

        // Now that we've figured out which instructions to remove, and which nodes
        // are required for execution, let's figure out the set of nodes which we
        // _know_ are never used
        for nx in self.graph.node_indices() {
            // Our criteria for removing nodes is as follows:
            // 1. It must not be any node we've reached
            // 2. It must not be downgraph from any node we've reached (ignoring
            //    cyclic nodes)

            trace!("node incides testing: {:#?}", self.graph[nx]);
            // This node is used -- it must be kept
            if self.graph[nx]
                .flags
                .contains(BasicBlockFlags::USED_IN_EXECUTION)
            {
                trace!("ignoring");
                continue;
            }

            let has_used_parent = node_branch_direction
                .keys()
                .any(|used_nx| self.is_downgraph(*used_nx, nx));
            trace!("has_used_parent? {:#?}", has_used_parent);

            // We don't have any paths to this node from nodes which are _actually_ used. We should
            // remove it
            if !has_used_parent {
                nodes_to_remove.insert(nx);

                // Remove this edge to any children
                let child_edges = self
                    .graph
                    .edges_directed(nx, Direction::Outgoing)
                    .map(|e| e.id())
                    .collect::<Vec<_>>();

                self.graph.retain_edges(|_g, edge| {
                    !child_edges.iter().any(|child_edge| *child_edge == edge)
                });
            }
        }

        self.write_dot("unused_all_removed_edges");

        for (nx, insns_to_remove) in insns_to_remove {
            for ins_idx in insns_to_remove.iter().rev().cloned() {
                let current_node = &mut self.graph[nx];
                current_node.instrs.remove(ins_idx);
            }
        }

        self.write_dot("instructions_removed");

        // go over the empty nodes, merge them into their parent
        for node in self.graph.node_indices() {
            self.write_dot("last_merged");
            // TODO: This leaves some nodes that are empty
            if self.graph[node].instrs.is_empty() {
                let outgoing_nodes = self
                    .graph
                    .edges_directed(node, Direction::Outgoing)
                    .map(|e| e.target())
                    .filter(|target| {
                        // make sure these nodes aren't circular
                        !self.is_downgraph(*target, node)
                    })
                    .collect::<Vec<_>>();

                assert!(outgoing_nodes.len() <= 1);

                if let Some(child) = outgoing_nodes.first() {
                    self.join_block(node, *child);
                    nodes_to_remove.insert(*child);
                }
            }
            self.write_dot("last_merged");
        }

        let mut needs_new_root = false;
        let root = self.root;
        self.graph.retain_nodes(|g, node| {
            if nodes_to_remove.contains(&node) {
                trace!("removing node starting at: {}", g[node].start_offset);
                if node == root {
                    // find the new root
                    needs_new_root = true;
                }
                false
            } else {
                true
            }
        });

        self.write_dot("target");

        if needs_new_root {
            trace!("{:#?}", self.graph.node_indices().collect::<Vec<_>>());
            self.root = self.graph.node_indices().next().unwrap();
        }
        trace!("root node is now: {:#?}", self.graph[self.root]);
    }

    pub(crate) fn clear_flags(&mut self, root: NodeIndex, flags: BasicBlockFlags) {
        let mut bfs = Bfs::new(&self.graph, root);
        while let Some(nx) = bfs.next(&self.graph) {
            self.graph[nx].flags.remove(flags);
        }
    }

    /// Updates basic block offsets following the expected code flow order. i.e. non-target conditional jumps will always
    /// be right after the jump instruction and the point at which the two branches "meet" will be sequential.
    pub(crate) fn update_bb_offsets(&mut self) {
        let mut current_offset = 0;
        let mut stop_at_queue = Vec::new();
        let mut node_queue = Vec::new();
        let mut updated_nodes = BTreeSet::new();
        node_queue.push(self.root);
        trace!("beginning bb offset updating visitor");
        while let Some(nx) = node_queue.pop() {
            trace!("current: {:#?}", self.graph[nx]);
            if let Some(stop_at) = stop_at_queue.last() {
                if *stop_at == nx {
                    stop_at_queue.pop();
                }
            }

            if updated_nodes.contains(&nx) {
                continue;
            }

            updated_nodes.insert(nx);

            let current_node = &mut self.graph[nx];

            trace!("current offset: {}", current_offset);
            let end_offset = current_node
                .instrs
                .iter()
                .fold(0, |accum, instr| accum + instr.unwrap().len());

            let end_offset = end_offset as u64;
            current_node.start_offset = current_offset;
            current_node.end_offset = current_offset
                + (end_offset - current_node.instrs.last().unwrap().unwrap().len() as u64);

            current_offset += end_offset;

            trace!("next offset: {}", current_offset);

            let mut targets = self
                .graph
                .edges_directed(nx, Direction::Outgoing)
                .map(|edge| (edge.target(), *edge.weight()))
                .collect::<Vec<_>>();

            // Sort the targets so that the non-branch path is last. THIS IS IMPORTANT!!!!!
            // we need to ensure that the path we're taking is added FIRST so that it's further
            // down the stack
            targets.sort_by(|(_a, aweight), (_b, bweight)| bweight.cmp(aweight));

            // Add the non-constexpr path to the "stop_at_queue" so that we don't accidentally
            // go down that path before handling it ourself
            let jump_path = targets.iter().find_map(|(target, weight)| {
                if *weight == EdgeWeight::Jump {
                    Some(*target)
                } else {
                    None
                }
            });

            if let Some(jump_path) = jump_path {
                trace!("jump path is to: {:#?}", self.graph[jump_path])
            }

            for (target, _weight) in targets {
                trace!("target loop");
                // If this is the next node in the nodes to ignore, don't add it
                if let Some(pending) = stop_at_queue.last() {
                    trace!("Pending: {:#?}", self.graph[*pending]);
                    if *pending == target {
                        continue;
                    }

                    // we need to find this path to see if it goes through a node that has already
                    // had its offsets touched
                    if self.is_downgraph(*pending, target) {
                        let path = astar(
                            &self.graph,
                            *pending,
                            |finish| finish == target,
                            |_e| 0,
                            |_| 0,
                        )
                        .unwrap()
                        .1;
                        let goes_through_updated_node =
                            path.iter().any(|node| updated_nodes.contains(node));

                        // If this does not go through an updated node, we can ignore
                        // the fact that the target is downgraph
                        if !goes_through_updated_node {
                            continue;
                        }
                    }
                }

                if updated_nodes.contains(&target) {
                    continue;
                }

                node_queue.push(target);
            }

            if let Some(jump_path) = jump_path {
                if !updated_nodes.contains(&jump_path) {
                    // the other node may add this one
                    if let Some(pending) = stop_at_queue.last() {
                        if !self.is_downgraph(*pending, jump_path) {
                            stop_at_queue.push(jump_path);
                        }
                    } else {
                        stop_at_queue.push(jump_path);
                    }
                }
            }
        }
    }

    /// Update branching instructions to reflect the correct offset for their target, which may have changed since the
    /// graph was created.
    pub(crate) fn update_branches(&mut self) {
        let mut updated_nodes = BTreeSet::new();

        let mut bfs = Bfs::new(&self.graph, self.root);
        while let Some(nx) = bfs.next(&self.graph) {
            updated_nodes.insert(nx);

            // Update any paths to this node -- we need to update their jump instructions
            // if they exist
            let incoming_edges = self
                .graph
                .edges_directed(nx, Direction::Incoming)
                .map(|edge| (*edge.weight(), edge.source()))
                .collect::<Vec<_>>();

            for (weight, incoming_edge) in incoming_edges {
                let outgoing_edges_from_parent = self
                    .graph
                    .edges_directed(incoming_edge, Direction::Outgoing)
                    .count();

                // We only update edges that are jumping to us
                if weight != EdgeWeight::Jump && outgoing_edges_from_parent > 1 {
                    continue;
                }

                let source_node = &mut self.graph[incoming_edge];
                let mut last_ins = source_node.instrs.last_mut().unwrap().unwrap();

                if !last_ins.opcode.is_jump() {
                    continue;
                }

                assert!(last_ins.opcode.has_arg());

                let last_ins_len = last_ins.len();

                let target_node = &self.graph[nx];
                let target_node_start = target_node.start_offset;

                let source_node = &mut self.graph[incoming_edge];
                let end_of_jump_ins = source_node.end_offset + last_ins_len as u64;

                if last_ins.opcode == TargetOpcode::JUMP_ABSOLUTE
                    && target_node_start > source_node.start_offset
                {
                    unsafe { Rc::get_mut_unchecked(&mut last_ins) }.opcode =
                        TargetOpcode::JUMP_FORWARD;
                }

                if last_ins.opcode == TargetOpcode::JUMP_FORWARD
                    && target_node_start < end_of_jump_ins
                {
                    unsafe { Rc::get_mut_unchecked(&mut last_ins) }.opcode =
                        TargetOpcode::JUMP_ABSOLUTE;
                }

                let last_ins_is_abs_jump = last_ins.opcode.is_absolute_jump();

                let new_arg = if last_ins_is_abs_jump {
                    target_node_start
                } else {
                    if target_node_start < source_node.end_offset {
                        let target_node = &self.graph[nx];
                        let source_node = &self.graph[incoming_edge];
                        panic!(
                            "target start < source end offset\nsource: {:#?},\ntarget {:#?}",
                            source_node, target_node
                        );
                    }
                    target_node_start - end_of_jump_ins
                };

                let mut last_ins = source_node.instrs.last_mut().unwrap().unwrap();
                unsafe { Rc::get_mut_unchecked(&mut last_ins) }.arg = Some(new_arg as u16);
            }
        }
    }

    /// Write out the object bytecode.
    pub(crate) fn write_bytecode(&mut self, root: NodeIndex, new_bytecode: &mut Vec<u8>) {
        let mut stop_at_queue = Vec::new();
        let mut node_queue = Vec::new();
        node_queue.push(root);
        trace!("beginning bytecode bb visitor");
        'node_visitor: while let Some(nx) = node_queue.pop() {
            if let Some(stop_at) = stop_at_queue.last() {
                if *stop_at == nx {
                    stop_at_queue.pop();
                }
            }

            let current_node = &mut self.graph[nx];
            if current_node
                .flags
                .intersects(BasicBlockFlags::BYTECODE_WRITTEN)
            {
                continue;
            }

            current_node.flags |= BasicBlockFlags::BYTECODE_WRITTEN;

            for instr in current_node.instrs.iter().map(|i| i.unwrap()) {
                new_bytecode.push(instr.opcode as u8);
                if let Some(arg) = instr.arg {
                    new_bytecode.extend_from_slice(&arg.to_le_bytes()[..]);
                }
            }

            let mut targets = self
                .graph
                .edges_directed(nx, Direction::Outgoing)
                .map(|edge| (edge.target(), *edge.weight()))
                .collect::<Vec<_>>();

            // Sort the targets so that the non-branch path is last
            targets.sort_by(|(_a, aweight), (_b, bweight)| bweight.cmp(aweight));

            // Add the non-constexpr path to the "stop_at_queue" so that we don't accidentally
            // go down that path before handling it ourself
            let jump_path = targets.iter().find_map(|(target, weight)| {
                if *weight == EdgeWeight::Jump {
                    Some(*target)
                } else {
                    None
                }
            });

            for (target, _weight) in targets {
                // If this is the next node in the nodes to ignore, don't add it
                if let Some(pending) = stop_at_queue.last() {
                    // we need to find this path to see if it goes through a node that has already
                    // had its offsets touched
                    if self.is_downgraph(*pending, target) {
                        let path = astar(
                            &self.graph,
                            *pending,
                            |finish| finish == target,
                            |_e| 0,
                            |_| 0,
                        )
                        .unwrap()
                        .1;
                        let mut goes_through_updated_node = false;
                        for node in path {
                            if self.graph[node]
                                .flags
                                .intersects(BasicBlockFlags::BYTECODE_WRITTEN)
                            {
                                goes_through_updated_node = true;
                                break;
                            }
                        }

                        // If this does not go through an updated node, we can ignore
                        // the fact that the target is downgraph
                        if !goes_through_updated_node {
                            continue;
                        }
                    }
                    if *pending == target {
                        continue;
                    }
                }

                if self.graph[target]
                    .flags
                    .contains(BasicBlockFlags::BYTECODE_WRITTEN)
                {
                    continue;
                }

                node_queue.push(target);
            }

            if let Some(jump_path) = jump_path {
                if !self.graph[jump_path]
                    .flags
                    .contains(BasicBlockFlags::BYTECODE_WRITTEN)
                {
                    // the other node may add this one
                    if let Some(pending) = stop_at_queue.last() {
                        if !self.is_downgraph(*pending, jump_path) {
                            stop_at_queue.push(jump_path);
                        }
                    } else {
                        stop_at_queue.push(jump_path);
                    }
                }
            }
        }
    }

    /// Fixes any [`BasicBlock`]s with bad instructions. This essentially replaces all of the
    /// instructions in a basic block with the appropriate number of `POP_TOP` instructions to clear
    /// the stack, *try* loading the `None` const item, and returning. If `None` is not in the
    /// const items, then const index 0 is returned.
    pub(crate) fn fix_bbs_with_bad_instr(&mut self, root: NodeIndex, code: &Code) {
        let mut bfs = Bfs::new(&self.graph, root);
        while let Some(nx) = bfs.next(&self.graph) {
            let current_node = &mut self.graph[nx];
            // We only operate on nodes with bad instructions
            if !current_node.has_bad_instrs {
                continue;
            }

            // We're going to change the instructions in here to return immediately
            current_node.instrs.clear();

            // We need to walk instructions to this point to get the stack size so we can balance it
            let path = astar(&self.graph, root, |finish| finish == nx, |_e| 0, |_| 0)
                .unwrap()
                .1;
            let mut stack_size = 0;
            for (idx, node) in path.iter().cloned().enumerate() {
                if node == nx {
                    break;
                }

                for instr in &self.graph[node].instrs {
                    // these ones pop only if we're not taking the branch
                    if matches!(
                        instr.unwrap().opcode,
                        TargetOpcode::JUMP_IF_TRUE_OR_POP | TargetOpcode::JUMP_IF_FALSE_OR_POP
                    ) {
                        // Grab the edge from this node to the next
                        let edge = self.graph.find_edge(node, path[idx + 1]).unwrap();
                        if *self.graph.edge_weight(edge).unwrap() == EdgeWeight::NonJump {
                            stack_size -= 1;
                        } else {
                            // do nothing if we take the branch
                        }
                    } else {
                        stack_size += instr.unwrap().stack_adjustment_after();
                    }
                }
            }

            let current_node = &mut self.graph[nx];
            for _i in 0..stack_size {
                current_node
                    .instrs
                    .push(ParsedInstr::Good(Rc::new(Instruction {
                        opcode: TargetOpcode::POP_TOP,
                        arg: None,
                    })));
            }

            // Find the `None` constant object
            let const_idx = code
                .consts
                .iter()
                .enumerate()
                .find_map(|(idx, obj)| {
                    if matches!(obj, Obj::None) {
                        Some(idx)
                    } else {
                        None
                    }
                })
                .unwrap_or(0);
            current_node
                .instrs
                .push(ParsedInstr::Good(Rc::new(Instruction {
                    opcode: TargetOpcode::LOAD_CONST,
                    arg: Some(const_idx as u16),
                })));
            current_node
                .instrs
                .push(ParsedInstr::Good(Rc::new(Instruction {
                    opcode: TargetOpcode::RETURN_VALUE,
                    arg: None,
                })));

            current_node.has_bad_instrs = false;
        }
    }

    /// Insert `JUMP_FORWARD 0` instructions at locations that jump in to
    pub(crate) fn insert_jump_0(&mut self, root: NodeIndex) {
        let mut stop_at_queue = Vec::new();
        let mut node_queue = Vec::new();
        node_queue.push(root);
        trace!("beginning insert jump 0 visitor");
        'node_visitor: while let Some(nx) = node_queue.pop() {
            if let Some(stop_at) = stop_at_queue.last() {
                if *stop_at == nx {
                    stop_at_queue.pop();
                }
            }

            let current_node = &mut self.graph[nx];
            if current_node
                .flags
                .intersects(BasicBlockFlags::JUMP0_INSERTED)
            {
                continue;
            }

            current_node.flags |= BasicBlockFlags::JUMP0_INSERTED;

            let mut targets = self
                .graph
                .edges_directed(nx, Direction::Outgoing)
                .map(|edge| (edge.target(), *edge.weight()))
                .collect::<Vec<_>>();

            // Sort the targets so that the non-branch path is last
            targets.sort_by(|(_a, aweight), (_b, bweight)| bweight.cmp(aweight));

            // Add the non-constexpr path to the "stop_at_queue" so that we don't accidentally
            // go down that path before handling it ourself
            let jump_path = targets.iter().find_map(|(target, weight)| {
                if *weight == EdgeWeight::Jump {
                    Some(*target)
                } else {
                    None
                }
            });

            for (target, _weight) in targets {
                // If this is the next node in the nodes to ignore, don't add it
                if let Some(pending) = stop_at_queue.last() {
                    // we need to find this path to see if it goes through a node that has already
                    // had its offsets touched
                    if self.is_downgraph(*pending, target) {
                        let path = astar(
                            &self.graph,
                            *pending,
                            |finish| finish == target,
                            |_e| 0,
                            |_| 0,
                        )
                        .unwrap()
                        .1;
                        let mut goes_through_updated_node = false;
                        for node in path {
                            if self.graph[node]
                                .flags
                                .intersects(BasicBlockFlags::JUMP0_INSERTED)
                            {
                                goes_through_updated_node = true;
                                break;
                            }
                        }

                        // If this does not go through an updated node, we can ignore
                        // the fact that the target is downgraph
                        if !goes_through_updated_node {
                            continue;
                        }
                    }
                    if *pending == target {
                        continue;
                    }
                }

                if self.graph[target]
                    .flags
                    .contains(BasicBlockFlags::JUMP0_INSERTED)
                {
                    continue;
                }

                node_queue.push(target);
            }

            if let Some(jump_path) = jump_path {
                if !self.graph[jump_path]
                    .flags
                    .contains(BasicBlockFlags::JUMP0_INSERTED)
                {
                    // the other node may add this one
                    if let Some(pending) = stop_at_queue.last() {
                        if !self.is_downgraph(*pending, jump_path) {
                            stop_at_queue.push(jump_path);
                        } else {
                            // ensure that this does not end in a jump
                            let current_node = &mut self.graph[nx];
                            if let Some(last) = current_node.instrs.last().map(|i| i.unwrap()) {
                                if !last.opcode.is_jump() {
                                    // insert a jump 0
                                    current_node.instrs.push(crate::smallvm::ParsedInstr::Good(
                                        Rc::new(Instruction {
                                            opcode: TargetOpcode::JUMP_FORWARD,
                                            arg: Some(0),
                                        }),
                                    ));
                                }
                            }
                        }
                    } else {
                        stop_at_queue.push(jump_path);
                    }
                }
            }
        }
    }

    /// Join redundant basic blocks together. This will take blocks like `(1) [NOP] -> (2) [LOAD_CONST 3]` and merge
    /// the second node into the first, forming `(1) [NOP, LOAD CONST 3]`. The 2nd node will be deleted and all of its outgoing
    /// edges will now originate from the merged node (1).
    ///
    /// This can only occur if (1) only has one outgoing edge, and (2) has only 1 incoming edge (1).
    pub(crate) fn join_blocks(&mut self) {
        let mut nodes_to_remove = BTreeSet::new();
        let mut merge_map = std::collections::BTreeMap::new();

        let mut bfs = Bfs::new(&self.graph, self.root);
        let mut nodes = vec![];
        while let Some(nx) = bfs.next(&self.graph) {
            nodes.push(nx);
        }

        for nx in nodes {
            let num_incoming = self.graph.edges_directed(nx, Direction::Incoming).count();

            // Ensure only 1 node points to this location
            if num_incoming != 1 {
                continue;
            }

            // Grab the incoming edge to this node so we can see how many outgoing the source has. We might be able
            // to combine these nodes
            let incoming_edge = self
                .graph
                .edges_directed(nx, Direction::Incoming)
                .next()
                .unwrap();

            let mut source_node_index = incoming_edge.source();
            if let Some(merged_to) = merge_map.get(&source_node_index) {
                source_node_index = *merged_to;
            }

            let parent_outgoing_edge_count = self
                .graph
                .edges_directed(source_node_index, Direction::Outgoing)
                .count();
            if parent_outgoing_edge_count != 1 {
                continue;
            }

            // Make sure that these nodes are not circular
            let are_circular = self
                .graph
                .edges_directed(nx, Direction::Outgoing)
                .any(|edge| edge.target() == source_node_index);

            if are_circular {
                continue;
            }

            self.join_block(source_node_index, nx);

            nodes_to_remove.insert(nx);
            merge_map.insert(nx, source_node_index);
        }

        self.graph
            .retain_nodes(|_graph, node| !nodes_to_remove.contains(&node));
    }

    /// Merges dest into source
    pub fn join_block(&mut self, source_node_index: NodeIndex, dest: NodeIndex) {
        let incoming_edges = self
            .graph
            .edges_directed(dest, Direction::Incoming)
            .map(|edge| edge.id())
            .collect::<Vec<_>>();

        let outgoing_edges: Vec<(EdgeIndex, u64, EdgeWeight)> = self
            .graph
            .edges_directed(dest, Direction::Outgoing)
            .map(|edge| {
                (
                    edge.id(),
                    self.graph[edge.target()].start_offset,
                    *edge.weight(),
                )
            })
            .collect();
        let current_node = &self.graph[dest];

        let mut current_instrs = current_node.instrs.clone();
        let mut current_end_offset = current_node.end_offset;
        let parent_node = &mut self.graph[source_node_index];

        if let Some(last_instr) = parent_node.instrs.last().map(|i| i.unwrap()) {
            if last_instr.opcode.is_jump() {
                // Remove the last instruction -- this is our jump
                let removed_instruction = parent_node.instrs.pop().unwrap();

                trace!("{:?}", removed_instruction);
                assert!(!removed_instruction.unwrap().opcode.is_conditional_jump());
                current_end_offset -= removed_instruction.unwrap().len() as u64;
            }
        }

        // Adjust the merged node's offsets
        parent_node.end_offset = current_end_offset;

        // Move this node's instructions into the parent
        parent_node.instrs.append(&mut current_instrs);

        let merged_node_index = source_node_index;

        // Remove the old outgoing edges -- these are no longer valid
        self.graph.retain_edges(|_graph, edge| {
            !outgoing_edges
                .iter()
                .any(|(outgoing_index, _target_offset, _weight)| *outgoing_index == edge)
                && !incoming_edges
                    .iter()
                    .any(|incoming_index| *incoming_index == edge)
        });

        // Re-add the old node's outgoing edges
        for (_edge_index, target_offset, weight) in outgoing_edges {
            let target_index = self
                .graph
                .node_indices()
                .find(|i| self.graph[*i].start_offset == target_offset)
                .unwrap();

            // Grab this node's index
            self.graph.add_edge(merged_node_index, target_index, weight);
        }
    }

    pub fn is_downgraph(&self, source: NodeIndex, dest: NodeIndex) -> bool {
        let node_map = dijkstra(&self.graph, source, Some(dest), |_| 1);
        node_map.get(&dest).is_some()
    }

    /// Whether a node is downgraph from a node that's used in execution
    pub fn is_downgraph_from_used_node(&self, source: NodeIndex, dest: NodeIndex) -> bool {
        if let Some(path) = astar(
            &self.graph,
            source,
            |finish| finish == dest,
            |e| {
                if self.graph[e.target()]
                    .flags
                    .contains(BasicBlockFlags::USED_IN_EXECUTION)
                {
                    1
                } else {
                    0
                }
            },
            |_| 0,
        ) {
            path.0 > 0
        } else {
            false
        }
    }
}

#[cfg(test)]
pub(crate) mod tests {
    use super::*;
    use crate::smallvm::tests::*;
    use crate::{Instr, Long};
    use pydis::opcode::Instruction;

    type TargetOpcode = pydis::opcode::Python27;

    #[test]
    fn joining_multiple_jump_absolutes() {
        let mut code = default_code_obj();

        let instrs = [
            Instr!(TargetOpcode::JUMP_ABSOLUTE, 3),
            Instr!(TargetOpcode::JUMP_ABSOLUTE, 6),
            Instr!(TargetOpcode::JUMP_ABSOLUTE, 9),
            Instr!(TargetOpcode::LOAD_CONST, 0),
            Instr!(TargetOpcode::RETURN_VALUE),
        ];

        change_code_instrs(&mut code, &instrs[..]);

        let mut code_graph = CodeGraph::from_code(code).unwrap();

        code_graph.join_blocks();

        assert_eq!(code_graph.graph.node_indices().count(), 1);

        let bb = &code_graph.graph[code_graph.graph.node_indices().next().unwrap()];
        assert_eq!(bb.instrs.len(), 2);
        assert_eq!(*bb.instrs[0].unwrap(), Instr!(TargetOpcode::LOAD_CONST, 0));
        assert_eq!(*bb.instrs[1].unwrap(), Instr!(TargetOpcode::RETURN_VALUE));
    }

    #[test]
    fn joining_jump_forward() {
        let mut code = default_code_obj();

        let instrs = [
            Instr!(TargetOpcode::JUMP_ABSOLUTE, 3),
            Instr!(TargetOpcode::JUMP_ABSOLUTE, 6),
            Instr!(TargetOpcode::JUMP_FORWARD, 0),
            Instr!(TargetOpcode::LOAD_CONST, 0),
            Instr!(TargetOpcode::RETURN_VALUE),
        ];

        change_code_instrs(&mut code, &instrs[..]);

        let mut code_graph = CodeGraph::from_code(code).unwrap();

        code_graph.join_blocks();

        assert_eq!(code_graph.graph.node_indices().count(), 1);

        let bb = &code_graph.graph[code_graph.graph.node_indices().next().unwrap()];
        assert_eq!(bb.instrs.len(), 2);
        assert_eq!(*bb.instrs[0].unwrap(), Instr!(TargetOpcode::LOAD_CONST, 0));
        assert_eq!(*bb.instrs[1].unwrap(), Instr!(TargetOpcode::RETURN_VALUE));
    }
    #[test]
    fn joining_with_conditional_jump() {
        let mut code = default_code_obj();

        let instrs = [
            Instr!(TargetOpcode::JUMP_ABSOLUTE, 3),
            Instr!(TargetOpcode::JUMP_ABSOLUTE, 6),
            Instr!(TargetOpcode::POP_JUMP_IF_TRUE, 13), // jump to LOAD_CONST 1
            Instr!(TargetOpcode::LOAD_CONST, 0),
            Instr!(TargetOpcode::RETURN_VALUE),
            Instr!(TargetOpcode::LOAD_CONST, 1),
            Instr!(TargetOpcode::RETURN_VALUE),
        ];

        change_code_instrs(&mut code, &instrs[..]);

        let mut code_graph = CodeGraph::from_code(code).unwrap();

        code_graph.join_blocks();

        assert_eq!(code_graph.graph.node_indices().count(), 3);

        let expected = [
            vec![
                Instr!(TargetOpcode::POP_JUMP_IF_TRUE, 13), // jump to LOAD_CONST 1
            ],
            vec![
                Instr!(TargetOpcode::LOAD_CONST, 0),
                Instr!(TargetOpcode::RETURN_VALUE),
            ],
            vec![
                Instr!(TargetOpcode::LOAD_CONST, 1),
                Instr!(TargetOpcode::RETURN_VALUE),
            ],
        ];

        for (bb_num, nx) in code_graph.graph.node_indices().enumerate() {
            let bb = &code_graph.graph[nx];

            assert_eq!(expected[bb_num].len(), bb.instrs.len());

            for (ix, instr) in bb.instrs.iter().enumerate() {
                assert_eq!(*instr.unwrap(), expected[bb_num][ix])
            }
        }
    }

    #[test]
    fn offsets_are_updated_simple() {
        let mut code = default_code_obj();

        let instrs = [
            Instr!(TargetOpcode::JUMP_ABSOLUTE, 3),
            Instr!(TargetOpcode::JUMP_ABSOLUTE, 6),
            Instr!(TargetOpcode::JUMP_FORWARD, 0),
            Instr!(TargetOpcode::LOAD_CONST, 0),
            Instr!(TargetOpcode::RETURN_VALUE),
        ];

        change_code_instrs(&mut code, &instrs[..]);

        let mut code_graph = CodeGraph::from_code(code).unwrap();

        code_graph.join_blocks();
        code_graph.update_bb_offsets();

        assert_eq!(code_graph.graph.node_indices().count(), 1);

        let bb = &code_graph.graph[code_graph.graph.node_indices().next().unwrap()];
        assert_eq!(bb.start_offset, 0);
        assert_eq!(bb.end_offset, 3);
    }

    pub fn change_code_instrs(code: &mut Arc<Code>, instrs: &[Instruction<TargetOpcode>]) {
        let mut bytecode = vec![];

        for instr in instrs {
            serialize_instr(instr, &mut bytecode);
        }

        Arc::get_mut(code).unwrap().code = Arc::new(bytecode);
    }

    pub fn serialize_instr(instr: &Instruction<TargetOpcode>, output: &mut Vec<u8>) {
        output.push(instr.opcode as u8);
        if let Some(arg) = instr.arg {
            output.extend_from_slice(&arg.to_le_bytes()[..]);
        }
    }
}
