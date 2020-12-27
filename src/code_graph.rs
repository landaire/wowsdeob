use crate::partial_execution::*;
use crate::smallvm::ParsedInstr;
use anyhow::Result;
use bitflags::bitflags;
use cpython::{PyBytes, PyDict, PyList, PyModule, PyObject, PyResult, Python, PythonObject};
use log::{debug, trace};
use num_bigint::ToBigInt;
use petgraph::algo::astar;
use petgraph::algo::dijkstra;
use petgraph::graph::{Graph, NodeIndex};
use petgraph::visit::{Bfs, EdgeRef};
use petgraph::Direction;
use petgraph::IntoWeightedEdge;
use py_marshal::{Code, Obj};
use pydis::prelude::*;
use std::collections::HashMap;
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

        /// This node will be deleted
        const WILL_DELETE = 0b00010000;

        /// This node has already been checked for constexpr conditions which may be removed
        const CONSTEXPR_CHECKED = 0b00100000;

        /// This node has already had a JUMP_FORWARD 0 inserted
        const JUMP0_INSERTED = 0b01000000;
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
        println!("{:?}, {:#?}", offset, self);
        for (i, ins) in self.instrs.iter().enumerate() {
            println!("{} {}", ins_offset, offset);
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
    pub(crate) graph: Graph<BasicBlock, u64>,
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
        let mut code_graph = petgraph::Graph::<BasicBlock, u64>::new();
        let mut edges = vec![];
        let mut root_node_id = None;
        let mut has_invalid_jump_sites = false;

        let mut join_at_queue = Vec::new();

        let mut found_it = false;
        for (offset, instr) in analyzed_instructions {
            if offset == 58
                && instr.unwrap().opcode == TargetOpcode::LOAD_CONST
                && instr.unwrap().arg.unwrap() == 0
            {
                found_it = true;
            }
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
                    } else if *to > curr_basic_block.start_offset
                        && *to <= curr_basic_block.end_offset
                    {
                        let (ins_offset, split_bb) = curr_basic_block.split(*to);
                        edges.push((split_bb.end_offset, ins_offset, false));
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
                let mut split_at = None;
                for (_from, to, weight) in &edges {
                    let _weight = *weight;
                    if *to > curr_basic_block.start_offset && *to <= curr_basic_block.end_offset {
                        split_at = Some(*to);

                        break;
                    }
                }

                // Push the next instruction
                if instr.opcode.is_conditional_jump()
                    || instr.opcode.is_other_conditional_jump()
                    || (!instr.opcode.is_jump())
                {
                    edges.push((curr_basic_block.end_offset, next_instr, false));
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

                    if bad_jump_target {
                        // we land on a bad instruction. we should just make an edge to
                        // our known "invalid jump site"
                        edges.push((
                            curr_basic_block.end_offset,
                            0xFFFF,
                            !matches!(
                                instr.opcode,
                                TargetOpcode::JUMP_FORWARD | TargetOpcode::JUMP_ABSOLUTE,
                            ),
                        ));
                    } else {
                        edges.push((
                            curr_basic_block.end_offset,
                            target,
                            !matches!(
                                instr.opcode,
                                TargetOpcode::JUMP_FORWARD | TargetOpcode::JUMP_ABSOLUTE,
                            ),
                        ));
                    }

                    // Check if this block is self-referencing
                    if target > curr_basic_block.start_offset
                        && target <= curr_basic_block.end_offset
                    {
                        split_at = Some(target);
                    } else if !bad_jump_target {
                        // Check if this jump lands us in the middle of a block that's already
                        // been parsed
                        if let Some(root) = root_node_id.as_ref() {
                            // Special case for splitting up an existing node we're pointing to
                            for nx in code_graph.node_indices() {
                                let target_node = &mut code_graph[nx];
                                dbg!(target);
                                dbg!(target_node.start_offset);
                                dbg!(target_node.end_offset);
                                if target > target_node.start_offset
                                    && target <= target_node.end_offset
                                {
                                    println!("found");
                                    let (ins_offset, split_bb) = target_node.split(target);
                                    edges.push((split_bb.end_offset, ins_offset, false));
                                    let new_node_id = code_graph.add_node(split_bb);
                                    if nx == *root {
                                        root_node_id = Some(new_node_id);
                                    }
                                    break;
                                }
                            }
                            // if target == 102 {
                            //     panic!("yo");
                            // }
                        }
                    }

                    if instr.opcode.is_conditional_jump() {
                        // We use this to force the "else" basic block to end
                        // at a set position
                        next_bb_end = Some(target);
                    }
                }

                if let Some(split_at) = split_at {
                    let (ins_offset, split_bb) = curr_basic_block.split(split_at);
                    edges.push((split_bb.end_offset, ins_offset, false));
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

        if found_it {
            //panic!("{:#?}", code_graph);
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
                    Some(
                        (new_edge.0.unwrap(), new_edge.1.unwrap(), *weight as u64)
                            .into_weighted_edge(),
                    )
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

    pub fn write_dot(&self, stage: &str) {
        use petgraph::dot::{Config, Dot};

        let filename = format!(
            "{}_{}_{}_{}.dot",
            crate::deob::FILES_PROCESSED
                .get()
                .unwrap()
                .load(std::sync::atomic::Ordering::Relaxed),
            self.code.filename,
            self.code.name,
            stage
        );
        std::fs::write(
            &filename,
            format!("{}", Dot::with_config(&self.graph, &[Config::EdgeNoLabel])),
        )
        .unwrap_or_else(|e| panic!("failed to write dot file to {}: {}", filename, e));
    }

    pub(crate) fn remove_const_conditions(
        &mut self,
        mapped_function_names: &mut HashMap<String, String>,
    ) {
        let mut execution_path = ExecutionPath::default();

        let (nodes_to_remove, completed_paths) = perform_partial_execution(
            self.root,
            self,
            &mut execution_path,
            mapped_function_names,
            Arc::clone(&self.code),
        );

        self.write_dot("after_dead");

        println!("{:?}", nodes_to_remove);

        let mut nodes_to_remove_set = std::collections::BTreeSet::<NodeIndex>::new();
        nodes_to_remove_set.extend(nodes_to_remove.into_iter());

        let mut stop_at_queue = Vec::new();
        let mut node_queue = Vec::new();
        node_queue.push(self.root);
        println!("beginning visitor");
        let mut insns_to_remove = HashMap::<NodeIndex, std::collections::BTreeSet<usize>>::new();
        let mut node_branch_direction = HashMap::<NodeIndex, u64>::new();

        // we grab the first item just to have some conditions to reference
        //
        // TODO: high runtime complexity
        for path in &completed_paths {
            'conditions: for (node, result) in
                path.condition_results.iter().filter_map(|(node, result)| {
                    if result.is_some() {
                        Some((node, result.as_ref().unwrap()))
                    } else {
                        None
                    }
                })
            {
                // we already did the work for this node
                if insns_to_remove.contains_key(&node) {
                    continue;
                }

                let branch_taken = result.0;

                for other_path in &completed_paths {
                    match other_path.condition_results.get(&node) {
                        Some(Some(current_path_value)) => {
                            // we have a mismatch -- we cannot safely remove this
                            if branch_taken != current_path_value.0 {
                                continue 'conditions;
                            } else {
                                // this match!
                            }
                        }
                        Some(None) => {
                            // this path was unable to evaluate this condition
                            // and therefore we cannot safely remove this value
                        }
                        None => {
                            // this branch never hit this bb -- this is safe to remove
                        }
                    }
                }

                // We've found that all nodes agree on this value. Let's add the
                // related instructions to our list of instructions to remove
                for (node, idx) in &result.1 {
                    insns_to_remove.entry(*node).or_default().insert(*idx);
                }

                node_branch_direction.insert(*node, branch_taken);
            }
        }

        'node_visitor: while let Some(nx) = node_queue.pop() {
            let yes = self.graph[nx].instrs.len() > 0
                && self.graph[nx].instrs.last().unwrap().unwrap().opcode
                    == TargetOpcode::POP_JUMP_IF_TRUE
                && self.graph[nx].instrs.last().unwrap().unwrap().arg.unwrap() == 480;
            if let Some(stop_at) = stop_at_queue.last() {
                if *stop_at == nx {
                    stop_at_queue.pop();
                }
            }
            if self.graph[nx]
                .flags
                .contains(BasicBlockFlags::CONSTEXPR_CHECKED)
            {
                continue;
            }

            self.graph[nx].flags |= BasicBlockFlags::CONSTEXPR_CHECKED;

            println!("Visiting: {:#?}", self.graph[nx]);

            let mut targets = self
                .graph
                .edges_directed(nx, Direction::Outgoing)
                .map(|edge| (edge.target(), *edge.weight()))
                .collect::<Vec<_>>();

            // Sort the targets so that the constexpr path is first
            targets.sort_by(|(a, _aweight), (b, _bweight)| {
                (self.graph[*b].flags & BasicBlockFlags::CONSTEXPR_CONDITION)
                    .cmp(&(self.graph[*a].flags & BasicBlockFlags::CONSTEXPR_CONDITION))
            });

            // Add the non-constexpr path to the "stop_at_queue" so that we don't accidentally
            // go down that path before handling it ourself
            let jump_path =
                targets
                    .first()
                    .and_then(|(target, weight)| if *weight == 1 { Some(*target) } else { None });

            for (target, _weight) in targets {
                // If this is the next node in the nodes to ignore, don't add it
                if let Some(pending) = stop_at_queue.last() {
                    if *pending == target {
                        println!(
                            "skipping target {} (stop queue related)",
                            self.graph[target].start_offset
                        );
                        continue;
                    }
                }

                if self.graph[target]
                    .flags
                    .contains(BasicBlockFlags::CONSTEXPR_CHECKED)
                {
                    println!(
                        "skipping target {} (been checked)",
                        self.graph[target].start_offset
                    );
                    continue;
                }

                println!(
                    "adding target {} to node queue",
                    self.graph[target].start_offset
                );

                node_queue.push(target);
            }

            if let Some(jump_path) = jump_path {
                stop_at_queue.push(jump_path);
            }

            // Check if any of the nodes connecting to this could not be
            // solved
            let mut only_modify_self = false;
            let path_value = node_branch_direction.get(&nx);

            for source in self
                .graph
                .edges_directed(nx, Direction::Incoming)
                .map(|edge| edge.source())
                .collect::<Vec<_>>()
            {
                // if nx == NodeIndex::new(14) && counter == 1 {
                //     println!("we're in 14: {:#?}", self.graph[source]);
                // }
                let source_flags = self.graph[source].flags;
                if !source_flags
                    .intersects(BasicBlockFlags::CONSTEXPR_CONDITION | BasicBlockFlags::WILL_DELETE)
                {
                    // Ok, we have a connecting node that could not be solved. We don't touch this node.
                    let toggled_flags =
                        self.graph[nx].flags & !BasicBlockFlags::CONSTEXPR_CONDITION;

                    self.graph[nx].flags = toggled_flags;

                    // Remove this node from nodes to remove, if it exists
                    println!(
                        "removing {} from node removal list list",
                        self.graph[nx].start_offset
                    );
                    nodes_to_remove_set.remove(&nx);

                    // println!("New flags: {:#?}", self.graph[nx].flags);

                    // we may continue *only if* all paths agree on this node
                    // in this node there are isolated instructions to remove
                    if !insns_to_remove.contains_key(&nx) {
                        // Ok, we have a connecting node that could not be solved. We don't touch this node.
                        self.graph[nx].flags.remove(
                            BasicBlockFlags::CONSTEXPR_CONDITION | BasicBlockFlags::WILL_DELETE,
                        );

                        // Remove this node from nodes to remove, if it exists
                        nodes_to_remove_set.remove(&nx);
                        continue 'node_visitor;
                    } else {
                        println!(
                            "node #{:?} can bypass: {:#?}. condition: {:?}. deleting: {:?}",
                            nx, self.graph[nx].start_offset, path_value, insns_to_remove[&nx]
                        );
                        only_modify_self = true;
                    }
                    //if !nodes_with_isolated_constexprs.contains(&nx) {
                    //}
                }
            }

            if nodes_to_remove_set.contains(&nx) {
                println!("deleting entire node...");
                self.graph[nx].flags |= BasicBlockFlags::WILL_DELETE;

                // if we're deleting this node, we should delete our children too
                let outgoing_edges = self
                    .graph
                    .edges_directed(nx, Direction::Outgoing)
                    .map(|edge| {
                        println!("EDGE VALUE: {}", edge.weight());
                        (edge.id(), edge.target())
                    })
                    .collect::<Vec<_>>();

                self.graph
                    .retain_edges(|_g, e| !outgoing_edges.iter().any(|outgoing| outgoing.0 == e));
                for (_target_edge, target) in outgoing_edges.iter().cloned().rev() {
                    println!(
                        "REMOVING EDGE FROM {} TO {}",
                        self.graph[nx].start_offset, self.graph[target].start_offset
                    );
                    //self.graph.remove_edge(target_edge);

                    // check if the target has any more incoming edges
                    if self
                        .graph
                        .edges_directed(target, Direction::Incoming)
                        .count()
                        == 0
                    {
                        println!("edge count is 0, we can remove");
                        // make sure this node is flagged for removal
                        self.graph[target].flags |= BasicBlockFlags::WILL_DELETE;
                        nodes_to_remove_set.insert(target);
                    }

                    if self.graph[target].start_offset == 65535 {
                        //panic!("");
                    }
                }

                // if we're deleting this node, delete any children that are not downgraph from the target

                // continue;
            }

            // if !insns_to_remove.contains_key(&nx) {
            //     continue;
            // }
            println!("removing instructions");

            if let Some(insns_to_remove) = insns_to_remove.get(&nx) {
                for ins_idx in insns_to_remove.iter().rev().cloned() {
                    // if *code.filename == "26949592413111478" && *code.name == "50844295913873" {
                    //     panic!("1");
                    // }

                    let current_node = &self.graph[nx];
                    // If we're removing a jump, remove the related edge
                    if current_node.instrs[ins_idx]
                        .unwrap()
                        .opcode
                        .is_conditional_jump()
                    {
                        println!("PATH VALUE: {:?}", path_value);
                        if let Some(path_value) = path_value {
                            if let Some((target_edge, target)) = self
                                .graph
                                .edges_directed(nx, Direction::Outgoing)
                                .find_map(|edge| {
                                    println!("EDGE VALUE: {}", edge.weight());
                                    if *edge.weight() != *path_value {
                                        Some((edge.id(), edge.target()))
                                    } else {
                                        None
                                    }
                                })
                            {
                                println!(
                                    "REMOVING EDGE FROM {} TO {}",
                                    self.graph[nx].start_offset, self.graph[target].start_offset
                                );
                                self.graph.remove_edge(target_edge);

                                // check if the target has any more incoming edges
                                if self
                                    .graph
                                    .edges_directed(target, Direction::Incoming)
                                    .count()
                                    == 0
                                {
                                    // make sure this node is flagged for removal
                                    self.graph[target].flags |= BasicBlockFlags::WILL_DELETE;
                                    nodes_to_remove_set.insert(target);
                                }
                            }
                        }
                    }

                    let current_node = &mut self.graph[nx];
                    current_node.instrs.remove(ins_idx);
                }
            }
            if yes {
                //panic!("{:#?}", self.graph[nx]);
            }

            // Remove this node if it has no more instructions
            let current_node = &self.graph[nx];
            if current_node.instrs.is_empty() {
                // if *code.filename == "26949592413111478" && *code.name == "50844295913873" {
                //     panic!("1");
                // }
                self.graph[nx].flags |= BasicBlockFlags::WILL_DELETE;
                nodes_to_remove_set.insert(nx);
                // self.graph[nx]
                //     .instrs
                //     .push(crate::smallvm::ParsedInstr::Good(Rc::new(Instruction {
                //         opcode: TargetOpcode::JUMP_FORWARD,
                //         arg: Some(0),
                //     })));
            }
            if yes {
                // panic!("{:#?}", self.graph[nx]);
            }
        }

        self.write_dot("target");

        let mut needs_new_root = false;
        let root = self.root;
        self.graph.retain_nodes(|g, node| {
            if nodes_to_remove_set.contains(&node) {
                println!("removing node starting at: {}", g[node].start_offset);
                // println!("{:?}", self.graph.node_indices());
                // println!("removing {:#?}", self.graph[node]);
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
            println!("{:#?}", self.graph.node_indices().collect::<Vec<_>>());
            self.root = self.graph.node_indices().next().unwrap();
            // for node in self.graph.node_indices() {
            //     // this is our new root if it has no incoming edges
            //     if self.graph.edges_directed(node, Direction::Incoming).count() == 0 {
            //         root_node_id = node;
            //         break;
            //     }
            // }
        }
        println!("root node is now: {:#?}", self.graph[self.root]);
    }

    pub(crate) fn clear_flags(&mut self, root: NodeIndex, flags: BasicBlockFlags) {
        let mut bfs = Bfs::new(&self.graph, root);
        while let Some(nx) = bfs.next(&self.graph) {
            self.graph[nx].flags.remove(flags);
        }
    }

    /// Updates basic block offsets following the expected code flow order. i.e. non-target conditional jumps will always
    /// be right after the jump instruction and the point at which the two branches "meet" will be sequential.
    pub(crate) fn update_bb_offsets(&mut self, root: NodeIndex) {
        let mut current_offset = 0;
        let mut stop_at_queue = Vec::new();
        let mut node_queue = Vec::new();
        node_queue.push(root);
        println!("beginning bb visitor");
        'node_visitor: while let Some(nx) = node_queue.pop() {
            println!("current: {:#?}", self.graph[nx]);
            if let Some(stop_at) = stop_at_queue.last() {
                if *stop_at == nx {
                    stop_at_queue.pop();
                }
            }

            let target_found = current_offset == 197;
            // if graph[nx].instrs.len() == 1
            //     && current_offset == 197
            //     && graph[nx].instrs[0].unwrap().opcode == TargetOpcode::LOAD_FAST
            //     && graph[nx].instrs[0].unwrap().arg.unwrap() == 5
            // {
            //     panic!("YOOO");
            // }
            let current_node = &mut self.graph[nx];
            let print = current_node.start_offset == 1219;
            if print {
                //panic!("{:#?}, {}", current_node, current_offset);
            }
            if current_node
                .flags
                .intersects(BasicBlockFlags::OFFSETS_UPDATED)
            {
                continue;
            }

            current_node.flags |= BasicBlockFlags::OFFSETS_UPDATED;

            println!("current offset: {}", current_offset);
            let end_offset = current_node
                .instrs
                .iter()
                .fold(0, |accum, instr| accum + instr.unwrap().len());

            let end_offset = end_offset as u64;
            current_node.start_offset = current_offset;
            current_node.end_offset = current_offset
                + (end_offset - current_node.instrs.last().unwrap().unwrap().len() as u64);

            current_offset += end_offset;

            println!("next offset: {}", current_offset);

            let mut targets = self
                .graph
                .edges_directed(nx, Direction::Outgoing)
                .map(|edge| (edge.target(), *edge.weight()))
                .collect::<Vec<_>>();

            // Sort the targets so that the non-branch path is last
            targets.sort_by(|(_a, aweight), (_b, bweight)| bweight.cmp(aweight));

            // Add the non-constexpr path to the "stop_at_queue" so that we don't accidentally
            // go down that path before handling it ourself
            let jump_path =
                targets
                    .iter()
                    .find_map(|(target, weight)| if *weight == 1 { Some(*target) } else { None });
            //println!("jump path: {:#?}");

            for (target, _weight) in targets {
                println!("target loop");
                // If this is the next node in the nodes to ignore, don't add it
                if let Some(pending) = stop_at_queue.last() {
                    println!("Pending: {:#?}", self.graph[*pending]);
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
                                .intersects(BasicBlockFlags::OFFSETS_UPDATED)
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
                        // if graph[nx].instrs[0].unwrap().opcode == TargetOpcode::LOAD_NAME
                        //     && graph[nx].instrs[0].unwrap().arg.unwrap() == 9
                        //     && graph[nx].instrs.last().unwrap().unwrap().opcode
                        //         == TargetOpcode::JUMP_FORWARD
                        //     && graph[nx].instrs.last().unwrap().unwrap().arg.unwrap() == 1222
                        // {
                        //     panic!("YOOO : {:#?}", graph[target]);
                        // }
                        continue;
                    }
                }
                // if graph[nx].instrs[0].unwrap().opcode == TargetOpcode::LOAD_NAME
                //     && graph[nx].instrs[0].unwrap().arg.unwrap() == 9
                //     && graph[nx].instrs.last().unwrap().unwrap().opcode == TargetOpcode::JUMP_FORWARD
                //     && graph[nx].instrs.last().unwrap().unwrap().arg.unwrap() == 0
                // {
                //     panic!("YOOO : {:?} {:?} {:#?}", target, _weight, graph[target]);
                // }
                // if graph[nx].instrs[0].unwrap().opcode == TargetOpcode::LOAD_CONST
                //     && graph[nx].instrs[0].unwrap().arg.unwrap() == 1
                //     && graph[nx].instrs.last().unwrap().unwrap().opcode
                //         == TargetOpcode::POP_JUMP_IF_TRUE
                //     && graph[nx].instrs.last().unwrap().unwrap().arg.unwrap() == 231
                // {
                //     println!("{:#?}", node_queue);
                //     panic!("hmmm : {:#?}", graph[target]);
                // }

                if self.graph[target]
                    .flags
                    .contains(BasicBlockFlags::OFFSETS_UPDATED)
                {
                    continue;
                }

                node_queue.push(target);
            }

            if let Some(jump_path) = jump_path {
                if !self.graph[jump_path]
                    .flags
                    .contains(BasicBlockFlags::OFFSETS_UPDATED)
                {
                    // the other node may add this one
                    if let Some(pending) = stop_at_queue.last() {
                        if !self.is_downgraph(*pending, jump_path) {
                            stop_at_queue.push(jump_path);
                        }
                    } else {
                        stop_at_queue.push(jump_path);
                    }
                    // use petgraph::algo::astar;
                    // let mut path =
                    //     astar(&*graph, *pending, |finish| finish == target, |e| 0, |_| 0)
                    //         .unwrap()
                    //         .1;
                    // let mut goes_through_updated_node = false;
                    // for node in path {
                    //     if graph[node]
                    //         .flags
                    //         .intersects(BasicBlockFlags::OFFSETS_UPDATED)
                    //     {
                    //         goes_through_updated_node = true;
                    //         break;
                    //     }
                    // }

                    // // If this does not go through an updated node, we can ignore
                    // // the fact that the target is downgraph
                    // if !goes_through_updated_node {
                    //     if graph[nx].instrs[0].unwrap().opcode == TargetOpcode::LOAD_NAME
                    //         && graph[nx].instrs[0].unwrap().arg.unwrap() == 4
                    //         && graph[nx].instrs.last().unwrap().unwrap().opcode
                    //             == TargetOpcode::STORE_NAME
                    //         && graph[nx].instrs.last().unwrap().unwrap().arg.unwrap() == 41
                    //     {
                    //         panic!("YOOO : {:#?}", graph[target]);
                    //     }
                    //     // if graph[nx].instrs[0].unwrap().opcode == TargetOpcode::FOR_ITER
                    //     //     && graph[nx].instrs[0].unwrap().arg.unwrap() == 31
                    //     // {
                    //     //     panic!("YOOO : {:#?}, {}", graph[target], goes_through_updated_node);
                    //     // }
                    //     if found_target
                    //         && graph[nx].instrs[0].unwrap().opcode == TargetOpcode::LOAD_FAST
                    //         && graph[nx].instrs[0].unwrap().arg.unwrap() == 5
                    //     {
                    //         panic!("YOOO : {:#?}, {}", graph[target], goes_through_updated_node);
                    //     }
                    //     continue;
                    // }
                    // }
                    // if graph[jump_path].instrs[0].unwrap().opcode == TargetOpcode::RETURN_VALUE
                    //     && graph[jump_path].start_offset == 105
                    //     && graph[root].instrs[0].unwrap().opcode == TargetOpcode::BUILD_LIST
                    // {
                    //     panic!("added by: {:#?}", graph[nx]);
                    // }
                }
            }
        }

        // let mut edges = graph
        //     .edges_directed(root, Direction::Outgoing)
        //     .collect::<Vec<_>>();

        // // Sort these edges so that we serialize the non-jump path comes first
        // edges.sort_by(|a, b| a.weight().cmp(b.weight()));

        // // this is the right-hand side of the branch
        // let child_stop_at = edges
        //     .iter()
        //     .find(|edge| {
        //         *edge.weight() > 0 && edge.target() != root && !is_downgraph(graph, root, edge.target())
        //     })
        //     .map(|edge| edge.target());

        // let targets = edges
        //     .iter()
        //     .filter_map(|edge| {
        //         if edge.target() != root {
        //             Some((edge.weight().clone(), edge.target()))
        //         } else {
        //             None
        //         }
        //     })
        //     .collect::<Vec<_>>();

        // let target_count = targets.len();

        // if let Some(last) = graph[root].instrs.last().map(|ins| ins.unwrap()) {
        //     if last.opcode == TargetOpcode::POP_JUMP_IF_FALSE && last.arg.unwrap() == 829 {
        //         println!("{:#?}", stop_at);
        //         println!("{:#?}", child_stop_at);
        //         for target in &targets {
        //             println!("target: {:#?}", graph[target.1]);
        //         }
        //         //panic!("{:#?}", graph[root]);
        //     }
        // }
        // for (weight, target) in targets {
        //     // Don't go down this path if it where we're supposed to stop, or this node is downgraph
        //     // from the node we're supposed to stop at
        //     if let Some(stop_at) = stop_at {
        //         if stop_at == target {
        //             continue;
        //         }

        //         if is_downgraph(&*graph, stop_at, target) {
        //             continue;
        //         }
        //     }

        //     if weight == 0 {
        //         update_bb_offsets(target, graph, current_offset, child_stop_at);
        //     } else {
        //         update_bb_offsets(target, graph, current_offset, None);
        //     }
        // }
    }

    /// Update branching instructions to reflect the correct offset for their target, which may have changed since the
    /// graph was created.
    pub(crate) fn update_branches(&mut self, root: NodeIndex) -> bool {
        let current_node = &mut self.graph[root];
        if current_node
            .flags
            .intersects(BasicBlockFlags::BRANCHES_UPDATED)
        {
            return false;
        }

        let mut removed_condition = false;

        current_node.flags |= BasicBlockFlags::BRANCHES_UPDATED;
        // Update any paths to this node -- we need to update their jump instructions
        // if they exist
        let incoming_edges = self
            .graph
            .edges_directed(root, Direction::Incoming)
            .map(|edge| (*edge.weight(), edge.source()))
            .collect::<Vec<_>>();

        for (weight, incoming_edge) in incoming_edges {
            let outgoing_edges_from_parent = self
                .graph
                .edges_directed(incoming_edge, Direction::Outgoing)
                .count();

            if weight != 1 && outgoing_edges_from_parent > 1 {
                continue;
            }

            let source_node = &mut self.graph[incoming_edge];
            let mut last_ins = source_node.instrs.last_mut().unwrap().unwrap();
            if last_ins.opcode == TargetOpcode::JUMP_FORWARD {
                //unsafe { Rc::get_mut_unchecked(&mut last_ins) }.opcode = TargetOpcode::JUMP_ABSOLUTE;
                println!("yo: {:?}", last_ins);
            }

            if !last_ins.opcode.is_jump() {
                continue;
            }

            assert!(last_ins.opcode.has_arg());

            let last_ins_len = last_ins.len();

            let target_node = &self.graph[root];
            let target_node_start = target_node.start_offset;

            let source_node = &mut self.graph[incoming_edge];
            let end_of_jump_ins = source_node.end_offset + last_ins_len as u64;
            let mut can_remove_condition = false;

            if last_ins.opcode == TargetOpcode::JUMP_ABSOLUTE
                && target_node_start > source_node.start_offset
            {
                unsafe { Rc::get_mut_unchecked(&mut last_ins) }.opcode = TargetOpcode::JUMP_FORWARD;
            }

            if last_ins.opcode == TargetOpcode::JUMP_FORWARD && target_node_start < end_of_jump_ins
            {
                unsafe { Rc::get_mut_unchecked(&mut last_ins) }.opcode =
                    TargetOpcode::JUMP_ABSOLUTE;
            }

            let last_ins_is_abs_jump = last_ins.opcode.is_absolute_jump();

            let new_arg = if last_ins_is_abs_jump {
                if target_node_start == end_of_jump_ins {
                    can_remove_condition = true;
                }
                target_node_start
            } else {
                if target_node_start < source_node.end_offset {
                    let target_node = &self.graph[root];
                    let source_node = &self.graph[incoming_edge];
                    panic!(
                        "target start < source end offset\nsource: {:#?},\ntarget {:#?}",
                        source_node, target_node
                    );
                }
                let delta = target_node_start - end_of_jump_ins;
                if delta == 0 {
                    can_remove_condition = true;
                }

                delta
            };

            // if can_remove_condition {
            //     source_node.instrs.pop();
            //     removed_condition = true;
            //     continue;
            // }

            if last_ins.opcode == TargetOpcode::JUMP_ABSOLUTE {
                dbg!(target_node_start);
                dbg!(source_node.end_offset);
                println!("{:?}", new_arg);
            }

            let mut last_ins = source_node.instrs.last_mut().unwrap().unwrap();
            unsafe { Rc::get_mut_unchecked(&mut last_ins) }.arg = Some(new_arg as u16);
        }

        for outgoing_edge in self
            .graph
            .edges_directed(root, Direction::Outgoing)
            .map(|edge| edge.target())
            .collect::<Vec<_>>()
        {
            removed_condition |= self.update_branches(outgoing_edge);
        }

        removed_condition
    }

    /// Write out the object bytecode.
    pub(crate) fn write_bytecode(&mut self, root: NodeIndex, new_bytecode: &mut Vec<u8>) {
        let mut stop_at_queue = Vec::new();
        let mut node_queue = Vec::new();
        node_queue.push(root);
        println!("beginning bb visitor");
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
            let jump_path =
                targets
                    .iter()
                    .find_map(|(target, weight)| if *weight == 1 { Some(*target) } else { None });

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
                        if *self.graph.edge_weight(edge).unwrap() == 0 {
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
        println!("beginning insert jump 0 visitor");
        'node_visitor: while let Some(nx) = node_queue.pop() {
            if let Some(stop_at) = stop_at_queue.last() {
                if *stop_at == nx {
                    stop_at_queue.pop();
                    // ensure that this does not end in a jump
                    // let current_node = &mut graph[nx];
                    // if let Some(last) = current_node.instrs.last().map(|i| i.unwrap()) {
                    //     if !last.opcode.is_jump() {
                    //         // insert a jump 0
                    //         current_node
                    //             .instrs
                    //             .push(crate::smallvm::ParsedInstr::Good(Rc::new(Instruction {
                    //                 opcode: TargetOpcode::JUMP_FORWARD,
                    //                 arg: Some(0),
                    //             })));
                    //     }
                    // }
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
            let jump_path =
                targets
                    .iter()
                    .find_map(|(target, weight)| if *weight == 1 { Some(*target) } else { None });

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
    pub(crate) fn join_blocks(&mut self, root: NodeIndex) -> bool {
        let mut bfs = Bfs::new(&self.graph, root);
        while let Some(nx) = bfs.next(&self.graph) {
            let current_node = &self.graph[nx];
            let incoming_edges = self.graph.edges_directed(nx, Direction::Incoming);

            let num_incoming = incoming_edges.count();
            let outgoing_edges: Vec<(u64, u64)> = self
                .graph
                .edges_directed(nx, Direction::Outgoing)
                .map(|edge| (self.graph[edge.target()].start_offset, *edge.weight()))
                .collect();

            // Ensure only 1 node points to this location
            if num_incoming != 1 {
                continue;
            }
            // Grab the incoming edge and see how many incoming edges it has. We might be able
            // to combine these nodes
            let incoming_edge = self
                .graph
                .edges_directed(nx, Direction::Incoming)
                .next()
                .unwrap();

            let source_node_index = incoming_edge.source();

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

            let mut current_instrs = current_node.instrs.clone();
            let mut current_end_offset = current_node.end_offset;
            let parent_node = &mut self.graph[source_node_index];
            let parent_node_start_offset = parent_node.start_offset;

            if let Some(last_instr) = parent_node.instrs.last().map(|i| i.unwrap()) {
                if last_instr.opcode.is_jump() {
                    // Remove the last instruction -- this is our jump
                    let removed_instruction = parent_node.instrs.pop().unwrap();

                    println!("{:?}", removed_instruction);
                    assert!(!removed_instruction.unwrap().opcode.is_conditional_jump());
                    current_end_offset -= removed_instruction.unwrap().len() as u64;
                }
            }

            // Adjust the merged node's offsets
            parent_node.end_offset = current_end_offset;

            // Move this node's instructions into the parent
            parent_node.instrs.append(&mut current_instrs);

            self.graph.remove_node(nx);

            // This is no longer valid. Force compiler error if it's used
            let _source_node_index = ();

            let merged_node_index = self
                .graph
                .node_indices()
                .find(|i| self.graph[*i].start_offset == parent_node_start_offset)
                .unwrap();

            // Re-add the old node's outgoing edges
            for (target_offset, weight) in outgoing_edges {
                let target_index = self
                    .graph
                    .node_indices()
                    .find(|i| self.graph[*i].start_offset == target_offset)
                    .unwrap();

                // Grab this node's index
                self.graph.add_edge(merged_node_index, target_index, weight);
            }

            return true;
        }

        false
    }

    pub fn is_downgraph(&self, source: NodeIndex, dest: NodeIndex) -> bool {
        let node_map = dijkstra(&self.graph, source, Some(dest), |_| 1);
        node_map.get(&dest).is_some()
    }
}
