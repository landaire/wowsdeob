use anyhow::Result;
use bitflags::bitflags;
use log::{debug, trace};
use petgraph::graph::{Graph, NodeIndex};
use petgraph::visit::{Bfs, EdgeRef};
use petgraph::Direction;
use py_marshal::{Code, Obj};
use pydis::prelude::*;
use std::collections::{BTreeMap, VecDeque};
use std::io::Cursor;
use std::sync::Arc;

type TargetOpcode = pydis::opcode::Python27;
use crate::smallvm::ParsedInstr;
use std::rc::Rc;

bitflags! {
    #[derive(Default)]
    pub struct BasicBlockFlags: u32 {
        const OFFSETS_UPDATED = 0b00000001;
        const BRANCHES_UPDATED = 0b00000010;
        const BYTECODE_WRITTEN= 0b00000100;
        const CONSTEXPR_CONDITION= 0b00001000;
        const WILL_DELETE= 0b00010000;
        const CONSTEXPR_CHECKED= 0b00100000;
    }
}

#[derive(Debug, Default)]
pub struct BasicBlock {
    start_offset: u64,
    end_offset: u64,
    instrs: Vec<ParsedInstr>,
    has_bad_instrs: bool,
    flags: BasicBlockFlags,
}

use std::fmt;
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
    fn split(&mut self, offset: u64) -> (u64, BasicBlock) {
        // It does indeed land in the middle of this block. Let's figure out which
        // instruction it lands on
        let mut ins_offset = self.start_offset;
        let mut ins_index = None;
        for (i, ins) in self.instrs.iter().enumerate() {
            if offset == ins_offset {
                ins_index = Some(i);
                break;
            }

            ins_offset += ins.unwrap().len() as u64;
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

pub fn deobfuscate_bytecode(code: Arc<Code>) -> Result<Vec<u8>> {
    let debug = !true;

    let bytecode = code.code.as_slice();
    let consts = Arc::clone(&code.consts);
    let mut new_bytecode: Vec<u8> = vec![];

    let (mut root_node_id, mut code_graph) = bytecode_to_graph(Arc::clone(&code))?;

    // Start joining blocks
    use petgraph::dot::{Config, Dot};
    let mut counter = 0;
    for i in 0..200 {
        if !std::path::PathBuf::from(format!("before_{}.dot", i)).exists() {
            counter = i;
            break;
        }
    }

    std::fs::write(
        format!("before_{}.dot", counter),
        format!("{}", Dot::with_config(&code_graph, &[Config::EdgeNoLabel])),
    );

    remove_bad_branches(root_node_id, &mut code_graph, &code);

    // if first.opcode == TargetOpcode::JUMP_ABSOLUTE && first.arg.unwrap() == 44 {
    //     panic!("");
    // }
    while join_blocks(root_node_id, &mut code_graph) {}

    let mut had_removed_nodes = 0;

    std::fs::write(
        format!("joined_{}.dot", counter),
        format!("{}", Dot::with_config(&code_graph, &[Config::EdgeNoLabel])),
    );

    let mut execution_path = ExecutionPath::default();

    let (insns_to_remove, mut nodes_to_remove, completed_paths) = dead_code_analysis(
        root_node_id,
        &mut code_graph,
        &mut execution_path,
        Arc::clone(&code),
    );
    if counter == 5 {
        //panic!("{:#?}", completed_paths.first().unwrap().condition_results);
    }
    std::fs::write(
        format!("after_dead_{}.dot", counter),
        format!("{}", Dot::with_config(&code_graph, &[Config::EdgeNoLabel])),
    );

    if !insns_to_remove.is_empty() {
        use std::iter::FromIterator;
        println!("{:?}\n{:?}", insns_to_remove, nodes_to_remove);

        let mut nodes_to_remove_set = std::collections::BTreeSet::<NodeIndex>::new();
        nodes_to_remove_set.extend(nodes_to_remove.into_iter());

        let mut stop_at_queue = Vec::new();
        let mut node_queue = Vec::new();
        node_queue.push(root_node_id);
        println!("beginning visitor");
        'node_visitor: while let Some(nx) = node_queue.pop() {
            code_graph[nx].flags |= BasicBlockFlags::CONSTEXPR_CHECKED;
            if let Some(stop_at) = stop_at_queue.last() {
                if *stop_at == nx {
                    stop_at_queue.pop();
                }
            }

            println!("Visiting: {:#?}", code_graph[nx]);

            let mut targets = code_graph
                .edges_directed(nx, Direction::Outgoing)
                .map(|edge| (edge.target(), *edge.weight()))
                .collect::<Vec<_>>();

            // Sort the targets so that the constexpr path is first
            targets.sort_by(|(a, _aweight), (b, _bweight)| {
                (code_graph[*b].flags & BasicBlockFlags::CONSTEXPR_CONDITION)
                    .cmp(&(code_graph[*a].flags & BasicBlockFlags::CONSTEXPR_CONDITION))
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
                        continue;
                    }
                }

                if code_graph[target]
                    .flags
                    .contains(BasicBlockFlags::CONSTEXPR_CHECKED)
                {
                    continue;
                }

                node_queue.push(target);
            }

            if let Some(jump_path) = jump_path {
                stop_at_queue.push(jump_path);
            }

            let mut insns_to_remove_set = std::collections::BTreeSet::<usize>::new();
            if let Some(instructions) = insns_to_remove.get(&nx) {
                insns_to_remove_set.extend(&mut instructions.borrow_mut().iter());
            }

            // Check if any of the nodes connecting to this could not be
            // solved
            let mut only_modify_self = false;
            let mut path_value = None;
            for source in code_graph
                .edges_directed(nx, Direction::Incoming)
                .map(|edge| edge.source())
                .collect::<Vec<_>>()
            {
                // if nx == NodeIndex::new(14) && counter == 1 {
                //     println!("we're in 14: {:#?}", code_graph[source]);
                // }
                let source_flags = code_graph[source].flags;
                if !source_flags
                    .intersects(BasicBlockFlags::CONSTEXPR_CONDITION | BasicBlockFlags::WILL_DELETE)
                {
                    // println!("{:#?}", source);
                    // println!("{:#?}", nx);
                    // println!("{:#?}", code_graph[source]);
                    // println!("{:#?}", code_graph[nx]);
                    if counter == 1 {
                        println!("ye");
                    }
                    // Ok, we have a connecting node that could not be solved. We don't touch this node.
                    let toggled_flags =
                        code_graph[nx].flags & !BasicBlockFlags::CONSTEXPR_CONDITION;

                    code_graph[nx].flags = toggled_flags;

                    // Remove this node from nodes to remove, if it exists
                    println!(
                        "removing {} from node removal list list",
                        code_graph[nx].start_offset
                    );
                    nodes_to_remove_set.remove(&nx);

                    // println!("New flags: {:#?}", code_graph[nx].flags);

                    // we may continue *only if* all paths agree on this node
                    // in this node
                    for path in &completed_paths {
                        match path.condition_results.get(&nx) {
                            Some(value) => match path_value {
                                Some(previous_value) => {
                                    if previous_value != value.0 {
                                        path_value = None;
                                        break;
                                    }
                                }
                                None => {
                                    path_value = Some(value.0);
                                }
                            },
                            None => {
                                break;
                            }
                        }
                    }

                    if path_value.is_none() {
                        // Ok, we have a connecting node that could not be solved. We don't touch this node.
                        let toggled_flags =
                            code_graph[nx].flags & !BasicBlockFlags::CONSTEXPR_CONDITION;

                        code_graph[nx].flags = toggled_flags;

                        // Remove this node from nodes to remove, if it exists
                        nodes_to_remove_set.remove(&nx);
                        continue 'node_visitor;
                    } else {
                        println!(
                            "{} node can bypass: {:#?}. condition: {:?}. deleting: {:?}",
                            counter, code_graph[nx].start_offset, path_value, insns_to_remove_set
                        );
                        only_modify_self = true;
                    }
                    //if !nodes_with_isolated_constexprs.contains(&nx) {
                    //}
                }
            }

            if !only_modify_self {
                path_value = completed_paths[0].condition_results.get(&nx).map(|x| x.0);
            }

            if nodes_to_remove_set.contains(&nx) {
                println!("deleting entire node...");
                code_graph[nx].flags |= BasicBlockFlags::WILL_DELETE;
                continue;
            }

            // if !insns_to_remove.contains_key(&nx) {
            //     continue;
            // }
            println!("removing instructions");

            for ins_idx in insns_to_remove_set.iter().rev().cloned() {
                // if *code.filename == "26949592413111478" && *code.name == "50844295913873" {
                //     panic!("1");
                // }

                let current_node = &code_graph[nx];
                // If we're removing a jump, remove the related edge
                if current_node.instrs[ins_idx]
                    .unwrap()
                    .opcode
                    .is_conditional_jump()
                {
                    println!("PATH VALUE: {:?}", path_value);
                    if let Some(path_value) = path_value {
                        if let Some((target_edge, target)) = code_graph
                            .edges_directed(nx, Direction::Outgoing)
                            .find_map(|edge| {
                                println!("EDGE VALUE: {}", edge.weight());
                                if *edge.weight() != path_value {
                                    Some((edge.id(), edge.target()))
                                } else {
                                    None
                                }
                            })
                        {
                            println!(
                                "REMOVING EDGE FROM {} TO {}",
                                code_graph[nx].start_offset, code_graph[target].start_offset
                            );
                            code_graph.remove_edge(target_edge);
                        }
                    }
                }

                let current_node = &mut code_graph[nx];
                current_node.instrs.remove(ins_idx);
            }

            // Remove this node if it has no more instructions
            let current_node = &code_graph[nx];
            if current_node.instrs.is_empty() {
                // if *code.filename == "26949592413111478" && *code.name == "50844295913873" {
                //     panic!("1");
                // }
                //code_graph[nx].flags |= BasicBlockFlags::WILL_DELETE;
                //nodes_to_remove_set.insert(nx);
                code_graph[nx]
                    .instrs
                    .push(crate::smallvm::ParsedInstr::Good(Rc::new(Instruction {
                        opcode: TargetOpcode::JUMP_FORWARD,
                        arg: Some(0),
                    })));
            }
        }

        if counter == 5 {
            std::fs::write(
                format!("target.dot"),
                format!("{}", Dot::with_config(&code_graph, &[Config::EdgeNoLabel])),
            );
            // panic!("");
        }

        let mut needs_new_root = false;
        for node in nodes_to_remove_set.iter().rev().cloned() {
            println!(
                "removing node starting at: {}",
                code_graph[node].start_offset
            );
            // println!("{:?}", code_graph.node_indices());
            // println!("removing {:#?}", code_graph[node]);
            if node == root_node_id {
                // find the new root
                needs_new_root = true;
            }

            // let mut targets = code_graph
            //     .edges_directed(node, Direction::Outgoing)
            //     .map(|e| e.target())
            //     .collect::<Vec<_>>();
            // // There must be only one outgoing connection. That new node should consume
            // // any incoming connections here
            // let incoming_nodes = code_graph
            //     .edges_directed(node, Direction::Incoming)
            //     .map(|e| (*e.weight(), e.target()))
            //     .collect::<Vec<_>>();
            // println!(
            //     "outgoing: {}, incoming: {}",
            //     targets.len(),
            //     incoming_nodes.len()
            // );
            // assert!(targets.len() <= 1);
            // let target = targets.pop().unwrap();
            // for (weight, incoming) in incoming_nodes {
            //     code_graph.add_edge(incoming, target, weight);
            // }

            // if *code.filename == "26949592413111478" && *code.name == "50844295913873" {
            //     panic!("1");
            // }
            code_graph.remove_node(node);

            //println!("{:?}", code_graph.node_indices());
        }

        if needs_new_root {
            for node in code_graph.node_indices() {
                // this is our new root if it has no incoming edges
                if code_graph.edges_directed(node, Direction::Incoming).count() == 0 {
                    root_node_id = node;
                    break;
                }
            }
        }
        println!("root node is now: {:#?}", code_graph[root_node_id]);

        println!("yo?");

        std::fs::write(
            format!("target.dot"),
            format!("{}", Dot::with_config(&code_graph, &[Config::EdgeNoLabel])),
        );

        if counter == 5 {
            //panic!("");
        }
        if had_removed_nodes > 4 {
            //panic!("");
        }
        had_removed_nodes += 1;
    }

    //  if had_removed_nodes > 0 {
    std::fs::write(
        format!("target.dot"),
        format!("{}", Dot::with_config(&code_graph, &[Config::EdgeNoLabel])),
    );
    //panic!("");
    // }
    while join_blocks(root_node_id, &mut code_graph) {}
    std::fs::write(
        format!("joined.dot"),
        format!("{}", Dot::with_config(&code_graph, &[Config::EdgeNoLabel])),
    );
    if counter == 2 {
        //panic!("")
    }

    // update BB offsets
    update_bb_offsets(root_node_id, &mut code_graph);
    std::fs::write(
        format!("updated_bb.dot"),
        format!("{}", Dot::with_config(&code_graph, &[Config::EdgeNoLabel])),
    );
    if update_branches(root_node_id, &mut code_graph) {
        clear_flags(
            root_node_id,
            &mut code_graph,
            BasicBlockFlags::OFFSETS_UPDATED,
        );
        update_bb_offsets(root_node_id, &mut code_graph);
    }
    clear_flags(
        root_node_id,
        &mut code_graph,
        BasicBlockFlags::OFFSETS_UPDATED,
    );
    update_bb_offsets(root_node_id, &mut code_graph);

    std::fs::write(
        format!("offsets_{}.dot", counter),
        format!("{}", Dot::with_config(&code_graph, &[Config::EdgeNoLabel])),
    );

    // if code.filename.as_ref() == "26949592413111478" && code.name.as_ref() == "124013281542" {
    //     panic!("");
    // }

    write_bytecode(root_node_id, &mut code_graph, &mut new_bytecode);

    if debug {
        let mut cursor = std::io::Cursor::new(&new_bytecode);
        trace!("{}", cursor.position());
        while let Ok(instr) = decode_py27(&mut cursor) {
            trace!("{:?}", instr);
            trace!("");
            trace!("{}", cursor.position());
        }
    }

    Ok(new_bytecode)
}

fn clear_flags(root: NodeIndex, graph: &mut Graph<BasicBlock, u64>, flags: BasicBlockFlags) {
    let mut bfs = Bfs::new(&*graph, root);
    while let Some(nx) = bfs.next(&*graph) {
        graph[nx].flags.remove(flags);
    }
}

pub fn bytecode_to_graph(code: Arc<Code>) -> Result<(NodeIndex, Graph<BasicBlock, u64>)> {
    let debug = false;

    let analyzed_instructions = crate::smallvm::const_jmp_instruction_walker(
        code.code.as_slice(),
        Arc::clone(&code.consts),
        |_instr, _offset| {
            // We don't care about instructions that are executed
            crate::smallvm::WalkerState::Continue
        },
    )?;

    if true || debug {
        trace!("analyzed\n{:#?}", analyzed_instructions);
    }

    let mut curr_basic_block = BasicBlock::default();
    let mut code_graph = petgraph::Graph::<BasicBlock, u64>::new();
    let mut edges = vec![];
    let mut root_node_id = None;
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

        curr_basic_block.instrs.push(instr.clone());

        // If this is a bad opcode let's abort this BB immediately
        let instr = match instr {
            ParsedInstr::Good(instr) => instr,
            ParsedInstr::Bad => {
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
                let weight = *weight;
                if *to > curr_basic_block.start_offset && *to <= curr_basic_block.end_offset {
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
                let weight = *weight;
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

                edges.push((
                    curr_basic_block.end_offset,
                    target,
                    !matches!(
                        instr.opcode,
                        TargetOpcode::JUMP_FORWARD | TargetOpcode::JUMP_ABSOLUTE,
                    ),
                ));

                // Check if this block is self-referencing
                if target > curr_basic_block.start_offset && target <= curr_basic_block.end_offset {
                    split_at = Some(target);
                } else {
                    // Check if this jump lands us in the middle of a block that's already
                    // been parsed
                    if let Some(root) = root_node_id.as_ref() {
                        for nx in code_graph.node_indices() {
                            let target_node = &mut code_graph[nx];
                            dbg!(target);
                            dbg!(target_node.start_offset);
                            dbg!(target_node.end_offset);
                            if target > target_node.start_offset && target <= target_node.end_offset
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

    if found_it {
        //panic!("{:#?}", code_graph);
    }

    use petgraph::IntoWeightedEdge;
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
                    (new_edge.0.unwrap(), new_edge.1.unwrap(), *weight as u64).into_weighted_edge(),
                )
            } else {
                None
            }
        })
        .collect::<Vec<_>>();

    code_graph.extend_with_edges(edges.as_slice());

    Ok((root_node_id.unwrap(), code_graph))
}

fn update_bb_offsets(root: NodeIndex, graph: &mut Graph<BasicBlock, u64>) {
    let mut current_offset = 0;
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

        let target_found = current_offset == 197;
        // if graph[nx].instrs.len() == 1
        //     && current_offset == 197
        //     && graph[nx].instrs[0].unwrap().opcode == TargetOpcode::LOAD_FAST
        //     && graph[nx].instrs[0].unwrap().arg.unwrap() == 5
        // {
        //     panic!("YOOO");
        // }
        let current_node = &mut graph[nx];
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

        let mut targets = graph
            .edges_directed(nx, Direction::Outgoing)
            .map(|edge| (edge.target(), *edge.weight()))
            .collect::<Vec<_>>();

        // Sort the targets so that the non-branch path is last
        targets.sort_by(|(a, aweight), (b, bweight)| bweight.cmp(aweight));

        // Add the non-constexpr path to the "stop_at_queue" so that we don't accidentally
        // go down that path before handling it ourself
        let jump_path = targets
            .iter()
            .find_map(|(target, weight)| if *weight == 1 { Some(*target) } else { None });
        //println!("jump path: {:#?}");
        let found_target = graph[nx].instrs.len() == 1
            && graph[nx].instrs[0].unwrap().opcode == TargetOpcode::FOR_ITER
            && graph[nx].instrs[0].unwrap().arg.unwrap() == 31;
        if graph[nx].instrs.len() == 1
            && target_found
            && graph[nx].instrs[0].unwrap().opcode == TargetOpcode::LOAD_FAST
            && graph[nx].instrs[0].unwrap().arg.unwrap() == 5
        {
            //panic!("YOOO : {:#?} {:#?}", graph[targets[0].0], stop_at_queue);
        }

        for (target, _weight) in targets {
            println!("target loop");
            // If this is the next node in the nodes to ignore, don't add it
            if let Some(pending) = stop_at_queue.last() {
                println!("Pending: {:#?}", graph[*pending]);
                // we need to find this path to see if it goes through a node that has already
                // had its offsets touched
                if is_downgraph(graph, *pending, target) {
                    use petgraph::algo::astar;
                    let mut path =
                        astar(&*graph, *pending, |finish| finish == target, |e| 0, |_| 0)
                            .unwrap()
                            .1;
                    let mut goes_through_updated_node = false;
                    for node in path {
                        if graph[node]
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
                        if graph[nx].instrs[0].unwrap().opcode == TargetOpcode::LOAD_NAME
                            && graph[nx].instrs[0].unwrap().arg.unwrap() == 4
                            && graph[nx].instrs.last().unwrap().unwrap().opcode
                                == TargetOpcode::STORE_NAME
                            && graph[nx].instrs.last().unwrap().unwrap().arg.unwrap() == 41
                        {
                            //panic!("YOOO : {:#?}", graph[target]);
                        }
                        // if graph[nx].instrs[0].unwrap().opcode == TargetOpcode::FOR_ITER
                        //     && graph[nx].instrs[0].unwrap().arg.unwrap() == 31
                        // {
                        //     panic!("YOOO : {:#?}, {}", graph[target], goes_through_updated_node);
                        // }
                        if found_target
                            && graph[nx].instrs[0].unwrap().opcode == TargetOpcode::LOAD_FAST
                            && graph[nx].instrs[0].unwrap().arg.unwrap() == 5
                        {
                            //panic!("YOOO : {:#?}, {}", graph[target], goes_through_updated_node);
                        }
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
            if graph[nx].instrs.len() == 1
                && found_target
                && graph[nx].instrs[0].unwrap().opcode == TargetOpcode::LOAD_FAST
                && graph[nx].instrs[0].unwrap().arg.unwrap() == 5
            {
                //panic!("YOOO : {:#?}, {:?}", graph[target], node_queue);
            }
            if graph[nx].instrs[0].unwrap().opcode == TargetOpcode::LOAD_NAME
                && graph[nx].instrs[0].unwrap().arg.unwrap() == 9
                && graph[nx].instrs.last().unwrap().unwrap().opcode == TargetOpcode::JUMP_FORWARD
                && graph[nx].instrs.last().unwrap().unwrap().arg.unwrap() == 1222
            {
                //panic!("YOOO : {:#?}", graph[target]);
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

            if graph[target]
                .flags
                .contains(BasicBlockFlags::OFFSETS_UPDATED)
            {
                continue;
            }

            node_queue.push(target);
        }

        if let Some(jump_path) = jump_path {
            if !graph[jump_path]
                .flags
                .contains(BasicBlockFlags::OFFSETS_UPDATED)
            {
                // the other node may add this one
                if let Some(pending) = stop_at_queue.last() {
                    if !is_downgraph(graph, *pending, jump_path) {
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

fn update_branches(root: NodeIndex, graph: &mut Graph<BasicBlock, u64>) -> bool {
    let current_node = &mut graph[root];
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
    let incoming_edges = graph
        .edges_directed(root, Direction::Incoming)
        .map(|edge| (*edge.weight(), edge.source()))
        .collect::<Vec<_>>();

    for (weight, incoming_edge) in incoming_edges {
        let outgoing_edges_from_parent = graph
            .edges_directed(incoming_edge, Direction::Outgoing)
            .count();

        if weight != 1 && outgoing_edges_from_parent > 1 {
            continue;
        }

        let source_node = &mut graph[incoming_edge];
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

        let target_node = &graph[root];
        let target_node_start = target_node.start_offset;

        let source_node = &mut graph[incoming_edge];
        let end_of_jump_ins = (source_node.end_offset + last_ins_len as u64);
        let mut can_remove_condition = false;

        if last_ins.opcode == TargetOpcode::JUMP_ABSOLUTE
            && target_node_start > source_node.start_offset
        {
            unsafe { Rc::get_mut_unchecked(&mut last_ins) }.opcode = TargetOpcode::JUMP_FORWARD;
        }

        if last_ins.opcode == TargetOpcode::JUMP_FORWARD && target_node_start < end_of_jump_ins {
            unsafe { Rc::get_mut_unchecked(&mut last_ins) }.opcode = TargetOpcode::JUMP_ABSOLUTE;
        }

        let last_ins_is_abs_jump = last_ins.opcode.is_absolute_jump();

        let new_arg = if last_ins_is_abs_jump {
            if target_node_start == end_of_jump_ins {
                can_remove_condition = true;
            }
            target_node_start
        } else {
            if target_node_start < source_node.end_offset {
                let target_node = &graph[root];
                let source_node = &graph[incoming_edge];
                panic!("source: {:#?},\ntarget {:#?}", source_node, target_node);
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

    for outgoing_edge in graph
        .edges_directed(root, Direction::Outgoing)
        .map(|edge| edge.target())
        .collect::<Vec<_>>()
    {
        removed_condition |= update_branches(outgoing_edge, graph);
    }

    removed_condition
}

fn write_bytecode(root: NodeIndex, graph: &mut Graph<BasicBlock, u64>, new_bytecode: &mut Vec<u8>) {
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

        let current_node = &mut graph[nx];
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

        let mut targets = graph
            .edges_directed(nx, Direction::Outgoing)
            .map(|edge| (edge.target(), *edge.weight()))
            .collect::<Vec<_>>();

        // Sort the targets so that the non-branch path is last
        targets.sort_by(|(a, aweight), (b, bweight)| bweight.cmp(aweight));

        // Add the non-constexpr path to the "stop_at_queue" so that we don't accidentally
        // go down that path before handling it ourself
        let jump_path = targets
            .iter()
            .find_map(|(target, weight)| if *weight == 1 { Some(*target) } else { None });

        for (target, _weight) in targets {
            // If this is the next node in the nodes to ignore, don't add it
            if let Some(pending) = stop_at_queue.last() {
                // we need to find this path to see if it goes through a node that has already
                // had its offsets touched
                if is_downgraph(graph, *pending, target) {
                    use petgraph::algo::astar;
                    let mut path =
                        astar(&*graph, *pending, |finish| finish == target, |e| 0, |_| 0)
                            .unwrap()
                            .1;
                    let mut goes_through_updated_node = false;
                    for node in path {
                        if graph[node]
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

            if graph[target]
                .flags
                .contains(BasicBlockFlags::BYTECODE_WRITTEN)
            {
                continue;
            }

            node_queue.push(target);
        }

        if let Some(jump_path) = jump_path {
            if !graph[jump_path]
                .flags
                .contains(BasicBlockFlags::BYTECODE_WRITTEN)
            {
                // the other node may add this one
                if let Some(pending) = stop_at_queue.last() {
                    if !is_downgraph(graph, *pending, jump_path) {
                        stop_at_queue.push(jump_path);
                    }
                } else {
                    stop_at_queue.push(jump_path);
                }
            }
        }
    }
}

fn remove_bad_branches(root: NodeIndex, graph: &mut Graph<BasicBlock, u64>, code: &Code) {
    let mut bfs = Bfs::new(&*graph, root);
    while let Some(nx) = bfs.next(&*graph) {
        let current_node = &mut graph[nx];
        // We only operate on nodes with bad instructions
        if !current_node.has_bad_instrs {
            continue;
        }

        // We're going to change the instructions in here to return immediately
        current_node.instrs.clear();

        // We need to walk instructions to this point to get the stack size so we can balance it
        use petgraph::algo::astar;
        let mut path = astar(&*graph, root, |finish| finish == nx, |e| 0, |_| 0)
            .unwrap()
            .1;
        let mut stack_size = 0;
        // Remove all edges along this path
        for (idx, node) in path.iter().cloned().enumerate() {
            if node == nx {
                break;
            }

            for instr in &graph[node].instrs {
                // these ones pop only if we're not taking the branch
                if matches!(
                    instr.unwrap().opcode,
                    TargetOpcode::JUMP_IF_TRUE_OR_POP | TargetOpcode::JUMP_IF_FALSE_OR_POP
                ) {
                    // Grab the edge from this node to the next
                    let edge = graph.find_edge(node, path[idx + 1]).unwrap();
                    if *graph.edge_weight(edge).unwrap() == 0 {
                        stack_size -= 1;
                    } else {
                        // do nothing if we take the branch
                    }
                } else {
                    stack_size += instr.unwrap().stack_adjustment_after();
                }
            }
        }

        let current_node = &mut graph[nx];
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

fn join_blocks(root: NodeIndex, graph: &mut Graph<BasicBlock, u64>) -> bool {
    let mut bfs = Bfs::new(&*graph, root);
    while let Some(nx) = bfs.next(&*graph) {
        let current_node = &graph[nx];
        let incoming_edges = graph.edges_directed(nx, Direction::Incoming);

        let num_incoming = incoming_edges.count();
        let outgoing_edges: Vec<(u64, u64)> = graph
            .edges_directed(nx, Direction::Outgoing)
            .map(|edge| (graph[edge.target()].start_offset, *edge.weight()))
            .collect();

        // Ensure only 1 node points to this location
        if num_incoming != 1 {
            continue;
        }
        // Grab the incoming edge and see how many incoming edges it has. We might be able
        // to combine these nodes
        let incoming_edge = graph
            .edges_directed(nx, Direction::Incoming)
            .next()
            .unwrap();

        let source_node_index = incoming_edge.source();

        let parent_outgoing_edge_count = graph
            .edges_directed(source_node_index, Direction::Outgoing)
            .count();
        if parent_outgoing_edge_count != 1 {
            continue;
        }

        // Make sure that these nodes are not circular
        let are_circular = graph
            .edges_directed(nx, Direction::Outgoing)
            .any(|edge| edge.target() == source_node_index);

        if are_circular {
            continue;
        }

        let mut current_instrs = current_node.instrs.clone();
        let mut current_end_offset = current_node.end_offset;
        let parent_node = &mut graph[source_node_index];
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

        graph.remove_node(nx);

        // This is no longer valid. Force compiler error if it's used
        let source_node_index = ();

        let merged_node_index = graph
            .node_indices()
            .find(|i| graph[*i].start_offset == parent_node_start_offset)
            .unwrap();

        // Re-add the old node's outgoing edges
        for (target_offset, weight) in outgoing_edges {
            let target_index = graph
                .node_indices()
                .find(|i| graph[*i].start_offset == target_offset)
                .unwrap();

            // Grab this node's index
            graph.add_edge(merged_node_index, target_index, weight);
        }

        return true;
    }

    false
}

use std::collections::HashMap;
#[derive(Debug, Default, Clone)]
struct ExecutionPath {
    stack: crate::smallvm::VmStack<AccessTrackingInfo>,
    vars: crate::smallvm::VmVars<AccessTrackingInfo>,
    names: crate::smallvm::VmNames<AccessTrackingInfo>,
    names_loaded: crate::smallvm::LoadedNames,
    condition_results: HashMap<NodeIndex, (u64, Vec<AccessTrackingInfo>)>,
}

use std::cell::RefCell;
pub type AccessTrackingInfo = (petgraph::graph::NodeIndex, usize);
fn dead_code_analysis(
    root: NodeIndex,
    graph: &mut Graph<BasicBlock, u64>,
    execution_path: &mut ExecutionPath,
    code: Arc<Code>,
) -> (
    std::collections::HashMap<NodeIndex, Rc<RefCell<Vec<usize>>>>,
    Vec<NodeIndex>,
    Vec<ExecutionPath>,
) {
    let debug = false;
    let current_node = &graph[root];
    let mut instructions_to_remove =
        std::collections::HashMap::<NodeIndex, Rc<RefCell<Vec<usize>>>>::new();
    let mut nodes_to_remove = Vec::new();
    let mut edges = graph
        .edges_directed(root, Direction::Outgoing)
        .collect::<Vec<_>>();
    let mut nodes_with_isolated_constexprs = std::collections::HashSet::new();

    let mut completed_paths = Vec::new();

    // Sort these edges so that we serialize the non-jump path first
    edges.sort_by(|a, b| a.weight().cmp(b.weight()));
    let targets = edges
        .iter()
        .map(|edge| (edge.weight().clone(), edge.target(), edge.id()))
        .collect::<Vec<_>>();

    'instr_loop: for (ins_idx, instr) in current_node.instrs.iter().enumerate() {
        // We handle jumps
        let instr = instr.unwrap();
        if instr.opcode == TargetOpcode::RETURN_VALUE {
            continue;
        }

        if debug {
            println!(
                "DEAD CODE REMOVAL INSTR: {:?}, KEY: {:?}",
                instr,
                (root, ins_idx)
            );
        }

        if instr.opcode.is_conditional_jump() {
            let mut tos_temp = None;
            let (tos_ref, modifying_instructions) = execution_path.stack.last().unwrap();
            let mut tos = tos_ref;
            if debug {
                println!("TOS: {:?}", tos);
            }
            if instr.opcode == TargetOpcode::POP_JUMP_IF_TRUE && instr.arg.unwrap() == 565 {
                //panic!("node index: {:?}", root);
            }

            // if instr.opcode == TargetOpcode::POP_JUMP_IF_FALSE && instr.arg.unwrap() == 75 {
            //     panic!("{} {}", code.filename, code.name);
            // }
            // we may be able to cheat by looking at the other paths. if one contains
            // bad instructions, we can safely assert we will not take that path
            // TODO: This may be over-aggressive and remove variables that are later used
            if tos.is_none() {
                let mut jump_path_has_bad_instrs = None;
                for (weight, target, id) in &targets {
                    if graph[*target].has_bad_instrs {
                        if *weight == 1 {
                            jump_path_has_bad_instrs = Some(true);
                        } else {
                            jump_path_has_bad_instrs = Some(false);
                        }

                        break;
                    }
                }

                match jump_path_has_bad_instrs {
                    Some(true) => {
                        if matches!(
                            instr.opcode,
                            TargetOpcode::POP_JUMP_IF_TRUE | TargetOpcode::JUMP_IF_TRUE_OR_POP
                        ) {
                            tos_temp = Some(Obj::Bool(false));
                        } else {
                            tos_temp = Some(Obj::Bool(true));
                        }
                        tos = &tos_temp;
                    }
                    Some(false) => {
                        if matches!(
                            instr.opcode,
                            TargetOpcode::POP_JUMP_IF_TRUE | TargetOpcode::JUMP_IF_TRUE_OR_POP
                        ) {
                            tos_temp = Some(Obj::Bool(true));
                        } else {
                            tos_temp = Some(Obj::Bool(false));
                        }
                        tos = &tos_temp;
                    }
                    None => {
                        // can't assume anything :(
                    }
                }
            }
            // we know where this jump should take us
            if let Some(tos) = tos {
                // if *code.filename == "26949592413111478" && *code.name == "50857798689625" {
                //     panic!("{:?}", tos);
                // }
                graph[root].flags |= BasicBlockFlags::CONSTEXPR_CONDITION;

                if debug {
                    println!("{:#?}", modifying_instructions);
                }
                let modifying_instructions = Rc::clone(modifying_instructions);

                if debug {
                    println!("{:#?}", graph[root]);
                    println!("{:?} {:#?}", tos, modifying_instructions);

                    println!("{:?}", instr);
                }
                use num_bigint::ToBigInt;
                macro_rules! extract_truthy_value {
                    ($value:expr) => {
                        match $value {
                            Some(Obj::Bool(result)) => result,
                            Some(Obj::Long(result)) => *result != 0.to_bigint().unwrap(),
                            Some(Obj::Float(result)) => result != 0.0,
                            Some(Obj::Set(result_lock)) => {
                                let result = result_lock.read().unwrap();
                                !result.is_empty()
                            }
                            Some(Obj::List(result_lock)) => {
                                let result = result_lock.read().unwrap();
                                !result.is_empty()
                            }
                            Some(Obj::Tuple(result)) => !result.is_empty(),
                            Some(Obj::String(result)) => !result.is_empty(),
                            other => {
                                panic!("unexpected TOS type for condition: {:?}", other);
                            }
                        }
                    };
                }
                let target_weight = match instr.opcode {
                    TargetOpcode::POP_JUMP_IF_FALSE => {
                        let tos = execution_path.stack.pop().unwrap().0;
                        if !extract_truthy_value!(tos) {
                            1
                        } else {
                            0
                        }
                    }
                    TargetOpcode::POP_JUMP_IF_TRUE => {
                        let tos = execution_path.stack.pop().unwrap().0;
                        if extract_truthy_value!(tos) {
                            1
                        } else {
                            0
                        }
                    }
                    TargetOpcode::JUMP_IF_TRUE_OR_POP => {
                        if extract_truthy_value!(Some(tos.clone())) {
                            1
                        } else {
                            execution_path.stack.pop();
                            0
                        }
                    }
                    TargetOpcode::JUMP_IF_FALSE_OR_POP => {
                        if !extract_truthy_value!(Some(tos.clone())) {
                            1
                        } else {
                            execution_path.stack.pop();
                            0
                        }
                    }
                    other => panic!("did not expect opcode {:?} with static result", other),
                };
                execution_path.condition_results.insert(
                    root,
                    (target_weight, modifying_instructions.borrow().clone()),
                );
                if debug {
                    println!("{:?}", instr);
                    println!("stack after: {:#?}", execution_path.stack);
                }
                let target = targets
                    .iter()
                    .find_map(|(weight, idx, edge)| {
                        if *weight == target_weight {
                            Some(*idx)
                        } else {
                            None
                        }
                    })
                    .unwrap();
                if instr.opcode == TargetOpcode::POP_JUMP_IF_TRUE && instr.arg.unwrap() == 565 {
                    //panic!("node index: {:?}", root);
                }
                // Find branches from this point
                for (_weight, node, _edge) in targets {
                    if node == target {
                        continue;
                    }

                    // only mark this node for removal if it's not downgraph from our target path
                    // AND it does not go through this node
                    use petgraph::algo::astar;
                    let goes_through_this_constexpr =
                        astar(&*graph, target, |finish| finish == node, |e| 0, |_| 0)
                            .map(|(_cost, path)| path.iter().any(|node| *node == root))
                            .unwrap_or_default();
                    if goes_through_this_constexpr || !is_downgraph(graph, target, node) {
                        nodes_to_remove.push(node);
                        continue;
                    }
                    //  else {
                    //     panic!("yo {:?} is downgraph from {:?}", graph[target], graph[node]);
                    // }

                    // let (mut ins, mut nodes) = dead_code_analysis(
                    //     target,
                    //     graph,
                    //     stack,
                    //     vars,
                    //     Arc::clone(&code),
                    //     child_stop_at,
                    // );

                    // instructions_to_remove.append(&mut ins);
                    // nodes_to_remove.append(&mut nodes);
                }
                modifying_instructions.borrow_mut().push((root, ins_idx));
                let mut nodes = std::collections::HashSet::new();
                for (node, instr_idx) in &*modifying_instructions.borrow_mut() {
                    instructions_to_remove
                        .entry(*node)
                        .or_default()
                        .borrow_mut()
                        .push(*instr_idx);
                    nodes.insert(*node);
                }
                if nodes.len() == 1 {
                    nodes_with_isolated_constexprs.extend(nodes.into_iter());
                }
                println!("dead code analysis on: {:?}", graph[target]);
                let (ins, mut rnodes, mut paths) =
                    dead_code_analysis(target, graph, execution_path, Arc::clone(&code));

                instructions_to_remove.extend(ins);
                nodes_to_remove.append(&mut rnodes);
                completed_paths.append(&mut paths);

                return (instructions_to_remove, nodes_to_remove, completed_paths);
            }
        }

        if debug {
            println!("{:?}", instr);
        }
        if !instr.opcode.is_jump() {
            if let Err(e) = crate::smallvm::execute_instruction(
                &*instr,
                Arc::clone(&code),
                &mut execution_path.stack,
                &mut execution_path.vars,
                &mut execution_path.names,
                Rc::clone(&execution_path.names_loaded),
                |function, args, kwargs| {
                    // we dont execute functions here
                    println!("need to implement call_function: {:?}", function);
                    None
                },
                (root, ins_idx),
            ) {
                println!("Encountered error executing instruction: {:?}", e);
                let last_instr = current_node.instrs.last().unwrap().unwrap();
                if last_instr.opcode == TargetOpcode::POP_JUMP_IF_TRUE
                    && last_instr.arg.unwrap() == 417
                {
                    panic!("{:#?}", execution_path.stack);
                }

                completed_paths.push(execution_path.clone());
                return (instructions_to_remove, nodes_to_remove, completed_paths);
            }
        } else {
            // panic!(
            //     "reached the end of block: {:#?} without answers",
            //     current_node
            // );
        }
        if debug {
            println!(
                "out of instructions -- stack after: {:#?}",
                execution_path.stack
            );
        }
    }

    if debug {
        println!("going to other nodes");
    }
    // We reached the last instruction in this node -- go on to the next
    // We don't know which branch to take
    for (weight, target, _edge) in targets {
        if debug {
            println!("target: {}", graph[target].start_offset);
        }
        if let Some(last_instr) = graph[root].instrs.last().map(|instr| instr.unwrap()) {
            // we never follow exception paths
            if last_instr.opcode == TargetOpcode::SETUP_EXCEPT && weight == 1 {
                if debug {
                    println!("skipping -- it's SETUP_EXCEPT");
                }
                continue;
            }

            // we never go in to loops
            if last_instr.opcode == TargetOpcode::FOR_ITER && weight == 0 {
                if debug {
                    println!("skipping -- it's for_iter");
                }
                continue;
            }
        }

        // Make sure that we're not being cyclic
        let is_cyclic = graph
            .edges_directed(target, Direction::Outgoing)
            .any(|edge| edge.target() == root);
        if is_cyclic {
            if debug {
                println!("skipping -- root is downgraph from target");
            }
            continue;
        }

        if debug {
            println!("STACK BEFORE {:?} {:#?}", root, execution_path.stack);
        }
        let (ins, mut rnodes, mut paths) =
            dead_code_analysis(target, graph, execution_path, Arc::clone(&code));
        if debug {
            println!("STACK AFTER {:?} {:#?}", root, execution_path.stack);
        }

        instructions_to_remove.extend(ins);
        nodes_to_remove.append(&mut rnodes);
        completed_paths.append(&mut paths);
    }

    completed_paths.push(execution_path.clone());
    (instructions_to_remove, nodes_to_remove, completed_paths)
}

fn is_downgraph(graph: &Graph<BasicBlock, u64>, source: NodeIndex, dest: NodeIndex) -> bool {
    use petgraph::algo::dijkstra;
    let node_map = dijkstra(&*graph, source, Some(dest), |_| 1);
    node_map.get(&dest).is_some()
}

use cpython::{PyBytes, PyDict, PyList, PyModule, PyObject, PyResult, Python, PythonObject};

pub fn rename_vars(code_data: &[u8], deobfuscated_code: &[Vec<u8>]) -> PyResult<Vec<u8>> {
    let gil = Python::acquire_gil();

    let py = gil.python();

    let marshal = py.import("marshal")?;
    let types = py.import("types")?;

    let module = PyModule::new(py, "deob")?;
    module.add(py, "__builtins__", py.eval("__builtins__", None, None)?)?;

    module.add(py, "marshal", marshal)?;
    module.add(py, "types", types)?;
    module.add(py, "data", PyBytes::new(py, code_data))?;

    let converted_objects: Vec<PyObject> = deobfuscated_code
        .iter()
        .map(|code| PyBytes::new(py, code.as_slice()).into_object())
        .collect();

    module.add(
        py,
        "deobfuscated_code",
        PyList::new(py, converted_objects.as_slice()),
    )?;

    let locals = PyDict::new(py);
    locals.set_item(py, "deob", &module)?;

    let source = r#"
unknowns = 0

def cleanup_code_obj(code):
    global deobfuscated_code
    new_code = deobfuscated_code.pop(0)
    new_consts = []
    for const in code.co_consts:
        if type(const) == types.CodeType:
            new_consts.append(cleanup_code_obj(const))
        else:
            new_consts.append(const)

    return types.CodeType(code.co_argcount, code.co_nlocals, code.co_stacksize, code.co_flags, new_code, tuple(new_consts), fix_varnames(code.co_names), fix_varnames(code.co_varnames), code.co_filename, fix_varnames([code.co_name])[0], code.co_firstlineno, code.co_lnotab, code.co_freevars, code.co_cellvars)


def fix_varnames(varnames):
    global unknowns
    newvars = []
    for var in varnames:
        var = var.strip()
        if len(var) <= 1 or ' ' in var:
            newvars.append('unknown_{0}'.format(unknowns))
            unknowns += 1
        else:
            newvars.append(var)
    
    return tuple(newvars)


code = marshal.loads(data)
output = marshal.dumps(cleanup_code_obj(code))
"#;

    locals.set_item(py, "source", source)?;

    let output = py.run("exec source in deob.__dict__", None, Some(&locals))?;
    debug!("{:?}", output);

    let output = module
        .get(py, "output")?
        .cast_as::<PyBytes>(py)?
        .data(py)
        .to_vec();

    Ok(output)
}
