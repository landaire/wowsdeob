use crate::code_graph::{BasicBlockFlags, CodeGraph, EdgeWeight};
use crate::smallvm::ParsedInstr;
use anyhow::Result;
use bitflags::bitflags;
use cpython::{PyBytes, PyDict, PyList, PyModule, PyObject, PyResult, Python, PythonObject};
use log::{debug, error, trace};
use num_bigint::ToBigInt;
use petgraph::algo::astar;
use petgraph::algo::dijkstra;
use petgraph::graph::{Graph, NodeIndex};
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

/// Represents an execution path taken by the VM
#[derive(Debug, Default, Clone)]
pub struct ExecutionPath {
    /// Stack at the end of this path
    pub stack: crate::smallvm::VmStack<AccessTrackingInfo>,
    /// Vars at the end of this path
    pub vars: crate::smallvm::VmVars<AccessTrackingInfo>,
    /// Names at the end of this path
    pub names: crate::smallvm::VmNames<AccessTrackingInfo>,
    /// Names loaded at the end of this path
    pub names_loaded: crate::smallvm::LoadedNames,
    /// Values for each conditional jump along this execution path
    pub condition_results: HashMap<NodeIndex, Option<(EdgeWeight, Vec<AccessTrackingInfo>)>>,
    /// Nodes that have been executed
    pub executed_nodes: BTreeSet<NodeIndex>,
}

/// Information required to track back an instruction that accessed/tainted a var
pub type AccessTrackingInfo = (petgraph::graph::NodeIndex, usize);

/// Performs partial VM execution. This will execute each instruction and record execution
/// paths down conditional branches. If a branch path cannot be determined, this path "ends" and
/// is forked down both directions.
///
// This function will return all execution paths until they end.
pub(crate) fn perform_partial_execution(
    root: NodeIndex,
    code_graph: &mut CodeGraph,
    execution_path: &mut ExecutionPath,
    mapped_function_names: &mut HashMap<String, String>,
    code: Arc<Code>,
) -> Vec<ExecutionPath> {
    let debug = !false;
    let debug_stack = false;
    let current_node = &code_graph.graph[root];
    let mut edges = code_graph
        .graph
        .edges_directed(root, Direction::Outgoing)
        .collect::<Vec<_>>();

    let mut completed_paths = Vec::new();

    // Sort these edges so that we serialize the non-jump path first
    edges.sort_by(|a, b| a.weight().cmp(b.weight()));
    let targets = edges
        .iter()
        .map(|edge| (edge.weight().clone(), edge.target(), edge.id()))
        .collect::<Vec<_>>();

    execution_path.executed_nodes.insert(root);

    for (ins_idx, instr) in current_node.instrs.iter().enumerate() {
        // We handle jumps
        let instr = instr.unwrap();
        if instr.opcode == TargetOpcode::RETURN_VALUE {
            continue;
        }

        if debug {
            trace!(
                "DEAD CODE REMOVAL INSTR: {:?}, KEY: {:?}",
                instr,
                (root, ins_idx)
            );
        }

        if instr.opcode.is_conditional_jump() {
            let (tos_ref, modifying_instructions) = execution_path.stack.last().unwrap();
            let mut tos = tos_ref.as_ref();
            if debug_stack {
                trace!("TOS: {:?}", tos);
            }

            // Check if this node is downgraph from something that looks like a loop
            let mut last_parent_loop = None;
            let mut bfs = Bfs::new(&code_graph.graph, code_graph.root);
            while let Some(nx) = bfs.next(&code_graph.graph) {
                if let Some(last_instr) = code_graph.graph[nx].instrs.last() {
                    if matches!(
                        last_instr.unwrap().opcode,
                        TargetOpcode::SETUP_LOOP | TargetOpcode::FOR_ITER
                    ) {
                        // Check if we're down the "non-jump" path of this loop
                        let non_jump = code_graph
                            .graph
                            .edges_directed(nx, Direction::Outgoing)
                            .find_map(|edge| {
                                if *edge.weight() == EdgeWeight::NonJump {
                                    Some(edge.target())
                                } else {
                                    None
                                }
                            });

                        if code_graph.is_downgraph(non_jump.unwrap(), root) {
                            last_parent_loop = Some(non_jump.unwrap());
                        }
                    }
                }
            }

            // If we had a parent loop node, let's figure out if our operands
            // change in this loop
            //
            // TODO: Maybe handle nested loops?
            if let Some(parent_loop) = last_parent_loop {
                let fast_operands = modifying_instructions
                    .borrow()
                    .iter()
                    .filter_map(|(nx, ix)| {
                        let instr = code_graph.graph[*nx].instrs[*ix].unwrap();
                        if instr.opcode == TargetOpcode::LOAD_FAST {
                            Some(instr.arg.unwrap())
                        } else {
                            None
                        }
                    })
                    .collect::<BTreeSet<_>>();

                // Now check if these operands are modified in any node within the loop that has *not*
                // yet been executed

                let mut bfs = Bfs::new(&code_graph.graph, parent_loop);
                while let Some(nx) = bfs.next(&code_graph.graph) {
                    for instr in &code_graph.graph[nx].instrs {
                        let instr = instr.unwrap();

                        // Check if this instruction clobbers one of the vars we
                        // use. This happens if it's a STORE_FAST with a matching
                        // index AND the node has not been executed by this execution
                        // path.
                        if instr.opcode == TargetOpcode::STORE_FAST
                            && fast_operands.contains(&instr.arg.unwrap())
                            && !execution_path.executed_nodes.contains(&nx)
                        {
                            // we have a match. this means that this loop modifies
                            // our condition. we shouldn't respect this TOS value
                            tos = None;
                            break;
                        }
                    }
                }
            }

            // we know where this jump should take us
            if let Some(tos) = tos {
                // if *code.filename == "26949592413111478" && *code.name == "50857798689625" {
                //     panic!("{:?}", tos);
                // }
                code_graph.graph[root].flags |= BasicBlockFlags::CONSTEXPR_CONDITION;

                if debug_stack {
                    trace!("{:#?}", modifying_instructions);
                }
                let modifying_instructions = Rc::clone(modifying_instructions);

                if debug {
                    trace!("CONDITION TOS:");
                    trace!("{:#?}", code_graph.graph[root].start_offset);
                    trace!("{:?}", tos);
                    trace!("{:?}", instr);

                    if debug_stack {
                        trace!("{:#?}", modifying_instructions);
                    }
                    trace!("END CONDITION TOS");
                }

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
                            Some(Obj::None) => false,
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
                            EdgeWeight::Jump
                        } else {
                            EdgeWeight::NonJump
                        }
                    }
                    TargetOpcode::POP_JUMP_IF_TRUE => {
                        let tos = execution_path.stack.pop().unwrap().0;
                        if extract_truthy_value!(tos) {
                            EdgeWeight::Jump
                        } else {
                            EdgeWeight::NonJump
                        }
                    }
                    TargetOpcode::JUMP_IF_TRUE_OR_POP => {
                        if extract_truthy_value!(Some(tos.clone())) {
                            EdgeWeight::Jump
                        } else {
                            execution_path.stack.pop();
                            EdgeWeight::NonJump
                        }
                    }
                    TargetOpcode::JUMP_IF_FALSE_OR_POP => {
                        if !extract_truthy_value!(Some(tos.clone())) {
                            EdgeWeight::Jump
                        } else {
                            execution_path.stack.pop();
                            EdgeWeight::NonJump
                        }
                    }
                    other => panic!("did not expect opcode {:?} with static result", other),
                };
                if debug {
                    trace!("{:?}", instr);
                    if debug_stack {
                        trace!("stack after: {:#?}", execution_path.stack);
                    }
                }
                let target = targets
                    .iter()
                    .find_map(|(weight, idx, _edge)| {
                        if *weight == target_weight {
                            Some(*idx)
                        } else {
                            None
                        }
                    })
                    .unwrap();
                // Find branches from this point
                for (_weight, node, _edge) in targets {
                    if node == target {
                        continue;
                    }

                    // only mark this node for removal if it's not downgraph from our target path
                    // AND it does not go through this node
                    let goes_through_this_constexpr = astar(
                        &code_graph.graph,
                        target,
                        |finish| finish == node,
                        |_e| 0,
                        |_| 0,
                    )
                    .map(|(_cost, path)| path.iter().any(|node| *node == root))
                    .unwrap_or_default();
                    if goes_through_this_constexpr || !code_graph.is_downgraph(target, node) {
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
                execution_path.condition_results.insert(
                    root,
                    Some((target_weight, modifying_instructions.borrow().clone())),
                );
                trace!("dead code analysis on: {:?}", code_graph.graph[target]);
                let mut paths = perform_partial_execution(
                    target,
                    code_graph,
                    execution_path,
                    mapped_function_names,
                    Arc::clone(&code),
                );

                completed_paths.append(&mut paths);

                return completed_paths;
            }
        }

        if debug {
            trace!("{:?}", instr);
        }
        if !instr.opcode.is_jump() {
            // if this is a "STORE_NAME" instruction let's see if this data originates
            // at a MAKE_FUNCTION
            if instr.opcode == TargetOpcode::STORE_NAME {
                if let Some((_tos, accessing_instructions)) = execution_path.stack.last() {
                    // this is the data we're storing. where does it originate?
                    let was_make_function =
                        accessing_instructions
                            .borrow()
                            .iter()
                            .rev()
                            .any(|(source_node, idx)| {
                                let source_instruction =
                                    &code_graph.graph[*source_node].instrs[*idx].unwrap();
                                source_instruction.opcode == TargetOpcode::MAKE_FUNCTION
                            });
                    if was_make_function {
                        let (const_origination_node, const_idx) =
                            &accessing_instructions.borrow()[0];

                        let const_instr =
                            &code_graph.graph[*const_origination_node].instrs[*const_idx];
                        let const_instr = const_instr.unwrap();

                        trace!("{:#?}", accessing_instructions.borrow());
                        trace!("{:#?}", instr);
                        for (node, instr) in &*accessing_instructions.borrow() {
                            let const_instr = &code_graph.graph[*node].instrs[*instr];
                            trace!("{:#?}", const_instr);
                        }

                        assert!(const_instr.opcode == TargetOpcode::LOAD_CONST);
                        let const_idx = const_instr.arg.unwrap() as usize;

                        let key = if let Obj::Code(code) = &code.consts[const_idx] {
                            format!("{}_{}", code.filename.to_string(), code.name.to_string())
                        } else {
                            panic!("mapped function is supposed to be a code object");
                        };

                        // TODO: figure out why this Arc::clone is needed and we cannot
                        // just take a reference...
                        let name = Arc::clone(&code.names[instr.arg.unwrap() as usize]);
                        mapped_function_names.insert(key, name.to_string());
                    }
                }
            }

            if instr.opcode == TargetOpcode::RAISE_VARARGS {
                if debug {
                    trace!("skipping -- it's RAISE_VARARGS");
                }
                continue;
            }

            if let Err(e) = crate::smallvm::execute_instruction(
                &*instr,
                Arc::clone(&code),
                &mut execution_path.stack,
                &mut execution_path.vars,
                &mut execution_path.names,
                Rc::clone(&execution_path.names_loaded),
                |function, _args, _kwargs| {
                    // we dont execute functions here
                    debug!("need to implement call_function: {:?}", function);
                    None
                },
                (root, ins_idx),
            ) {
                error!("Encountered error executing instruction: {:?}", e);
                let last_instr = current_node.instrs.last().unwrap().unwrap();

                completed_paths.push(execution_path.clone());
                return completed_paths;
            }
        }

        if debug_stack {
            trace!(
                "out of instructions -- stack after: {:#?}",
                execution_path.stack
            );
        }
    }

    if debug {
        trace!("going to other nodes");
    }

    execution_path.condition_results.insert(root, None);

    // We reached the last instruction in this node -- go on to the next
    // We don't know which branch to take
    for (weight, target, _edge) in targets {
        if debug {
            trace!("target: {}", code_graph.graph[target].start_offset);
        }

        let mut was_loop = false;
        if let Some(last_instr) = code_graph.graph[root]
            .instrs
            .last()
            .map(|instr| instr.unwrap())
        {
            // we never follow exception paths
            if last_instr.opcode == TargetOpcode::SETUP_EXCEPT && weight == EdgeWeight::Jump {
                if debug {
                    trace!("skipping -- it's SETUP_EXCEPT");
                }
                continue;
            }

            // Loops we have to handle special
            if last_instr.opcode == TargetOpcode::FOR_ITER && weight == EdgeWeight::NonJump {
                was_loop = true;
                if debug {
                    trace!("skipping -- it's for_iter");
                }
                // continue;
            }
        }

        // Make sure that we're not being cyclic
        // let is_cyclic = code_graph
        //     .graph
        //     .edges_directed(target, Direction::Outgoing)
        //     .any(|edge| edge.target() == root);
        // if is_cyclic {
        //     if debug {
        //         trace!("skipping -- root is downgraph from target");
        //     }
        //     continue;
        // }

        if debug_stack {
            trace!("STACK BEFORE {:?} {:#?}", root, execution_path.stack);
        }

        // Check if we're looping again. If so, we don't take this path
        if execution_path.executed_nodes.contains(&target) {
            continue;
        }

        let mut execution_path = execution_path.clone();
        if was_loop && weight == EdgeWeight::NonJump {
            execution_path
                .stack
                .push((None, Rc::new(std::cell::RefCell::new(vec![]))));
        }

        let mut paths = perform_partial_execution(
            target,
            code_graph,
            &mut execution_path,
            mapped_function_names,
            Arc::clone(&code),
        );

        if debug_stack {
            trace!("STACK AFTER {:?} {:#?}", root, execution_path.stack);
        }

        if crate::FILES_PROCESSED
            .get()
            .unwrap()
            .load(std::sync::atomic::Ordering::Relaxed)
            == 6
            && was_loop
        {
            //panic!("");
        }

        completed_paths.append(&mut paths);
    }

    completed_paths.push(execution_path.clone());
    completed_paths
}
