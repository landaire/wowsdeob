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
use crate::code_graph::{CodeGraph, BasicBlockFlags};

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
    pub condition_results: HashMap<NodeIndex, Option<(u64, Vec<AccessTrackingInfo>)>>,
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
) -> (Vec<NodeIndex>, Vec<ExecutionPath>) {
    let debug = false;
    let current_node = &code_graph.graph[root];
    let mut nodes_to_remove = Vec::new();
    let mut edges = code_graph.graph
        .edges_directed(root, Direction::Outgoing)
        .collect::<Vec<_>>();

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
            trace!(
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
                trace!("TOS: {:?}", tos);
            }

            // we may be able to cheat by looking at the other paths. if one contains
            // bad instructions, we can safely assert we will not take that path
            // TODO: This may be over-aggressive and remove variables that are later used
            if false && tos.is_none() {
                let mut jump_path_has_bad_instrs = None;
                for (weight, target, _id) in &targets {
                    if code_graph.graph[*target].has_bad_instrs {
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
                code_graph.graph[root].flags |= BasicBlockFlags::CONSTEXPR_CONDITION;

                if debug {
                    trace!("{:#?}", modifying_instructions);
                }
                let modifying_instructions = Rc::clone(modifying_instructions);

                if debug {
                    trace!("{:#?}", code_graph.graph[root]);
                    trace!("{:?} {:#?}", tos, modifying_instructions);

                    trace!("{:?}", instr);
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
                if debug {
                    trace!("{:?}", instr);
                    trace!("stack after: {:#?}", execution_path.stack);
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
                    let goes_through_this_constexpr =
                        astar(&code_graph.graph, target, |finish| finish == node, |_e| 0, |_| 0)
                            .map(|(_cost, path)| path.iter().any(|node| *node == root))
                            .unwrap_or_default();
                    if goes_through_this_constexpr || !code_graph.is_downgraph(target, node) {
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
                execution_path.condition_results.insert(
                    root,
                    Some((target_weight, modifying_instructions.borrow().clone())),
                );
                trace!("dead code analysis on: {:?}", code_graph.graph[target]);
                let (mut rnodes, mut paths) = perform_partial_execution(
                    target,
                    code_graph,
                    execution_path,
                    mapped_function_names,
                    Arc::clone(&code),
                );

                nodes_to_remove.append(&mut rnodes);
                completed_paths.append(&mut paths);

                return (nodes_to_remove, completed_paths);
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
                                let source_instruction = &code_graph.graph[*source_node].instrs[*idx].unwrap();
                                source_instruction.opcode == TargetOpcode::MAKE_FUNCTION
                            });
                    if was_make_function {
                        let (const_origination_node, const_idx) =
                            &accessing_instructions.borrow()[0];

                        let const_instr = &code_graph.graph[*const_origination_node].instrs[*const_idx];
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
                trace!("Encountered error executing instruction: {:?}", e);
                let last_instr = current_node.instrs.last().unwrap().unwrap();

                completed_paths.push(execution_path.clone());
                return (nodes_to_remove, completed_paths);
            }
        }

        if debug {
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
        if let Some(last_instr) = code_graph.graph[root].instrs.last().map(|instr| instr.unwrap()) {
            // we never follow exception paths
            if last_instr.opcode == TargetOpcode::SETUP_EXCEPT && weight == 1 {
                if debug {
                    trace!("skipping -- it's SETUP_EXCEPT");
                }
                continue;
            }

            // we never go in to loops
            if last_instr.opcode == TargetOpcode::FOR_ITER && weight == 0 {
                if debug {
                    trace!("skipping -- it's for_iter");
                }
                continue;
            }
        }

        // Make sure that we're not being cyclic
        let is_cyclic = code_graph.graph
            .edges_directed(target, Direction::Outgoing)
            .any(|edge| edge.target() == root);
        if is_cyclic {
            if debug {
                trace!("skipping -- root is downgraph from target");
            }
            continue;
        }

        if debug {
            trace!("STACK BEFORE {:?} {:#?}", root, execution_path.stack);
        }
        let (mut rnodes, mut paths) = perform_partial_execution(
            target,
            code_graph,
            execution_path,
            mapped_function_names,
            Arc::clone(&code),
        );
        if debug {
            trace!("STACK AFTER {:?} {:#?}", root, execution_path.stack);
        }

        nodes_to_remove.append(&mut rnodes);
        completed_paths.append(&mut paths);
    }

    completed_paths.push(execution_path.clone());
    (nodes_to_remove, completed_paths)
}