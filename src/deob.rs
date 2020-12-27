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
use std::rc::Rc;
use std::sync::Arc;

use crate::code_graph::*;

type TargetOpcode = pydis::opcode::Python27;

/// Deobfuscate the given code object. This will remove opaque predicates where possible,
/// simplify control flow to only go forward where possible, and rename local variables. This returns
/// the new bytecode and any function names resolved while deobfuscating the code object.
///
/// The returned HashMap is keyed by the code object's `$filename_$name` with a value of
/// what the suspected function name is.
pub fn deobfuscate_code(code: Arc<Code>) -> Result<(Vec<u8>, HashMap<String, String>)> {
    let debug = !true;

    let _bytecode = code.code.as_slice();
    let _consts = Arc::clone(&code.consts);
    let mut new_bytecode: Vec<u8> = vec![];
    let mut mapped_function_names = HashMap::new();

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

    fix_bbs_with_bad_instr(root_node_id, &mut code_graph, &code);

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

    let (nodes_to_remove, completed_paths) = perform_partial_execution(
        root_node_id,
        &mut code_graph,
        &mut execution_path,
        &mut mapped_function_names,
        Arc::clone(&code),
    );
    if counter == 5 {
        //panic!("{:#?}", completed_paths.first().unwrap().condition_results);
    }
    std::fs::write(
        format!("after_dead_{}.dot", counter),
        format!("{}", Dot::with_config(&code_graph, &[Config::EdgeNoLabel])),
    );

    println!("{:?}", nodes_to_remove);

    let mut nodes_to_remove_set = std::collections::BTreeSet::<NodeIndex>::new();
    nodes_to_remove_set.extend(nodes_to_remove.into_iter());

    let mut stop_at_queue = Vec::new();
    let mut node_queue = Vec::new();
    node_queue.push(root_node_id);
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
        let yes = code_graph[nx].instrs.len() > 0
            && code_graph[nx].instrs.last().unwrap().unwrap().opcode
                == TargetOpcode::POP_JUMP_IF_TRUE
            && code_graph[nx].instrs.last().unwrap().unwrap().arg.unwrap() == 480;
        if let Some(stop_at) = stop_at_queue.last() {
            if *stop_at == nx {
                stop_at_queue.pop();
            }
        }
        if code_graph[nx]
            .flags
            .contains(BasicBlockFlags::CONSTEXPR_CHECKED)
        {
            continue;
        }

        code_graph[nx].flags |= BasicBlockFlags::CONSTEXPR_CHECKED;

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
        let jump_path = targets
            .first()
            .and_then(|(target, weight)| if *weight == 1 { Some(*target) } else { None });

        for (target, _weight) in targets {
            // If this is the next node in the nodes to ignore, don't add it
            if let Some(pending) = stop_at_queue.last() {
                if *pending == target {
                    println!(
                        "skipping target {} (stop queue related)",
                        code_graph[target].start_offset
                    );
                    continue;
                }
            }

            if code_graph[target]
                .flags
                .contains(BasicBlockFlags::CONSTEXPR_CHECKED)
            {
                println!(
                    "skipping target {} (been checked)",
                    code_graph[target].start_offset
                );
                continue;
            }

            println!(
                "adding target {} to node queue",
                code_graph[target].start_offset
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
                let toggled_flags = code_graph[nx].flags & !BasicBlockFlags::CONSTEXPR_CONDITION;

                code_graph[nx].flags = toggled_flags;

                // Remove this node from nodes to remove, if it exists
                println!(
                    "removing {} from node removal list list",
                    code_graph[nx].start_offset
                );
                nodes_to_remove_set.remove(&nx);

                // println!("New flags: {:#?}", code_graph[nx].flags);

                // we may continue *only if* all paths agree on this node
                // in this node there are isolated instructions to remove
                if !insns_to_remove.contains_key(&nx) {
                    // Ok, we have a connecting node that could not be solved. We don't touch this node.
                    code_graph[nx].flags.remove(
                        BasicBlockFlags::CONSTEXPR_CONDITION | BasicBlockFlags::WILL_DELETE,
                    );

                    // Remove this node from nodes to remove, if it exists
                    nodes_to_remove_set.remove(&nx);
                    continue 'node_visitor;
                } else {
                    println!(
                        "{} node #{:?} can bypass: {:#?}. condition: {:?}. deleting: {:?}",
                        counter, nx, code_graph[nx].start_offset, path_value, insns_to_remove[&nx]
                    );
                    only_modify_self = true;
                }
                //if !nodes_with_isolated_constexprs.contains(&nx) {
                //}
            }
        }

        if nodes_to_remove_set.contains(&nx) {
            println!("deleting entire node...");
            code_graph[nx].flags |= BasicBlockFlags::WILL_DELETE;

            // if we're deleting this node, we should delete our children too
            let outgoing_edges = code_graph
                .edges_directed(nx, Direction::Outgoing)
                .map(|edge| {
                    println!("EDGE VALUE: {}", edge.weight());
                    (edge.id(), edge.target())
                })
                .collect::<Vec<_>>();

            code_graph.retain_edges(|_g, e| !outgoing_edges.iter().any(|outgoing| outgoing.0 == e));
            for (_target_edge, target) in outgoing_edges.iter().cloned().rev() {
                println!(
                    "REMOVING EDGE FROM {} TO {}",
                    code_graph[nx].start_offset, code_graph[target].start_offset
                );
                //code_graph.remove_edge(target_edge);

                // check if the target has any more incoming edges
                if code_graph
                    .edges_directed(target, Direction::Incoming)
                    .count()
                    == 0
                {
                    println!("edge count is 0, we can remove");
                    // make sure this node is flagged for removal
                    code_graph[target].flags |= BasicBlockFlags::WILL_DELETE;
                    nodes_to_remove_set.insert(target);
                }

                if code_graph[target].start_offset == 65535 {
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
                                if *edge.weight() != *path_value {
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

                            // check if the target has any more incoming edges
                            if code_graph
                                .edges_directed(target, Direction::Incoming)
                                .count()
                                == 0
                            {
                                // make sure this node is flagged for removal
                                code_graph[target].flags |= BasicBlockFlags::WILL_DELETE;
                                nodes_to_remove_set.insert(target);
                            }
                        }
                    }
                }

                let current_node = &mut code_graph[nx];
                current_node.instrs.remove(ins_idx);
            }
        }
        if yes {
            //panic!("{:#?}", code_graph[nx]);
        }

        // Remove this node if it has no more instructions
        let current_node = &code_graph[nx];
        if current_node.instrs.is_empty() {
            // if *code.filename == "26949592413111478" && *code.name == "50844295913873" {
            //     panic!("1");
            // }
            code_graph[nx].flags |= BasicBlockFlags::WILL_DELETE;
            nodes_to_remove_set.insert(nx);
            // code_graph[nx]
            //     .instrs
            //     .push(crate::smallvm::ParsedInstr::Good(Rc::new(Instruction {
            //         opcode: TargetOpcode::JUMP_FORWARD,
            //         arg: Some(0),
            //     })));
        }
        if yes {
            // panic!("{:#?}", code_graph[nx]);
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
    code_graph.retain_nodes(|g, node| {
        if nodes_to_remove_set.contains(&node) {
            println!("removing node starting at: {}", g[node].start_offset);
            // println!("{:?}", code_graph.node_indices());
            // println!("removing {:#?}", code_graph[node]);
            if node == root_node_id {
                // find the new root
                needs_new_root = true;
            }
            false
        } else {
            true
        }
    });

    std::fs::write(
        format!("target.dot"),
        format!("{}", Dot::with_config(&code_graph, &[Config::EdgeNoLabel])),
    );
    if needs_new_root {
        println!("{:#?}", code_graph.node_indices().collect::<Vec<_>>());
        root_node_id = code_graph.node_indices().next().unwrap();
        // for node in code_graph.node_indices() {
        //     // this is our new root if it has no incoming edges
        //     if code_graph.edges_directed(node, Direction::Incoming).count() == 0 {
        //         root_node_id = node;
        //         break;
        //     }
        // }
    }
    println!("root node is now: {:#?}", code_graph[root_node_id]);

    println!("yo?");

    std::fs::write(
        format!("target.dot"),
        format!("{}", Dot::with_config(&code_graph, &[Config::EdgeNoLabel])),
    );

    if counter == 1 {
        //panic!("");
    }
    if had_removed_nodes > 4 {
        //panic!("");
    }
    had_removed_nodes += 1;

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
    //insert_jump_0(root_node_id, &mut code_graph);
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

    Ok((new_bytecode, mapped_function_names))
}


pub fn rename_vars(
    code_data: &[u8],
    deobfuscated_code: &[Vec<u8>],
    mapped_function_names: &HashMap<String, String>,
) -> PyResult<Vec<u8>> {
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

    let mapped_names = PyDict::new(py);

    for (key, value) in mapped_function_names {
        mapped_names.set_item(
            py,
            cpython::PyString::new(py, key.as_ref()).into_object(),
            cpython::PyString::new(py, value.as_ref()).into_object(),
        );
    }
    module.add(py, "mapped_names", mapped_names)?;
    let locals = PyDict::new(py);
    locals.set_item(py, "deob", &module)?;

    let source = r#"
unknowns = 0

def cleanup_code_obj(code):
    global deobfuscated_code
    global mapped_names
    new_code = deobfuscated_code.pop(0)
    new_consts = []
    key = "{0}_{1}".format(code.co_filename, code.co_name)
    name = code.co_name
    if key in mapped_names:
        name = "{0}_{1}".format(mapped_names[key], name)
    else:
        name = fix_varnames([name])[0]
    for const in code.co_consts:
        if type(const) == types.CodeType:
            new_consts.append(cleanup_code_obj(const))
        else:
            new_consts.append(const)

    return types.CodeType(code.co_argcount, code.co_nlocals, code.co_stacksize, code.co_flags, new_code, tuple(new_consts), fix_varnames(code.co_names), fix_varnames(code.co_varnames), code.co_filename, name, code.co_firstlineno, code.co_lnotab, code.co_freevars, code.co_cellvars)


def fix_varnames(varnames):
    global unknowns
    newvars = []
    for var in varnames:
        var = var.strip()
        unallowed_chars = '!@#$%^&*()"\'/,. '
        banned_char = False
        for c in unallowed_chars:
            if c in var:
                banned_char = True
                
        if banned_char:
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
