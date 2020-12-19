use anyhow::Result;
use log::{debug, trace};
use py_marshal::{Code, Obj};
use pydis::prelude::*;
use std::collections::{BTreeMap, VecDeque};
use std::io::Cursor;
use std::sync::Arc;

/// Implements a deobfuscator for the given type
pub trait Deobfuscator {
    fn deobfuscate(&mut self) -> Result<()>;
}

impl Deobfuscator for Code {
    /// Deobfuscates a Python [`Code`] object in-place
    fn deobfuscate(&mut self) -> Result<()> {
        // SAFETY: we are the only ones processing this data from a single thread,
        // so getting a raw pointer and mutating should be safe.
        let consts_vec: &mut Vec<Obj> = unsafe { &mut *(Arc::as_ptr(&self.consts) as *mut Vec<_>) };
        for c in consts_vec {
            match &c {
                Obj::Code(code) => {
                    let inner_code: &mut Code = unsafe { &mut *(Arc::as_ptr(&code) as *mut Code) };
                    inner_code.deobfuscate()?;
                }
                _ => {
                    continue;
                }
            }
        }

        let bytecode: &mut Vec<u8> = unsafe { &mut *(Arc::as_ptr(&self.code) as *mut Vec<_>) };
        *bytecode = deobfuscate_bytecode(bytecode, Arc::clone(&self.consts))?;

        Ok(())
    }
}

type TargetOpcode = pydis::opcode::Python27;
use std::rc::Rc;
#[derive(Debug, Default)]
struct BasicBlock {
    start_offset: u64,
    end_offset: u64,
    instrs: Vec<std::rc::Rc<Instruction<TargetOpcode>>>,
}

use std::fmt;
impl fmt::Display for BasicBlock {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        writeln!(f, "Offset: {}", self.start_offset)?;
        for instr in &self.instrs {
            writeln!(f, "{}", instr)?;
        }

        Ok(())
    }
}

pub fn deobfuscate_bytecode(bytecode: &[u8], consts: Arc<Vec<Obj>>) -> Result<Vec<u8>> {
    let debug = !true;

    let mut new_bytecode: Vec<u8> = vec![];
    let analyzed_instructions =
        crate::smallvm::const_jmp_instruction_walker(bytecode, consts, |_instr, _offset| {
            // We don't care about instructions that are executed
            crate::smallvm::WalkerState::Continue
        })?;

    if true || debug {
        trace!("analyzed\n{:#?}", analyzed_instructions);
    }

    let first = analyzed_instructions.get(&0).cloned().unwrap();

    let mut curr_basic_block = BasicBlock::default();
    let mut code_graph = petgraph::Graph::<BasicBlock, u64>::new();
    let mut edges = vec![];
    let mut root_node_id = None;
    for (offset, instr) in analyzed_instructions {
        if curr_basic_block.instrs.is_empty() {
            curr_basic_block.start_offset = offset;
        }

        curr_basic_block.instrs.push(Rc::clone(&instr));

        if instr.opcode == TargetOpcode::RETURN_VALUE {
            curr_basic_block.end_offset = offset;
            let node_idx = code_graph.add_node(curr_basic_block);
            if root_node_id.is_none() {
                root_node_id = Some(node_idx);
            }

            curr_basic_block = BasicBlock::default();
            continue;
        }

        let next_instr = offset + instr.len() as u64;
        // if curr_basic_block.end_offset != 0 && next_instr == curr_basic_block.end_offset {
        //     curr_basic_block.end_offset = offset;
        //     let node_idx = code_graph.add_node(curr_basic_block);
        //     if root_node_id.is_none() {
        //         root_node_id = Some(node_idx);
        //     }

        //     if instr.opcode != TargetOpcode::RETURN_VALUE {
        //         edges.push((offset, next_instr, 0 as u64));
        //     }

        //     curr_basic_block = BasicBlock::default();
        //     continue;
        // }

        if instr.opcode.is_jump()
            || (curr_basic_block.end_offset != 0 && next_instr == curr_basic_block.end_offset)
        {
            curr_basic_block.end_offset = offset;

            // We need to see if the previous BB landed in the middle of this block.
            // If so, we should split this block
            if let Some((from, to, weight)) = edges.last() {
                if *to > curr_basic_block.start_offset && *to <= curr_basic_block.end_offset {
                    // It does indeed land in the middle of this block. Let's figure out which
                    // instruction it lands on
                    let mut ins_offset = curr_basic_block.start_offset;
                    let mut ins_index = None;
                    for (i, ins) in curr_basic_block.instrs.iter().enumerate() {
                        if *to == ins_offset {
                            ins_index = Some(i);
                            break;
                        }

                        ins_offset += ins.len() as u64;
                    }

                    let (new_bb_ins, curr_ins) =
                        curr_basic_block.instrs.split_at(ins_index.unwrap());

                    let split_bb = BasicBlock {
                        start_offset: curr_basic_block.start_offset,
                        end_offset: ins_offset - new_bb_ins.last().unwrap().len() as u64,
                        instrs: new_bb_ins.to_vec(),
                    };
                    edges.push((split_bb.end_offset, ins_offset, 0));
                    code_graph.add_node(split_bb);

                    curr_basic_block.start_offset = ins_offset;
                    curr_basic_block.instrs = curr_ins.to_vec();
                }
            }

            // Push the next instruction first -- ordering matters for the
            // breadth first search
            if instr.opcode.is_conditional_jump() || instr.opcode == TargetOpcode::FOR_ITER {
                edges.push((curr_basic_block.end_offset, next_instr, 0));
            }

            let mut next_instr_end = None;
            if instr.opcode.is_jump() {
                let target = if instr.opcode.is_absolute_jump() {
                    instr.arg.unwrap() as u64
                } else {
                    offset + instr.len() as u64 + instr.arg.unwrap() as u64
                };

                edges.push((curr_basic_block.end_offset, target, 1));

                if instr.opcode.is_conditional_jump() {
                    println!("next block should split at {}", target);
                    next_instr_end = Some(target);
                }
            }

            println!("{:#?}", curr_basic_block);

            let node_idx = code_graph.add_node(curr_basic_block);
            if root_node_id.is_none() {
                root_node_id = Some(node_idx);
            }

            curr_basic_block = BasicBlock::default();
            if let Some(next_instr_end) = next_instr_end {
                curr_basic_block.end_offset = next_instr_end;
            }
        }
    }

    println!("{:#?}", edges);

    use petgraph::IntoWeightedEdge;
    let edges = edges
        .iter()
        .filter_map(|(from, to, weight)| {
            let new_edge = (
                code_graph.node_indices().find(|i| {
                    (code_graph[*i].start_offset <= *from) && (code_graph[*i].end_offset >= *from)
                }),
                code_graph.node_indices().find(|i| {
                    (code_graph[*i].start_offset <= *to) && (code_graph[*i].end_offset >= *to)
                }),
            );

            println!("edge results: {:?}", new_edge);

            if new_edge.0.is_some() && new_edge.1.is_some() {
                Some((new_edge.0.unwrap(), new_edge.1.unwrap(), weight).into_weighted_edge())
            } else {
                None
            }
        })
        .collect::<Vec<_>>();

    code_graph.extend_with_edges(edges.as_slice());

    //println!("{:?}", code_graph.edges(root_node_id.unwrap()).next().unwrap());

    // Start joining blocks
    use petgraph::dot::{Config, Dot};
    std::fs::write(
        "before.dot",
        format!("{}", Dot::with_config(&code_graph, &[Config::EdgeNoLabel])),
    );
    panic!("test");
    while join_blocks(root_node_id.unwrap(), &mut code_graph) {}

    // if first.opcode == TargetOpcode::JUMP_ABSOLUTE && first.arg.unwrap() == 44 {
    //     panic!("");
    // }

    // update BB offsets
    let mut current_offset = 0u64;
    update_bb_offsets(
        root_node_id.unwrap(),
        &mut code_graph,
        &mut current_offset,
        None,
    );

    std::fs::write(
        "offsets.dot",
        format!("{}", Dot::with_config(&code_graph, &[Config::EdgeNoLabel])),
    );

    // update operands
    let mut bfs = Bfs::new(&code_graph, root_node_id.unwrap());
    let mut current_offset = 0;
    while let Some(nx) = bfs.next(&code_graph) {
        // Find our target if the condition evaluates successfully
        let edge_to_condition = code_graph
            .edges_directed(nx, Direction::Outgoing)
            .find(|edge| *edge.weight() == 1);

        // This node has no condition branches
        if edge_to_condition.is_none() {
            continue;
        }

        let edge_to_condition = edge_to_condition.unwrap();

        println!("target node: {:#?}", code_graph[edge_to_condition.target()]);
        let condition_target_offset = code_graph[edge_to_condition.target()].start_offset;

        let node = &mut code_graph[nx];
        println!("current node: {:#?}", node);
        let mut instr = node.instrs.last_mut().unwrap();
        let instr = unsafe { Rc::get_mut_unchecked(&mut instr) };
        // TODO: remap absolute and relative jump targets
        if instr.opcode.is_relative_jump() {
            instr.arg =
                Some((condition_target_offset - (node.end_offset + (instr.len() as u64))) as u16);
        } else {
            instr.arg = Some(condition_target_offset as u16);
        }
    }

    //panic!("{:#?}", analyzed_instructions);
    // if new_instruction_ordering.len() == 3 {
    // }
    let mut bfs = Bfs::new(&code_graph, root_node_id.unwrap());
    while let Some(nx) = bfs.next(&code_graph) {
        let node = &code_graph[nx];
        for instr in &node.instrs {
            new_bytecode.push(instr.opcode as u8);
            if let Some(arg) = instr.arg {
                new_bytecode.extend_from_slice(&arg.to_le_bytes()[..]);
            }
        }
    }

    std::fs::write(
        "after.dot",
        format!("{}", Dot::with_config(&code_graph, &[Config::EdgeNoLabel])),
    );
    panic!("test");

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
use petgraph::graph::{Graph, NodeIndex};
use petgraph::visit::{Bfs, EdgeRef};
use petgraph::Direction;
fn update_bb_offsets(
    root: NodeIndex,
    graph: &mut Graph<BasicBlock, u64>,
    current_offset: &mut u64,
    stop_at: Option<u64>,
) {
    // Count up the instructions in this node
    let end_offset = graph[root]
        .instrs
        .iter()
        .fold(0, |accum, instr| accum + instr.len());

    let end_offset = end_offset as u64;
    graph[root].start_offset = *current_offset;
    graph[root].end_offset = end_offset - graph[root].instrs.last().unwrap().len() as u64;

    *current_offset += end_offset;

    let mut edges = graph
        .edges_directed(root, Direction::Outgoing)
        .collect::<Vec<_>>();

    // Sort these edges so that we serialize the non-jump path comes first
    edges.sort_by(|a, b| a.weight().cmp(b.weight()));
    let targets = edges
        .iter()
        .map(|edge| (edge.weight().clone(), edge.target()))
        .collect::<Vec<_>>();

    for (weight, target) in targets {
        let node = &mut graph[target];
        if let Some(stop_at) = stop_at {
            // don't touch this node yet
            if stop_at <= node.start_offset {
                continue;
            }
        }

        // let stop_at = update_bb_offsets(
        //     target,
        //     graph,
        //     current_node,
        //     if weight == 0 {
        //         Some()
        //     } else {
        //     },
        // );
    }
}

fn join_blocks(root: NodeIndex, graph: &mut Graph<BasicBlock, u64>) -> bool {
    let mut bfs = Bfs::new(&*graph, root);
    while let Some(nx) = bfs.next(&*graph) {
        let current_node = &graph[nx];
        println!("Current node: {:#?}", current_node);
        let incoming_edges = graph.edges_directed(nx, Direction::Incoming);

        let num_incoming = incoming_edges.count();
        let outgoing_edges: Vec<u64> = graph
            .edges_directed(nx, Direction::Outgoing)
            .map(|edge| graph[edge.target()].start_offset)
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
        dbg!(parent_outgoing_edge_count);

        // Make sure that these nodes are not circular
        let are_circular = graph
            .edges_directed(nx, Direction::Outgoing)
            .any(|edge| edge.target() == source_node_index);

        dbg!(are_circular);

        if are_circular {
            continue;
        }

        let mut current_instrs = current_node.instrs.clone();
        let current_end_offset = current_node.end_offset;
        let parent_node = &mut graph[source_node_index];
        let parent_node_start_offset = parent_node.start_offset;

        println!("Parent node: {:#?}", parent_node);

        // Remove the last instruction -- this is our jump
        let removed_instruction = parent_node.instrs.pop().unwrap();
        println!("{:?}", removed_instruction);
        assert!(!removed_instruction.opcode.is_conditional_jump());

        // Adjust the merged node's offsets
        parent_node.end_offset = current_end_offset - (removed_instruction.len() as u64);

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
        for target_offset in outgoing_edges {
            let target_index = graph
                .node_indices()
                .find(|i| graph[*i].start_offset == target_offset)
                .unwrap();

            // Grab this node's index
            graph.add_edge(merged_node_index, target_index, 0);
        }

        return true;
    }

    false
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

    return types.CodeType(code.co_argcount, code.co_nlocals, code.co_stacksize, code.co_flags, new_code, tuple(new_consts), fix_varnames(code.co_names), fix_varnames(code.co_varnames), 'test', fix_varnames([code.co_name])[0], code.co_firstlineno, code.co_lnotab, code.co_freevars, code.co_cellvars)


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
