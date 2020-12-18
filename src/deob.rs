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

        if instr.opcode.is_jump() {
            curr_basic_block.end_offset = offset;
            let next_instr = offset + 3;
            let target = if instr.opcode.is_absolute_jump() {
                instr.arg.unwrap() as u64
            } else {
                offset + 3 + instr.arg.unwrap() as u64
            };

            edges.push((curr_basic_block.start_offset, target));
            if instr.opcode.is_conditional_jump() {
                edges.push((curr_basic_block.start_offset, next_instr));
            }

            let node_idx = code_graph.add_node(curr_basic_block);
            if root_node_id.is_none() {
                root_node_id = Some(node_idx);
            }

            curr_basic_block = BasicBlock::default();
        }

        if instr.opcode == TargetOpcode::RETURN_VALUE {
            code_graph.add_node(curr_basic_block);
            curr_basic_block = BasicBlock::default();
        }
    }


    let edges = edges
        .iter()
        .filter_map(|(from, to)| {
            let new_edge = (
                code_graph
                    .node_indices()
                    .find(|i| (code_graph[*i].start_offset == *from) || (code_graph[*i].end_offset== *from)),
                code_graph
                    .node_indices()
                    .find(|i| (code_graph[*i].start_offset == *to) || (code_graph[*i].end_offset== *to)),
            );

            if new_edge.0.is_some() && new_edge.1.is_some() {
                Some((new_edge.0.unwrap(), new_edge.1.unwrap()))
            } else {
                None
            }
        })
        .collect::<Vec<_>>();

    code_graph.extend_with_edges(edges.as_slice());

    //println!("{:?}", code_graph.edges(root_node_id.unwrap()).next().unwrap());

    // Start joining blocks
    if first.opcode == TargetOpcode::JUMP_ABSOLUTE && first.arg.unwrap() == 44 {
        while join_blocks(root_node_id.unwrap(), &mut code_graph) {}
    }

    use petgraph::dot::{Config, Dot};
    std::fs::write("out.dot", format!("{}", Dot::with_config(&code_graph, &[Config::EdgeNoLabel])));
    if first.opcode == TargetOpcode::JUMP_ABSOLUTE && first.arg.unwrap() == 44 {
        panic!("");
    }


    //panic!("{:#?}", analyzed_instructions);
    // if new_instruction_ordering.len() == 3 {
    // }

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
use petgraph::visit::{EdgeRef, Bfs};
use petgraph::graph::{Graph, NodeIndex};
use petgraph::Direction;
fn join_blocks(root: NodeIndex, graph: &mut Graph::<BasicBlock, u64>) -> bool {
    let mut bfs = Bfs::new(&*graph, root);
    while let Some(nx) = bfs.next(&*graph) {
        let current_node = &graph[nx];
        println!("{:?}", current_node);
        let incoming_edges = graph.edges_directed(nx, Direction::Incoming);
        let num_incoming = incoming_edges.count();
        let outgoing_edges: Vec<u64> = graph.edges_directed(nx, Direction::Outgoing).map(|edge| graph[edge.target()].start_offset).collect();
        if num_incoming == 1 {
            // Grab the incoming edge and see how many incoming edges it has. We might be able
            // to combine these nodes
            let incoming_edge = graph.edges_directed(nx, Direction::Incoming).next().unwrap();
            let source_node_index = incoming_edge.source();
            let mut current_instrs = current_node.instrs.clone();
            let parent_node = &mut graph[source_node_index];

            // Remove the last instruction -- this is our jump
            let last_instr_in_block  = parent_node.instrs.pop();
            assert!(!last_instr_in_block.unwrap().opcode.is_conditional_jump());
            println!("parent: {:?}", parent_node);
            // Move this node's instructions into the parent
            parent_node.instrs.append(&mut current_instrs);

            graph.remove_node(nx);

            // Re-add the old node's outgoing edges
            for target_offset in outgoing_edges {
                let target_index = graph
                    .node_indices()
                    .find(|i| graph[*i].start_offset == target_offset).unwrap();

                // Grab this node's index
                graph.add_edge(source_node_index, target_index, 0);
            }

            return true;
        }
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
