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

pub fn deobfuscate_bytecode(bytecode: &[u8], consts: Arc<Vec<Obj>>) -> Result<Vec<u8>> {
    type TargetOpcode = pydis::opcode::Python27;

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

    // mapping of old instruction offsets to their new one
    let mut new_instruction_offsets = BTreeMap::<u64, u64>::new();
    let mut new_instruction_ordering = Vec::new();

    // We need to rewrite conditional jumps to point to the correct offset
    let mut current_offset = 0u64;
    let mut offset_queue = VecDeque::new();
    offset_queue.push_back(*analyzed_instructions.first_key_value().unwrap().0);
    println!("");
    println!("");

    while let Some(offset) = offset_queue.pop_front() {
        // grab this instruction
        let instr = match analyzed_instructions.get(&offset) {
            Some(instr) => instr,
            None => continue,
        };
        match instr.opcode {
            TargetOpcode::JUMP_ABSOLUTE => {
                let target_offset = instr.arg.unwrap() as u64;
                // follow this instruction if it's not part of a loop
                if let Some(target_instr) = analyzed_instructions.get(&target_offset) {
                    if target_instr.opcode != TargetOpcode::FOR_ITER
                        && !new_instruction_offsets.contains_key(&target_offset)
                    {
                        offset_queue.push_front(target_offset);
                    }
                    continue;
                }
            }
            TargetOpcode::JUMP_FORWARD => {
                let target_offset = instr.arg.unwrap() as u64 + 3;

                if !new_instruction_offsets.contains_key(&target_offset) {
                    offset_queue.push_front(target_offset);
                }

                continue;
            }
            _ => {}
        }

        new_instruction_offsets.insert(offset, current_offset);
        new_instruction_ordering.push(offset);
        current_offset += instr.arg.map_or(1, |_| 3);
        offset_queue.push_back(offset + instr.arg.map_or(1, |_| 3));
    }

    // Start writing out the new instructions
    for offset in new_instruction_ordering {
        let instr = analyzed_instructions.get(&offset).unwrap();
        println!("writing: {:?}", instr);
        new_bytecode.push(instr.opcode as u8);

        if instr.opcode.is_relative_jump() {
            let target = (offset + 3) + instr.arg.unwrap() as u64;
            if let Some(new_target) = new_instruction_offsets.get(&target).cloned() {
                let this_new_offset = *new_instruction_offsets.get(&offset).unwrap();
                let new_target = new_target - (this_new_offset + 3);
                let new_target = new_target as u16;

                // look up the new offset and write that
                new_bytecode.extend_from_slice(&new_target.to_le_bytes()[..]);
            } else {
                new_bytecode.push(TargetOpcode::POP_TOP as u8);
            }
        } else if instr.opcode.is_absolute_jump() {
            let target = instr.arg.unwrap() as u64;
            if let Some(new_target) = new_instruction_offsets.get(&target).cloned() {
                let new_target = new_target as u16;

                // look up the new offset and write that
                new_bytecode.extend_from_slice(&new_target.to_le_bytes()[..]);
            } else {
                new_bytecode.push(TargetOpcode::POP_TOP as u8);
            }
        } else if let Some(arg) = instr.arg {
            new_bytecode.extend_from_slice(&arg.to_le_bytes()[..]);
        }
    }

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
    
    return types.CodeType(code.co_argcount, code.co_nlocals, code.co_stacksize, code.co_flags, new_code, tuple(new_consts), code.co_names, fix_varnames(code.co_varnames), 'test', fix_varnames([code.co_name])[0], code.co_firstlineno, code.co_lnotab, code.co_freevars, code.co_cellvars)


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
