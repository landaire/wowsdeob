use anyhow::Result;
use log::debug;
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
    type Opcode = pydis::opcode::Python27;

    let debug = !true;

    let analyzed_instructions =
        crate::smallvm::const_jmp_instruction_walker(bytecode, consts, |_instr, _offset| {
            // We don't care about instructions that are executed
            crate::smallvm::WalkerState::Continue
        })?;

    let mut new_bytecode = Vec::with_capacity(analyzed_instructions.len() * 3);

    if true || debug {
        debug!("analyzed\n{:#?}", analyzed_instructions);
    }
    let mut has_interleaved_instructions = false;

    // println!("{:#?}", analyzed_instructions);
    // Now that we've traced the bytecode we need to clean up
    //println!("{:#X?}", analyzed_instructions);
    for (offset, instr) in analyzed_instructions {
        // Instructions may have been overleaved
        if new_bytecode.len() <= offset as usize {
            let required_padding = offset as usize - new_bytecode.len();
            if required_padding > 0 {
                new_bytecode.append(&mut vec![Opcode::NOP as u8; required_padding as usize]);
            }

            new_bytecode.push(instr.opcode as u8);
            if let Some(arg) = instr.arg {
                new_bytecode.extend_from_slice(&arg.to_le_bytes()[..]);
            }
        } else {
            has_interleaved_instructions = true;
            // We have already written data at this address -- we probably have
            // instructions that are interleaved with each other. e.g. a
            // LOAD_CONST (arg)
            // where the ARG byte is actually a jump target later.
            if let Some(arg) = instr.arg {
                let arg_bytes = arg.to_le_bytes();
                let bytes = [instr.opcode as u8, arg_bytes[0], arg_bytes[1]];

                if new_bytecode.len() < offset as usize + 3 {
                    let bytes_needed = (offset as usize + 3) - new_bytecode.len();

                    new_bytecode.extend_from_slice(&bytes[3 - bytes_needed..]);
                }
            }
        }
    }
    dbg!(has_interleaved_instructions);

    if new_bytecode.len() != bytecode.len() {
        let required_padding = bytecode.len() - new_bytecode.len();
        if required_padding != 0 {
            new_bytecode.append(&mut vec![Opcode::NOP as u8; required_padding]);
        }
    }

    if debug {
        let mut cursor = std::io::Cursor::new(&new_bytecode);
        debug!("{}", cursor.position());
        while let Ok(instr) = decode_py27(&mut cursor) {
            debug!("{:?}", instr);
            debug!("");
            debug!("{}", cursor.position());
        }
    }

    // if referenced_consts.len() != consts.len() {
    //     for (i, c) in consts.iter().enumerate() {
    //         if referenced_consts.contains(&(i as u16)) {
    //             continue;
    //         }
    //         println!("unreferenced const: {:?}", c);
    //     }
    // }
    // assert_eq!(referenced_consts.len(), consts.len());

    assert_eq!(new_bytecode.len(), bytecode.len());

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
