use anyhow::Result;
use py_marshal::{Code, Obj};
use pydis::decode;
use pydis::error::DecodeError;
use pydis::opcode::*;
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
    let debug = false;
    let mut rdr = Cursor::new(bytecode);
    // Offset of instructions that need to be read
    let mut instruction_queue = VecDeque::<u64>::new();
    let mut analyzed_instructions = BTreeMap::<u64, Instruction>::new();
    let mut new_bytecode = Vec::with_capacity(bytecode.len());

    instruction_queue.push_front(0);

    macro_rules! queue {
        ($offset:expr) => {
            if !analyzed_instructions.contains_key(&$offset) {
                instruction_queue.push_back($offset);
            }
        };
    };

    if debug {
        println!("{:#?}", consts);
    }

    while let Some(offset) = instruction_queue.pop_front() {
        rdr.set_position(offset);
        // Ignore invalid instructions
        let instr = match decode(&mut rdr) {
            Ok(instr) => instr,
            Err(pydis::error::DecodeError::UnknownOpcode(_)) => {
                continue;
            }
            Err(e) => {
                return Err(e.into());
            }
        };

        //println!("Instruction: {:X?}", instr);
        analyzed_instructions.insert(offset, instr.clone());

        let mut ignore_jump_target = false;

        match instr.opcode {
            // We follow some absolute jumps immediately
            Opcode::JUMP_ABSOLUTE => {
                // Check the target
                let target = instr.arg.unwrap() as u64;
                rdr.set_position(target);
                let instr = decode(&mut rdr)?;
                if instr.opcode != Opcode::FOR_ITER {
                    queue!(target);
                    continue;
                }
            }
            Opcode::JUMP_FORWARD => {
                // Check the target
                let target = offset + instr.arg.unwrap() as u64;
                rdr.set_position(target);
                let instr = decode(&mut rdr)?;
                if instr.opcode != Opcode::FOR_ITER {
                    queue!(target);
                    continue;
                }
            }
            Opcode::POP_JUMP_IF_FALSE | Opcode::POP_JUMP_IF_TRUE => {
                for maybe_prev_instr in (offset-4..offset).rev() {
                    if let Some(prev) = analyzed_instructions.get(&maybe_prev_instr) {
                        // Check for potentially dead branches
                        if prev.opcode == Opcode::LOAD_CONST {
                            let const_index = prev.arg.unwrap();
                            if let Obj::Long(num) = &consts[const_index as usize] {
                                use num_bigint::ToBigInt;
                                if *num.as_ref() == 0.to_bigint().unwrap() {
                                    ignore_jump_target = true;
                                }
                            }
                        }
                    }
                }
            }
            _ => {
                // Do nothing with the rest for now
            }
        }

        if !ignore_jump_target && instr.opcode.is_absolute_jump() {
            queue!(instr.arg.unwrap() as u64);
        }

        if !ignore_jump_target && instr.opcode.is_relative_jump() {
            queue!(offset + instr.arg.unwrap() as u64);
        }

        if instr.opcode != Opcode::RETURN_VALUE {
            queue!(offset + instr.arg.map_or(1, |_| 3));
        }
    }

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
            // We're going to skip this instruction -- it was likely overleaved with another one
        }
    }

    if new_bytecode.len() != bytecode.len() {
        let required_padding = bytecode.len() - new_bytecode.len();
        if required_padding != 0 {
            new_bytecode.append(&mut vec![Opcode::NOP as u8; required_padding]);
        }
    }

    if debug {
        let mut cursor = std::io::Cursor::new(&new_bytecode);
        println!("{}", cursor.position());
        while let Ok(instr) = pydis::decode(&mut cursor) {
            println!("{:?}", instr);
            println!("");
            println!("{}", cursor.position());
        }
    }

    assert_eq!(new_bytecode.len(), bytecode.len());

    Ok(new_bytecode)
}
