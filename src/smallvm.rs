use anyhow::Result;
use py_marshal::*;
use pydis::prelude::*;
use std::collections::{BTreeMap, VecDeque};
use std::io::{Cursor, Read, Seek, SeekFrom};
use std::rc::Rc;
use std::sync::Arc;
type TargetOpcode = pydis::opcode::Python27;

enum State {
    Start,
    FindExec,
}

pub fn exec(code: Code, outer_code: Code) -> Result<Vec<u8>> {
    type opcode = pydis::opcode::Python27;

    let mut output = Vec::with_capacity(outer_code.code.len());
    let mut state = Some(State::Start);
    let mut rdr = Cursor::new(outer_code);

    while let Some(current_state) = state.take() {
        match current_state {
            State::Start => {
                state = Some(State::FindExec);
            }
            State::FindExec => {
                rdr.set_position(0);
                let mut exec_offset = None;
                const_jmp_instruction_walker(
                    code.code.as_slice(),
                    Arc::clone(&code.consts),
                    |instr, offset| {
                        if let TargetOpcode::EXEC_STMT = instr.opcode {
                            exec_offset = Some(offset);
                            false
                        } else {
                            true
                        }
                    },
                )?;
            }
        }
    }

    Ok(output)
}

/// Walks the bytecode in a manner that only follows what "looks like" valid
/// codepaths. This will only decode instructions that are either proven statically
/// to be taken (with `JUMP_ABSOLUTE`, `JUMP_IF_TRUE` with a const value that evaluates
/// to true, etc.)
pub fn const_jmp_instruction_walker<F>(
    bytecode: &[u8],
    consts: Arc<Vec<Obj>>,
    mut callback: F,
) -> Result<BTreeMap<u64, Rc<Instruction<TargetOpcode>>>>
where
    F: FnMut(&Instruction<TargetOpcode>, u64) -> bool,
{
    let debug = !true;
    let mut rdr = Cursor::new(bytecode);
    let mut instruction_sequence = Vec::new();
    let mut analyzed_instructions = BTreeMap::<u64, Rc<Instruction<TargetOpcode>>>::new();
    // Offset of instructions that need to be read
    let mut instruction_queue = VecDeque::<u64>::new();

    instruction_queue.push_front(0);

    macro_rules! queue {
        ($offset:expr) => {
            if !analyzed_instructions.contains_key(&$offset) {
                if debug {
                    println!("adding instruction at {} to queue", $offset);
                }
                instruction_queue.push_back($offset);
            }
        };
    };

    if debug {
        println!("{:#?}", consts);
    }

    'decode_loop: while let Some(offset) = instruction_queue.pop_front() {
        if debug {
            println!("offset: {}", offset);
        }
        rdr.set_position(offset);
        // Ignore invalid instructions
        let instr = match decode_py27(&mut rdr) {
            Ok(instr) => Rc::new(instr),
            Err(e @ pydis::error::DecodeError::UnknownOpcode(_)) => {
                eprintln!(
                    "Error decoding queued instruction at position: {}: {}",
                    offset, e
                );

                // We need to remove all instructions parsed between the last
                // conditional jump and this instruction
                if let Some(last_jump_offset) =
                    analyzed_instructions
                        .iter()
                        .rev()
                        .find_map(|(addr, instr)| {
                            if *addr < offset && instr.opcode.is_jump() {
                                Some(*addr)
                            } else {
                                None
                            }
                        })
                {
                    let bad_offsets: Vec<u64> = analyzed_instructions
                        .keys()
                        .into_iter()
                        .filter(|addr| **addr > last_jump_offset && **addr < offset)
                        .copied()
                        .collect();

                    for offset in bad_offsets {
                        analyzed_instructions.remove(&offset);
                    }
                }

                continue;
            }
            Err(e) => {
                return Err(e.into());
            }
        };

        if !callback(&instr, offset) {
            // We should stop decoding now
            break;
        }

        //println!("Instruction: {:X?}", instr);
        instruction_sequence.push(Rc::clone(&instr));
        analyzed_instructions.insert(offset, Rc::clone(&instr));

        let mut ignore_jump_target = false;

        if instr.opcode.is_jump() {
            if instr.opcode.is_conditional_jump() {
                if let Some(prev) = instruction_sequence.get(instruction_sequence.len() - 2) {
                    println!("previous: {:?}", prev);
                    // Check for potentially dead branches
                    if prev.opcode == TargetOpcode::LOAD_CONST {
                        let const_index = prev.arg.unwrap();
                        if let Obj::Long(num) = &consts[const_index as usize] {
                            use num_bigint::ToBigInt;
                            let top_of_stack = *num.as_ref() == 0.to_bigint().unwrap();
                            let condition_is_met = match instr.opcode {
                                TargetOpcode::JUMP_IF_FALSE_OR_POP
                                | TargetOpcode::POP_JUMP_IF_FALSE => !top_of_stack,
                                TargetOpcode::JUMP_IF_TRUE_OR_POP
                                | TargetOpcode::POP_JUMP_IF_TRUE => top_of_stack,
                                _ => unreachable!(),
                            };

                            if condition_is_met {
                                ignore_jump_target = true;
                            } else {
                                // We always take this branch -- decode now
                                queue!(instr.arg.unwrap() as u64);
                                continue 'decode_loop;
                            }
                        }
                    }
                }
            } else if matches!(
                instr.opcode,
                TargetOpcode::JUMP_ABSOLUTE | TargetOpcode::JUMP_FORWARD
            ) {
                // We've reached an unconditional jump. We need to decode the target
                let target = if instr.opcode.is_relative_jump() {
                    offset + instr.arg.unwrap() as u64
                } else {
                    instr.arg.unwrap() as u64
                };

                rdr.set_position(target);
                match decode_py27(&mut rdr) {
                    Ok(instr) => {
                        // Queue the target
                        queue!(target);
                        if instr.opcode != TargetOpcode::FOR_ITER {
                            continue;
                        }
                    }
                    Err(e @ pydis::error::DecodeError::UnknownOpcode(_)) => {
                        // Definitely do not queue this target
                        ignore_jump_target = true;

                        eprintln!(
                            "Erorr while parsing target opcode: {} at position {}",
                            e, offset
                        );
                    }
                    Err(e) => {
                        return Err(e.into());
                    }
                }
            }
        }

        if !ignore_jump_target && instr.opcode.is_absolute_jump() {
            queue!(instr.arg.unwrap() as u64);
        }

        if !ignore_jump_target && instr.opcode.is_relative_jump() {
            queue!(offset + instr.arg.unwrap() as u64);
        }

        if instr.opcode != TargetOpcode::RETURN_VALUE {
            queue!(offset + instr.arg.map_or(1, |_| 3));
        }
    }

    if true || debug {
        println!("analyzed\n{:#?}", analyzed_instructions);
    }

    Ok(analyzed_instructions)
}
