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

pub enum WalkerState {
    /// Continue parsing normally
    Continue,
    /// Stop parsing
    Break,
    /// Immediately start parsing at the given offset and continue parsing
    JumpTo(u64),
    /// Assume the result of the previous comparison evaluated to the given bool
    /// and continue parsing
    AssumeComparison(bool),
}

pub fn exec(code: Code, outer_code: Code) -> Result<Vec<u8>> {
    type opcode = pydis::opcode::Python27;

    let mut output = Vec::with_capacity(outer_code.code.len());
    let mut state = Some(State::Start);
    let mut rdr = Cursor::new(outer_code);

    // while let Some(current_state) = state.take() {
    //     match current_state {
    //         State::Start => {
    //             state = Some(State::FindExec);
    //         }
    //         State::FindExec => {
    //         }
    //     }
    // }

    let mut conditions_evaluated = 0;
    let mut begin_executing = false;

    const_jmp_instruction_walker(
        code.code.as_slice(),
        Arc::clone(&code.consts),
        |instr, offset| {
            if begin_executing {
            } else {
                if instr.opcode.is_conditional_jump() {
                    match conditions_evaluated {
                        0 => {
                            // This is the first check to see if id(marshal.loads) is != to some value
                            return WalkerState::AssumeComparison(false);
                        }
                        1 => {
                            // This is the second check to see if the sandbox has been established
                            return WalkerState::AssumeComparison(true);
                        }
                        2 => {
                            // This is the check to see if some `co_code` has been loaded
                            //
                            // In bytecode it looks like a UNARY_NOT followed by POP_JUMP_IF_TRUE
                            return WalkerState::AssumeComparison(true);
                        }
                        3 => {
                            return WalkerState::AssumeComparison(false);
                        }
                        _ => {
                            // Ignore other jumps
                        }
                    }
                    conditions_evaluated += 1;
                }
            }

            WalkerState::Continue
        },
    )?;

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
    F: FnMut(&Instruction<TargetOpcode>, u64) -> WalkerState,
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

        let next_instr_offset = rdr.position();

        let state = callback(&instr, offset);
        // We should stop decoding now
        if matches!(state, WalkerState::Break) {
            break;
        }

        //println!("Instruction: {:X?}", instr);
        instruction_sequence.push(Rc::clone(&instr));
        analyzed_instructions.insert(offset, Rc::clone(&instr));

        let mut ignore_jump_target = false;

        if instr.opcode.is_jump() {
            if instr.opcode.is_conditional_jump() {
                let mut previous_instruction = instruction_sequence.len() - 2;
                while let Some(prev) = instruction_sequence.get(previous_instruction) {
                    println!("previous: {:?}", prev);
                    // Check for potentially dead branches
                    if prev.opcode == TargetOpcode::LOAD_CONST {
                        let const_index = prev.arg.unwrap();
                        let cons = &consts[const_index as usize];
                        println!("{:?}", cons);
                        let top_of_stack = match cons {
                            Obj::Long(num) => {
                                use num_bigint::ToBigInt;
                                *num.as_ref() == 0.to_bigint().unwrap()
                            }
                            Obj::String(s) => !s.is_empty(),
                            Obj::Tuple(t) => !t.is_empty(),
                            Obj::List(l) => !l.read().unwrap().is_empty(),
                            Obj::Set(s) => !s.read().unwrap().is_empty(),
                            _ => panic!("need to handle const type: {:?}", cons.typ()),
                        };

                        let mut condition_is_met = match instr.opcode {
                            TargetOpcode::JUMP_IF_FALSE_OR_POP
                            | TargetOpcode::POP_JUMP_IF_FALSE => !top_of_stack,
                            TargetOpcode::JUMP_IF_TRUE_OR_POP | TargetOpcode::POP_JUMP_IF_TRUE => {
                                top_of_stack
                            }
                            _ => unreachable!(),
                        };
                        if let WalkerState::AssumeComparison(result) = state {
                            condition_is_met = result;
                        }

                        if condition_is_met {
                            // We always take this branch -- decode now
                            let target = if instr.opcode.is_relative_jump() {
                                next_instr_offset + instr.arg.unwrap() as u64
                            } else {
                                instr.arg.unwrap() as u64
                            };
                            queue!(target);
                            continue 'decode_loop;
                        } else {
                            ignore_jump_target = true;
                        }
                        break;
                    } else if prev.opcode.pushes_to_data_stack() {
                        // The stack has been modified most recently by something
                        // that doesn't load from const data. We don't do data flow
                        // analysis at the moment, so break out.
                        break;
                    } else {
                        previous_instruction -= 1;
                    }
                }
            }

            if matches!(
                instr.opcode,
                TargetOpcode::JUMP_ABSOLUTE | TargetOpcode::JUMP_FORWARD
            ) {
                // We've reached an unconditional jump. We need to decode the target
                let target = if instr.opcode.is_relative_jump() {
                    next_instr_offset + instr.arg.unwrap() as u64
                } else {
                    instr.arg.unwrap() as u64
                };

                rdr.set_position(target);
                match decode_py27(&mut rdr) {
                    Ok(instr) => {
                        // Queue the target
                        queue!(target);
                        if true || instr.opcode != TargetOpcode::FOR_ITER {
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
            queue!(next_instr_offset + instr.arg.unwrap() as u64);
        }

        if instr.opcode != TargetOpcode::RETURN_VALUE {
            queue!(next_instr_offset);
        }
    }

    if true || debug {
        println!("analyzed\n{:#?}", analyzed_instructions);
    }

    Ok(analyzed_instructions)
}
