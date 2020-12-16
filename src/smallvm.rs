use anyhow::Result;
use log::{debug, error};
use py_marshal::bstr::BString;
use py_marshal::*;
use pydis::prelude::*;
use std::collections::{BTreeMap, VecDeque};
use std::io::{Cursor, Read, Seek, SeekFrom};
use std::rc::Rc;
use std::sync::Arc;
type TargetOpcode = pydis::opcode::Python27;

pub enum WalkerState {
    /// Continue parsing normally
    Continue,
    /// Continue parsing and parse the next instruction even if it's already
    /// been parsed before
    ContinueIgnoreAnalyzedInstructions,
    /// Stop parsing
    Break,
    /// Immediately start parsing at the given offset and continue parsing
    JumpTo(u64),
    /// Assume the result of the previous comparison evaluated to the given bool
    /// and continue parsing
    AssumeComparison(bool),
}

impl WalkerState {
    fn force_queue_next(&self) -> bool {
        matches!(
            self,
            Self::ContinueIgnoreAnalyzedInstructions | Self::JumpTo(_) | Self::AssumeComparison(_)
        )
    }
}

type VmStack = VecDeque<Obj>;

pub fn exec_stage2(code: Arc<Code>, outer_code: Arc<Code>) -> Result<Vec<u8>> {
    let mut output = Vec::with_capacity(outer_code.code.len());
    let mut state = State::FindXorStart {
        make_functions_found: 0,
        function_index: 0,
    };

    #[derive(Clone)]
    enum State {
        FindXorStart {
            make_functions_found: usize,
            function_index: u16,
        },
        FindSwapMap(VecDeque<TargetOpcode>, u16),
        AssertInstructionSequence(VecDeque<TargetOpcode>, Box<State>),
        ExecuteVm(VmStack),
    }

    // while let Some(current_state) = state.take() {
    //     match current_state {
    //         State::Start => {
    //             state = Some(State::FindExec);
    //         }
    //         State::FindExec => {
    //         }
    //     }
    // }

    let mut original_code = Vec::clone(&outer_code.code);

    const_jmp_instruction_walker(
        code.code.as_slice(),
        Arc::clone(&code.consts),
        |instr, offset| {
            debug!("Instruction at {}: {:?}", offset, instr);
            match &mut state {
                State::FindXorStart {
                    make_functions_found,
                    function_index,
                } => {
                    if let TargetOpcode::LOAD_CONST = instr.opcode {
                        *function_index = instr.arg.unwrap();
                    }
                    if let TargetOpcode::MAKE_FUNCTION = instr.opcode {
                        *make_functions_found += 1;
                    }
                    if *make_functions_found == 3 {
                        // The next instruction processed will be our code that
                        // invokes the swapmap
                        state = State::FindSwapMap(
                            vec![
                                TargetOpcode::STORE_FAST,
                                TargetOpcode::BUILD_LIST,
                                TargetOpcode::BUILD_LIST,
                                TargetOpcode::LOAD_FAST,
                                TargetOpcode::LOAD_FAST,
                                TargetOpcode::CALL_FUNCTION,
                            ]
                            .into(),
                            *function_index,
                        );

                        return WalkerState::ContinueIgnoreAnalyzedInstructions;
                    }
                }
                State::FindSwapMap(seq, function_index) => {
                    assert_eq!(instr.opcode, seq.pop_front().unwrap());

                    // The last instruction is calling our SWAP_MAP function. Invoke that now
                    if seq.is_empty() {
                        // Now that we've discovered our swapmap function, let's figure out which
                        // of these consts is our swapmap
                        let function_const = &code.consts[*function_index as usize];
                        if let py_marshal::Obj::Code(function_code) = function_const {
                            let mut swapmap_index = None;
                            debug!("Found the swapmap function -- finding swapmap index");
                            const_jmp_instruction_walker(
                                function_code.code.as_slice(),
                                Arc::clone(&function_code.consts),
                                |instr, _offset| {
                                    if let TargetOpcode::LOAD_CONST = instr.opcode {
                                        swapmap_index = Some(instr.arg.unwrap() as usize);
                                        WalkerState::Break
                                    } else {
                                        WalkerState::Continue
                                    }
                                },
                            )
                            .expect("failed to walk function instructions");

                            // Now that we've found the swapmap, let's apply it to our
                            // original code
                            let swapmap_const = &function_code.consts[swapmap_index.unwrap()];
                            if let Obj::Dict(swapmap) = swapmap_const {
                                let swapmap = swapmap.read().unwrap();
                                for byte in &mut original_code {
                                    use num_bigint::ToBigInt;
                                    use num_traits::ToPrimitive;
                                    use std::convert::TryFrom;

                                    let byte_as_bigint = (*byte).to_bigint().unwrap();
                                    let swapmap_value = &swapmap[&ObjHashable::try_from(
                                        &Obj::Long(Arc::new(byte_as_bigint)),
                                    )
                                    .unwrap()];
                                    if let Obj::Long(value) = swapmap_value {
                                        *byte = (&*value).to_u8().unwrap();
                                    } else {
                                        panic!(
                                            "swapmap value should be a long, found: {:?}",
                                            swapmap_value.typ()
                                        );
                                    }
                                }
                            } else {
                                panic!(
                                    "suspected swapmap at index {} is a {:?}, not dict!",
                                    swapmap_index.unwrap(),
                                    function_const.typ()
                                );
                            }
                        } else {
                            panic!(
                                "const index {} is a {:?}, not code!",
                                function_index,
                                function_const.typ()
                            );
                        }

                        // Prepare the stack
                        let mut stack = VecDeque::new();
                        stack.push_back(Obj::String(Arc::new(BString::from(
                            outer_code.code.as_slice().to_vec(),
                        ))));

                        // We've successfully applied the swapmap! Let's now get
                        // to the point where we may execute the VM freely
                        state = State::AssertInstructionSequence(
                            vec![TargetOpcode::GET_ITER].into(),
                            Box::new(State::ExecuteVm(stack)),
                        );
                    }

                    return WalkerState::ContinueIgnoreAnalyzedInstructions;
                }
                State::AssertInstructionSequence(seq, next_state) => {
                    assert_eq!(instr.opcode, seq.pop_front().unwrap());

                    if seq.is_empty() {
                        // TODO: bad allocation since we cannot move out of a referenced
                        // box
                        state = *(next_state.clone());
                    }

                    return WalkerState::ContinueIgnoreAnalyzedInstructions;
                }
                State::ExecuteVm(stack) => {
                    match instr.opcode {
                        TargetOpcode::FOR_ITER => {}
                        other => panic!("Unhandled opcode: {:?}", other),
                    }

                    // We want to execute sequentially -- ignore the rest of the queue
                    // for now
                    return WalkerState::ContinueIgnoreAnalyzedInstructions;
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
            queue!($offset, false)
        };
        ($offset:expr, $force_queue:expr) => {
            if $force_queue {
                if debug {
                    debug!("adding instruction at {} to front queue", $offset);
                }
                instruction_queue.push_front($offset);
            } else if (!analyzed_instructions.contains_key(&$offset)
                && !instruction_queue.contains(&$offset))
            {
                if debug {
                    debug!("adding instruction at {} to queue", $offset);
                }
                instruction_queue.push_back($offset);
            }
        };
    };

    if debug {
        debug!("{:#?}", consts);
    }

    'decode_loop: while let Some(offset) = instruction_queue.pop_front() {
        if debug {
            debug!("offset: {}", offset);
        }
        rdr.set_position(offset);
        // Ignore invalid instructions
        let instr = match decode_py27(&mut rdr) {
            Ok(instr) => Rc::new(instr),
            Err(e @ pydis::error::DecodeError::UnknownOpcode(_)) => {
                error!("");
                debug!(
                    "Error decoding queued instruction at position: {}: {}",
                    offset, e
                );

                debug!(
                    "previous: {:?}",
                    instruction_sequence[instruction_sequence.len() - 1]
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
                        debug!("removing {:?}", analyzed_instructions.get(&offset));
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
                debug!("new conditional jump: {:?}", instr);
                while let Some(prev) = instruction_sequence.get(previous_instruction) {
                    debug!("previous: {:?}", prev);
                    // Check for potentially dead branches
                    if prev.opcode == TargetOpcode::LOAD_CONST {
                        let const_index = prev.arg.unwrap();
                        let cons = &consts[const_index as usize];
                        debug!("{:?}", cons);
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
                            queue!(target, state.force_queue_next());
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
                        queue!(target, state.force_queue_next());
                        continue;
                    }
                    Err(e @ pydis::error::DecodeError::UnknownOpcode(_)) => {
                        // Definitely do not queue this target
                        ignore_jump_target = true;

                        error!(
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
            queue!(instr.arg.unwrap() as u64, state.force_queue_next());
        }

        if !ignore_jump_target && instr.opcode.is_relative_jump() {
            queue!(next_instr_offset + instr.arg.unwrap() as u64);
        }

        if instr.opcode != TargetOpcode::RETURN_VALUE {
            queue!(next_instr_offset, state.force_queue_next());
        }
    }

    if true || debug {
        debug!("analyzed\n{:#?}", analyzed_instructions);
    }

    Ok(analyzed_instructions)
}
