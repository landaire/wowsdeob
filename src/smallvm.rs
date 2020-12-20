use anyhow::Result;
use log::{debug, error, trace};
use num_bigint::ToBigInt;
use num_traits::ToPrimitive;
use py_marshal::bstr::{BStr, BString};
use py_marshal::*;
use pydis::prelude::*;
use std::collections::{BTreeMap, HashMap, VecDeque};
use std::convert::TryFrom;
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

/// Represents a VM variable. The value is either `Some` (something we can)
/// statically resolve or `None` (something that cannot be resolved statically)
pub type VmVar = Option<Obj>;
pub type VmStack = Vec<VmVar>;
pub type VmVars = HashMap<u16, VmVar>;

pub fn exec_stage2(code: Arc<Code>, outer_code: Arc<Code>) -> Result<Vec<u8>> {
    let output = Arc::new(BString::from(Vec::with_capacity(outer_code.code.len())));
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
        ExecuteVm(VmStack, VmVars),
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
            trace!("Instruction at {}: {:?}", offset, instr);
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
                            trace!("Found the swapmap function -- finding swapmap index");
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

                        // We've successfully applied the swapmap! Let's now get
                        // to the point where we may execute the VM freely
                        state = State::AssertInstructionSequence(
                            vec![
                                TargetOpcode::GET_ITER,
                                // when we encounter the FOR_ITER we need to jump
                                // out of the loop
                                TargetOpcode::FOR_ITER,
                                // These instructions are post-loop
                                TargetOpcode::GET_ITER,
                            ]
                            .into(),
                            Box::new(State::ExecuteVm(
                                vec![
                                    Some(Obj::String(Arc::clone(&output))),
                                    Some(Obj::String(Arc::new(
                                        // reverse this data so we can use it as a proper-ordered stack
                                        BString::from(
                                            original_code
                                                .iter()
                                                .rev()
                                                .cloned()
                                                .collect::<Vec<u8>>(),
                                        ),
                                    ))),
                                ],
                                HashMap::new(),
                            )),
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

                    // Jump out of any loops
                    if let TargetOpcode::FOR_ITER = instr.opcode {
                        return WalkerState::JumpTo(offset + 3 + (instr.arg.unwrap() as u64));
                    }

                    return WalkerState::ContinueIgnoreAnalyzedInstructions;
                }
                State::ExecuteVm(stack, vars) => {
                    // Check if our bytecode has been drained. This should be index 0 on the satck
                    if let Some(Obj::String(s)) = &stack[1] {
                        if s.is_empty() && instr.opcode == TargetOpcode::FOR_ITER {
                            return WalkerState::Break;
                        }
                    }

                    execute_instruction(
                        &instr,
                        Arc::clone(&code),
                        stack,
                        vars,
                        |function, args, kwargs| match function {
                            Some(Obj::String(s)) => match std::str::from_utf8(&*s.as_slice())
                                .expect("string is not valid utf8")
                            {
                                "chr" => match &args[0] {
                                    Some(Obj::Long(l)) => {
                                        return Some(Obj::Long(Arc::new(
                                            l.to_u8().unwrap().to_bigint().unwrap(),
                                        )));
                                    }
                                    Some(other) => {
                                        panic!(
                                            "unexpected input type of {:?} for chr",
                                            other.typ()
                                        );
                                    }
                                    None => {
                                        panic!("cannot use chr on unknown value");
                                    }
                                },
                                other => {
                                    panic!("unsupported function: {}", other);
                                }
                            },
                            other => {
                                panic!("unsupported callable: {:?}", other);
                            }
                        },
                    );

                    // We want to execute sequentially -- ignore the rest of the queue
                    // for now
                    return WalkerState::ContinueIgnoreAnalyzedInstructions;
                }
            }

            WalkerState::Continue
        },
    )?;

    // Reverse the bytecode
    let output: Vec<u8> = output.iter().rev().copied().collect();

    Ok(output)
}

use py_marshal::ObjHashable;

pub fn execute_instruction<F>(
    instr: &Instruction<TargetOpcode>,
    code: Arc<Code>,
    stack: &mut VmStack,
    vars: &mut VmVars,
    mut function_callback: F,
) where
    F: FnMut(
        Option<Obj>,
        Vec<Option<Obj>>,
        std::collections::HashMap<Option<ObjHashable>, Option<Obj>>,
    ) -> Option<Obj>,
{
    let compare_ops = [
        "<",
        "<=",
        "==",
        "!=",
        ">",
        ">=",
        "in",
        "not in",
        "is",
        "is not",
        "exception match",
        "BAD",
    ];

    match instr.opcode {
        TargetOpcode::COMPARE_OP => {
            let right = stack.pop().unwrap();
            let left = stack.pop().unwrap();

            if right.is_none() || left.is_none() {
                stack.push(None);
                return;
            }

            let left = left.unwrap();
            let right = right.unwrap();

            match compare_ops[instr.arg.unwrap() as usize] {
                "<" => match left {
                    Obj::Long(l) => match right {
                        Obj::Long(r) => stack.push(Some(Obj::Bool(l < r))),
                        other => panic!("unsupported right-hand operand: {:?}", other.typ()),
                    },
                    other => panic!("unsupported left-hand operand: {:?}", other.typ()),
                },
                "<=" => match left {
                    Obj::Long(l) => match right {
                        Obj::Long(r) => stack.push(Some(Obj::Bool(l <= r))),
                        other => panic!("unsupported right-hand operand: {:?}", other.typ()),
                    },
                    other => panic!("unsupported left-hand operand: {:?}", other.typ()),
                },
                "==" => match left {
                    Obj::Long(l) => match right {
                        Obj::Long(r) => stack.push(Some(Obj::Bool(l == r))),
                        other => panic!("unsupported right-hand operand: {:?}", other.typ()),
                    },
                    other => panic!("unsupported left-hand operand: {:?}", other.typ()),
                },
                "!=" => match left {
                    Obj::Long(l) => match right {
                        Obj::Long(r) => stack.push(Some(Obj::Bool(l != r))),
                        other => panic!("unsupported right-hand operand: {:?}", other.typ()),
                    },
                    other => panic!("unsupported left-hand operand: {:?}", other.typ()),
                },
                ">" => match left {
                    Obj::Long(l) => match right {
                        Obj::Long(r) => stack.push(Some(Obj::Bool(l > r))),
                        other => panic!("unsupported right-hand operand: {:?}", other.typ()),
                    },
                    other => panic!("unsupported left-hand operand: {:?}", other.typ()),
                },
                ">=" => match left {
                    Obj::Long(l) => match right {
                        Obj::Long(r) => stack.push(Some(Obj::Bool(l >= r))),
                        other => panic!("unsupported right-hand operand: {:?}", other.typ()),
                    },
                    other => panic!("unsupported left-hand operand: {:?}", other.typ()),
                },
                other => panic!("unsupported comparison operator: {:?}", other),
            }
        }
        TargetOpcode::IMPORT_NAME => {
            let _fromlist = stack.pop().unwrap();
            let _level = stack.pop().unwrap();

            let name = &code.names[instr.arg.unwrap() as usize];
            println!("importing: {}", name);

            stack.push(None);
        }
        TargetOpcode::LOAD_ATTR => {
            // we don't support attributes
            let _obj = stack.pop().unwrap();
            let name = &code.names[instr.arg.unwrap() as usize];
            println!("attribute name: {}", name);

            stack.push(None);
        }
        TargetOpcode::FOR_ITER => {
            // Top of stack needs to be something we can iterate over
            // get the next item from our iterator
            let top_of_stack_index = stack.len() - 1;
            let new_tos = match &mut stack[top_of_stack_index] {
                Some(Obj::String(s)) => {
                    if let Some(byte) = unsafe { Arc::get_mut_unchecked(s) }.pop() {
                        Some(Obj::Long(Arc::new(byte.to_bigint().unwrap())))
                    } else {
                        // iterator is empty -- return
                        return;
                    }
                }
                Some(other) => panic!("stack object `{:?}` is not iterable", other),
                None => None,
            };
            stack.push(new_tos)
        }
        TargetOpcode::STORE_FAST => {
            // Store TOS in a var slot
            vars.insert(instr.arg.unwrap(), stack.pop().unwrap());
        }
        TargetOpcode::LOAD_NAME => {
            stack.push(Some(Obj::String(Arc::clone(
                &code.names[instr.arg.unwrap() as usize],
            ))));
        }
        TargetOpcode::LOAD_FAST => {
            stack.push(vars[&instr.arg.unwrap()].clone());
        }
        TargetOpcode::LOAD_CONST => {
            stack.push(Some(code.consts[instr.arg.unwrap() as usize].clone()));
        }
        TargetOpcode::BINARY_XOR => {
            let tos_value = stack.pop().unwrap().map(|tos| match tos {
                Obj::Long(l) => Arc::clone(&l),
                other => panic!("did not expect type: {:?}", other.typ()),
            });
            let tos1_value = stack.pop().unwrap().map(|tos| match tos {
                Obj::Long(l) => Arc::clone(&l),
                other => panic!("did not expect type: {:?}", other.typ()),
            });

            if tos_value.is_some() && tos1_value.is_some() {
                stack.push(Some(Obj::Long(Arc::new(
                    &*tos_value.unwrap() ^ &*tos1_value.unwrap(),
                ))));
            } else {
                stack.push(None);
            }
        }
        TargetOpcode::BINARY_AND => {
            let tos_value = stack.pop().unwrap().map(|tos| match tos {
                Obj::Long(l) => Arc::clone(&l),
                other => panic!("did not expect type: {:?}", other.typ()),
            });
            let tos1_value = stack.pop().unwrap().map(|tos| match tos {
                Obj::Long(l) => Arc::clone(&l),
                other => panic!("did not expect type: {:?}", other.typ()),
            });

            if tos_value.is_some() && tos1_value.is_some() {
                stack.push(Some(Obj::Long(Arc::new(
                    &*tos_value.unwrap() & &*tos1_value.unwrap(),
                ))));
            } else {
                stack.push(None);
            }
        }
        TargetOpcode::BINARY_OR => {
            let tos_value = stack.pop().unwrap().map(|tos| match tos {
                Obj::Long(l) => Arc::clone(&l),
                other => panic!("did not expect type: {:?}", other.typ()),
            });
            let tos1_value = stack.pop().unwrap().map(|tos| match tos {
                Obj::Long(l) => Arc::clone(&l),
                other => panic!("did not expect type: {:?}", other.typ()),
            });

            if tos_value.is_some() && tos1_value.is_some() {
                stack.push(Some(Obj::Long(Arc::new(
                    &*tos_value.unwrap() | &*tos1_value.unwrap(),
                ))));
            } else {
                stack.push(None);
            }
        }
        TargetOpcode::BINARY_RSHIFT => {
            let tos_value = stack.pop().unwrap().map(|tos| match tos {
                Obj::Long(l) => Arc::clone(&l),
                other => panic!("did not expect type: {:?}", other.typ()),
            });
            let tos1_value = stack.pop().unwrap().map(|tos| match tos {
                Obj::Long(l) => Arc::clone(&l),
                other => panic!("did not expect type: {:?}", other.typ()),
            });

            if tos_value.is_some() && tos1_value.is_some() {
                stack.push(Some(Obj::Long(Arc::new(
                    &*tos1_value.unwrap() >> tos_value.unwrap().to_usize().unwrap(),
                ))));
            } else {
                stack.push(None);
            }
        }
        TargetOpcode::BINARY_LSHIFT => {
            let tos_value = stack.pop().unwrap().map(|tos| match tos {
                Obj::Long(l) => Arc::clone(&l),
                other => panic!("did not expect type: {:?}", other.typ()),
            });
            let tos1_value = stack.pop().unwrap().map(|tos| match tos {
                Obj::Long(l) => Arc::clone(&l),
                other => panic!("did not expect type: {:?}", other.typ()),
            });

            if tos_value.is_some() && tos1_value.is_some() {
                stack.push(Some(Obj::Long(Arc::new(
                    &*tos1_value.unwrap() << tos_value.unwrap().to_usize().unwrap(),
                ))));
            } else {
                stack.push(None);
            }
        }
        TargetOpcode::LIST_APPEND => {
            // We make the assumption that the list in question
            // is the final code. This may not be guaranteed
            let tos_value = stack
                .pop()
                .unwrap()
                .map(|tos| {
                    match tos {
                        Obj::Long(l) => Arc::clone(&l),
                        other => panic!("did not expect type: {:?}", other.typ()),
                    }
                    .to_u8()
                    .unwrap()
                })
                .unwrap();

            let stack_len = stack.len();
            let output = &mut stack[stack_len - instr.arg.unwrap() as usize];

            match output {
                Some(Obj::String(s)) => {
                    unsafe { Arc::get_mut_unchecked(s) }.push(tos_value);
                }
                Some(other) => panic!("unsupported LIST_APPEND operand {:?}", other.typ()),
                None => {
                    // do nothing here
                }
            }
        }
        TargetOpcode::CALL_FUNCTION => {
            assert_eq!(instr.arg.unwrap(), 1);

            let positional_args_count = instr.arg.unwrap() & 0xFF;
            let mut args = Vec::with_capacity(positional_args_count as usize);
            for _ in 0..positional_args_count {
                args.push(stack.pop().unwrap());
            }

            let kwarg_count = (instr.arg.unwrap() >> 8) & 0xFF;
            let mut kwargs = std::collections::HashMap::with_capacity(kwarg_count as usize);
            for _ in 0..kwarg_count {
                let value = stack.pop().unwrap();
                let key = stack
                    .pop()
                    .unwrap()
                    .map(|key| ObjHashable::try_from(&key).unwrap());
                kwargs.insert(key, value);
            }

            // Function code reference
            let function = stack.pop().unwrap();
            let result = function_callback(function, args, kwargs);

            stack.push(result);

            // No name resolution for now -- let's assume this is ord().
            // This function is a nop since it returns its input
            // panic!(
            //     "we're calling a function with {} args: {:#?}",
            //     instr.arg.unwrap(),
            //     stack[stack.len() - (1 + instr.arg.unwrap()) as usize]
            // );
        }
        TargetOpcode::JUMP_ABSOLUTE => {
            // Looping again. This is fine.
        }
        other => panic!("Unhandled opcode: {:?}", other),
    }
}

#[derive(Debug, Clone)]
pub enum ParsedInstr {
    Good(Rc<Instruction<TargetOpcode>>),
    Bad,
}

impl ParsedInstr {
    #[track_caller]
    pub fn unwrap(&self) -> Rc<Instruction<TargetOpcode>> {
        if let ParsedInstr::Good(ins) = self {
            Rc::clone(ins)
        } else {
            panic!("unwrap called on bad instruction")
        }
    }
}

/// Walks the bytecode in a manner that only follows what "looks like" valid
/// codepaths. This will only decode instructions that are either proven statically
/// to be taken (with `JUMP_ABSOLUTE`, `JUMP_IF_TRUE` with a const value that evaluates
/// to true, etc.)
pub fn const_jmp_instruction_walker<F>(
    bytecode: &[u8],
    consts: Arc<Vec<Obj>>,
    mut callback: F,
) -> Result<BTreeMap<u64, ParsedInstr>>
where
    F: FnMut(&Instruction<TargetOpcode>, u64) -> WalkerState,
{
    let debug = true;
    let mut rdr = Cursor::new(bytecode);
    let mut instruction_sequence = Vec::new();
    let mut analyzed_instructions = BTreeMap::<u64, ParsedInstr>::new();
    // Offset of instructions that need to be read
    let mut instruction_queue = VecDeque::<u64>::new();

    instruction_queue.push_front(0);

    macro_rules! queue {
        ($offset:expr) => {
            queue!($offset, false)
        };
        ($offset:expr, $force_queue:expr) => {
            if $offset as usize > bytecode.len() {
                panic!(
                    "bad offset queued: 0x{:X} (bufsize is 0x{:X}). Analyzed instructions: {:#?}",
                    $offset,
                    bytecode.len(),
                    analyzed_instructions
                );
            }

            if $force_queue {
                if debug {
                    trace!("adding instruction at {} to front queue", $offset);
                }
                instruction_queue.push_front($offset);
            } else if (!analyzed_instructions.contains_key(&$offset)
                && !instruction_queue.contains(&$offset))
            {
                if debug {
                    trace!("adding instruction at {} to queue", $offset);
                }
                instruction_queue.push_back($offset);
            }
        };
    };

    if debug {
        trace!("{:#?}", consts);
    }

    'decode_loop: while let Some(offset) = instruction_queue.pop_front() {
        if debug {
            trace!("offset: {}", offset);
        }

        if offset as usize == bytecode.len() {
            continue;
        }

        rdr.set_position(offset);
        // Ignore invalid instructions
        let instr = match decode_py27(&mut rdr) {
            Ok(instr) => Rc::new(instr),
            Err(e @ pydis::error::DecodeError::UnknownOpcode(_)) => {
                trace!("");
                debug!(
                    "Error decoding queued instruction at position: {}: {}",
                    offset, e
                );

                trace!(
                    "previous: {:?}",
                    instruction_sequence[instruction_sequence.len() - 1]
                );

                //remove_bad_instructions_behind_offset(offset, &mut analyzed_instructions);
                // rdr.set_position(offset);
                // let instr_size = rdr.position() - offset;
                // let mut data = vec![0u8; instr_size as usize];
                // rdr.read_exact(data.as_mut_slice())?;

                // let data_rc = Rc::new(data);
                analyzed_instructions.insert(offset, ParsedInstr::Bad);
                instruction_sequence.push(ParsedInstr::Bad);

                //queue!(rdr.position());
                continue;
            }
            Err(e) => {
                if cfg!(debug_assertions) {
                    panic!("{:?}", e);
                }
                return Err(e.into());
            }
        };
        trace!("{}", bytecode[offset as usize]);
        trace!("{:?}", instr);

        let next_instr_offset = rdr.position();

        let state = callback(&instr, offset);
        // We should stop decoding now
        if matches!(state, WalkerState::Break) {
            break;
        }

        if let WalkerState::JumpTo(offset) = &state {
            queue!(*offset, true);
            continue;
        }

        //println!("Instruction: {:X?}", instr);
        instruction_sequence.push(ParsedInstr::Good(Rc::clone(&instr)));
        analyzed_instructions.insert(offset, ParsedInstr::Good(Rc::clone(&instr)));

        let mut ignore_jump_target = false;

        if instr.opcode.is_jump() {
            if instr.opcode.is_conditional_jump() {
                let mut previous_instruction = instruction_sequence.len() - 2;
                trace!("new conditional jump: {:?}", instr);
                while let Some(ParsedInstr::Good(prev)) =
                    instruction_sequence.get(previous_instruction)
                {
                    trace!("previous: {:?}", prev);
                    // Check for potentially dead branches
                    if prev.opcode == TargetOpcode::LOAD_CONST {
                        let const_index = prev.arg.unwrap();
                        let cons = &consts[const_index as usize];
                        trace!("{:?}", cons);
                        let top_of_stack = match cons {
                            Obj::Long(num) => {
                                use num_bigint::ToBigInt;
                                *num.as_ref() == 0.to_bigint().unwrap()
                            }
                            Obj::String(s) => !s.is_empty(),
                            Obj::Tuple(t) => !t.is_empty(),
                            Obj::List(l) => !l.read().unwrap().is_empty(),
                            Obj::Set(s) => !s.read().unwrap().is_empty(),
                            Obj::None => false,
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

                        // if condition_is_met {
                        //     // We always take this branch -- decode now
                        //     let target = if instr.opcode.is_relative_jump() {
                        //         next_instr_offset + instr.arg.unwrap() as u64
                        //     } else {
                        //         instr.arg.unwrap() as u64
                        //     };
                        //     queue!(target, state.force_queue_next());
                        //     continue 'decode_loop;
                        // } else {
                        //     ignore_jump_target = true;
                        // }
                        break;
                    } else if !matches!(prev.opcode, TargetOpcode::JUMP_ABSOLUTE) {
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

                        debug!(
                            "Error while parsing target opcode: {} at position {}",
                            e, offset
                        );
                    }
                    Err(e) => {
                        return Err(e.into());
                    }
                }
            }
        }

        let ignore_jump_target = false;
        if !ignore_jump_target && instr.opcode.is_absolute_jump() {
            if instr.arg.unwrap() as usize > bytecode.len() {
                debug!("instruction {:?} at {} has a bad target", instr, offset);
                //remove_bad_instructions_behind_offset(offset, &mut analyzed_instructions);
            } else {
                queue!(instr.arg.unwrap() as u64, state.force_queue_next());
            }
        }

        if !ignore_jump_target && instr.opcode.is_relative_jump() {
            let target = next_instr_offset + instr.arg.unwrap() as u64;
            if target as usize > bytecode.len() {
                debug!("instruction {:?} at {} has a bad target", instr, offset);
                //remove_bad_instructions_behind_offset(offset, &mut analyzed_instructions);
            } else {
                queue!(target as u64);
            }
        }

        if instr.opcode != TargetOpcode::RETURN_VALUE {
            queue!(next_instr_offset, state.force_queue_next());
        }
    }

    if true || debug {
        trace!("analyzed\n{:#?}", analyzed_instructions);
    }

    Ok(analyzed_instructions)
}

fn remove_bad_instructions_behind_offset(
    offset: u64,
    analyzed_instructions: &mut BTreeMap<u64, Rc<Instruction<TargetOpcode>>>,
) {
    // We need to remove all instructions parsed between the last
    // conditional jump and this instruction
    if let Some(last_jump_offset) = analyzed_instructions
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
            trace!("removing {:?}", analyzed_instructions.get(&offset));
            analyzed_instructions.remove(&offset);
        }
    }
}
