use anyhow::Result;
use log::{debug, trace};
use num_bigint::ToBigInt;
use num_traits::{Pow, ToPrimitive};
use py27_marshal::bstr::BString;
use py27_marshal::*;
use pydis::prelude::*;
use std::collections::{BTreeMap, HashMap, VecDeque};
use std::convert::TryFrom;
use std::io::{Cursor, Read};
use std::sync::{Arc, Mutex};
use unfuck::smallvm::*;
type TargetOpcode = pydis::opcode::py27::Standard;

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
        ExecuteVm(
            VmStack<()>,
            VmVars<()>,
            // names
            VmNames<()>,
            // globals
            VmNames<()>,
            LoadedNames,
        ),
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
                        if let py27_marshal::Obj::Code(function_code) = function_const {
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
                                    (
                                        Some(Obj::String(Arc::clone(&output))),
                                        InstructionTracker::new(),
                                    ),
                                    (
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
                                        InstructionTracker::new(),
                                    ),
                                ],
                                HashMap::new(),
                                HashMap::new(),
                                HashMap::new(),
                                Default::default(),
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
                State::ExecuteVm(stack, vars, names, globals, names_loaded) => {
                    // Check if our bytecode has been drained. This should be index 0 on the satck
                    if let (Some(Obj::String(s)), _modifying_instrs) = &stack[1] {
                        if s.is_empty() && instr.opcode == TargetOpcode::FOR_ITER {
                            return WalkerState::Break;
                        }
                    }

                    execute_instruction(
                        &instr,
                        Arc::clone(&code),
                        stack,
                        vars,
                        names,
                        globals,
                        Arc::clone(&*names_loaded),
                        |_function, args, _kwargs| match names_loaded.lock().unwrap().last() {
                            Some(s) => match std::str::from_utf8(&*s.as_slice())
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
                        (), // we don't care about tracking offsets
                    )
                    .expect("error executing stage2");

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
