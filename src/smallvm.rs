use anyhow::Result;
use log::{debug, trace};
use num_bigint::ToBigInt;
use num_traits::ToPrimitive;
use py_marshal::bstr::BString;
use py_marshal::*;
use pydis::prelude::*;
use std::collections::{BTreeMap, HashMap, VecDeque};
use std::convert::TryFrom;
use std::io::{Cursor, Read};
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

use std::cell::RefCell;

/// Represents a VM variable. The value is either `Some` (something we can)
/// statically resolve or `None` (something that cannot be resolved statically)
pub type VmVar = Option<Obj>;
pub type VmVarWithTracking<T> = (VmVar, Rc<RefCell<Vec<T>>>);
pub type VmStack<T> = Vec<VmVarWithTracking<T>>;
pub type VmVars<T> = HashMap<u16, VmVarWithTracking<T>>;
pub type VmNames<T> = HashMap<Arc<BString>, VmVarWithTracking<T>>;
pub type LoadedNames = Rc<RefCell<Vec<Arc<BString>>>>;

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
        ExecuteVm(VmStack<()>, VmVars<()>, VmNames<()>, LoadedNames),
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
                                    (
                                        Some(Obj::String(Arc::clone(&output))),
                                        Rc::new(RefCell::new(vec![])),
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
                                        Rc::new(RefCell::new(vec![])),
                                    ),
                                ],
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
                State::ExecuteVm(stack, vars, names, names_loaded) => {
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
                        Rc::clone(&*names_loaded),
                        |_function, args, _kwargs| match names_loaded.borrow().last() {
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

use py_marshal::ObjHashable;

pub fn execute_instruction<F, T>(
    instr: &Instruction<TargetOpcode>,
    code: Arc<Code>,
    stack: &mut VmStack<T>,
    vars: &mut VmVars<T>,
    names: &mut VmNames<T>,
    names_loaded: LoadedNames,
    mut function_callback: F,
    access_tracking: T,
) -> Result<()>
where
    F: FnMut(VmVar, Vec<VmVar>, std::collections::HashMap<Option<ObjHashable>, VmVar>) -> VmVar,
    T: Clone + Copy,
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

    macro_rules! apply_operator {
        ($operator:tt) => {
            let (tos, tos_accesses) = stack.pop().expect("no top of stack?");
            let (tos1, tos1_accesses) = stack.pop().expect("no operand");

            tos_accesses.borrow_mut().push(access_tracking);

            let tos_accesses = Rc::new(tos_accesses.as_ref().clone());
            tos_accesses.borrow_mut().extend_from_slice(tos1_accesses.borrow().as_slice());

            let operator_str = stringify!($operator);
            match &tos1 {
                Some(Obj::Long(left)) => {
                    match &tos {
                        Some(Obj::Long(right)) => {
                            // For longs we can just use the operator outright
                            let value = left.as_ref() $operator right.as_ref();
                            stack.push((
                                Some(Obj::Long(Arc::new(
                                    value
                                ))),
                                tos_accesses,
                            ));
                        }
                        Some(Obj::Float(right)) => {
                            match operator_str {
                                "*" => {
                                    // For longs we can just use the operator outright
                                    let value = left.as_ref().to_f64().unwrap() * right;
                                    stack.push((
                                        Some(Obj::Float(
                                            value
                                        )),
                                        tos_accesses,
                                    ));
                                }
                                "/" => {
                                    // For longs we can just use the operator outright
                                    let value = left.as_ref().to_f64().unwrap() / right;
                                    stack.push((
                                        Some(Obj::Float(
                                            value
                                        )),
                                        tos_accesses,
                                    ));
                                }
                                "+" => {
                                    // For longs we can just use the operator outright
                                    let value = left.as_ref().to_f64().unwrap() / right;
                                    stack.push((
                                        Some(Obj::Float(
                                            value
                                        )),
                                        tos_accesses,
                                    ));
                                }
                                "-" => {
                                    // For longs we can just use the operator outright
                                    let value = left.as_ref().to_f64().unwrap() / right;
                                    stack.push((
                                        Some(Obj::Float(
                                            value
                                        )),
                                        tos_accesses,
                                    ));
                                }
                                _other => panic!("unsupported RHS. left: {:?}, right: {:?}. operator: {}", tos1.unwrap().typ(), "Float", operator_str),
                            }
                        }
                        Some(right)=> panic!("unsupported RHS. left: {:?}, right: {:?}. operator: {}", tos1.unwrap().typ(), right.typ(), operator_str),
                        None => stack.push((None, tos_accesses)),
                    }
                }
                Some(Obj::Float(left)) => {
                    match &tos {
                        Some(Obj::Float(right)) => {
                            match operator_str {
                                "*" => {
                                    // For longs we can just use the operator outright
                                    let value = left * right;
                                    stack.push((
                                        Some(Obj::Float(
                                            value
                                        )),
                                        tos_accesses,
                                    ));
                                }
                                "-" => {
                                    // For longs we can just use the operator outright
                                    let value = left - right;
                                    stack.push((
                                        Some(Obj::Float(
                                            value
                                        )),
                                        tos_accesses,
                                    ));
                                }
                                "+" => {
                                    // For longs we can just use the operator outright
                                    let value = left + right;
                                    stack.push((
                                        Some(Obj::Float(
                                            value
                                        )),
                                        tos_accesses,
                                    ));
                                }
                                _ => panic!("operator {:?} not handled for float", operator_str),
                            }
                        }
                        Some(Obj::String(right)) => {
                            panic!("{:?}", right);
                            return Err(crate::error::ExecutionError::ComplexExpression(instr.clone(), Some(tos1.unwrap().typ())).into());
                        }
                        Some(right)=> panic!("unsupported RHS. left: {:?}, right: {:?}. operator: {}", tos1.unwrap().typ(), right.typ(), operator_str),
                        None => stack.push((None, tos_accesses)),
                    }
                }
                Some(Obj::Set(left)) => {
                    match &tos {
                        Some(Obj::Set(right)) => {
                            match operator_str {
                                "&" => {
                                    let left_set = left.read().unwrap();
                                    let right_set = right.read().unwrap();
                                    let intersection = left_set.intersection(&right_set);

                                    stack.push((
                                        Some(Obj::Set(Arc::new(
                                            std::sync::RwLock::new(
                                            intersection.cloned().collect::<std::collections::HashSet<_>>()
                                        )
                                        ))),
                                        tos_accesses,
                                    ));
                                }
                                "|" => {
                                    let left_set = left.read().unwrap();
                                    let right_set = right.read().unwrap();
                                    let union = left_set.union(&right_set);

                                    stack.push((
                                        Some(Obj::Set(Arc::new(
                                            std::sync::RwLock::new(
                                            union.cloned().collect::<std::collections::HashSet<_>>()
                                        )
                                        ))),
                                        tos_accesses,
                                    ));
                                }
                                other => panic!("unsupported operator `{}` for {:?}", other, "set")
                            }
                        }
                        Some(right)=> panic!("unsupported RHS. left: {:?}, right: {:?}. operator: {}", tos1.unwrap().typ(), right.typ(), operator_str),
                        None => stack.push((None, tos_accesses)),
                    }
                }
                Some(Obj::String(left)) => {
                    match &tos{
                        Some(Obj::Long(right)) => {
                            match operator_str {
                                "*" => {
                                    let value = left.repeat(right.to_usize().unwrap());
                                    stack.push((
                                        Some(Obj::String(Arc::new(
                                            BString::from(value)
                                        ))),
                                        tos_accesses,
                                    ));
                                }
                                "+" => {
                                    let mut value = left.clone();
                                    unsafe { Arc::get_mut_unchecked(&mut value) }.extend_from_slice(right.to_string().as_bytes());
                                    stack.push((
                                        Some(Obj::String(value)),
                                        tos_accesses,
                                    ));
                                }
                                _other => panic!("unsupported operator {:?} for LHS {:?} RHS {:?}", operator_str, tos1.unwrap().typ(), tos.unwrap().typ())
                            }
                        }
                        Some(Obj::String(right)) => {
                            match operator_str {
                                "+" => {
                                    let mut value = left.clone();
                                    unsafe { Arc::get_mut_unchecked(&mut value) }.extend_from_slice(right.as_slice());
                                    stack.push((
                                        Some(Obj::String(value)),
                                        tos_accesses,
                                    ));
                                }
                                _other => {
                                    //return Err(crate::error::ExecutionError::ComplexExpression(instr.clone(), Some(tos1.unwrap().typ())).into());
                                    panic!("unsupported operator {:?} for LHS {:?} RHS {:?}", operator_str, tos1.unwrap().typ(), tos.unwrap().typ())
                                }
                            }
                        }
                        Some(right)=> panic!("unsupported RHS. left: {:?}, right: {:?}. operator: {}", tos1.unwrap().typ(), right.typ(), operator_str),
                        None => stack.push((None, tos_accesses)),
                    }
                }
                Some(left)=> panic!("unsupported LHS {:?} for operator {:?}", left.typ(), operator_str),
                None => {
                    stack.push((None, tos_accesses));
                }
            }
        };
    }

    use num_traits::Signed;
    macro_rules! apply_unary_operator {
        ($operator:tt) => {
            let (tos, tos_accesses) = stack.pop().expect("no top of stack?");

            tos_accesses.borrow_mut().push(access_tracking);

            let operator_str = stringify!($operator);
            match tos {
                Some(Obj::Bool(result)) => {
                    let val = match operator_str {
                        "!" => !result,
                        other => panic!("unexpected unary operator {:?} for bool", other),
                    };
                    stack.push((Some(Obj::Bool(val)), tos_accesses));
                }
                Some(Obj::Long(result)) => {
                    let val = match operator_str {
                        "!" => {
                            let truthy_value = *result != 0.to_bigint().unwrap();
                            stack.push((Some(Obj::Bool(!truthy_value)), tos_accesses));
                            return Ok(());
                        }
                        "-" => -&*result,
                        "+" => result.abs(),
                        "~" => !&*result,
                        other => panic!("unexpected unary operator {:?} for bool", other),
                    };
                    stack.push((Some(Obj::Long(Arc::new(val))), tos_accesses));
                }
                Some(other) => {
                    panic!("unexpected TOS type for condition: {:?}", other.typ());
                }
                None => {
                    stack.push((None, tos_accesses));
                }
            }
        };
    }

    match instr.opcode {
        TargetOpcode::ROT_TWO => {
            let (tos, tos_accesses) = stack.pop().unwrap();
            let (tos1, tos1_accesses) = stack.pop().unwrap();
            tos_accesses.borrow_mut().push(access_tracking);
            tos1_accesses.borrow_mut().push(access_tracking);

            stack.push((tos1, tos1_accesses));
            stack.push((tos, tos_accesses));
        }
        TargetOpcode::ROT_THREE => {
            let (tos, tos_accesses) = stack.pop().unwrap();
            let (tos1, tos1_accesses) = stack.pop().unwrap();
            let (tos2, tos2_accesses) = stack.pop().unwrap();
            tos_accesses.borrow_mut().push(access_tracking);
            tos1_accesses.borrow_mut().push(access_tracking);
            tos2_accesses.borrow_mut().push(access_tracking);

            stack.push((tos2, tos2_accesses));
            stack.push((tos1, tos1_accesses));
            stack.push((tos, tos_accesses));
        }
        TargetOpcode::DUP_TOP => {
            let (var, accesses) = stack.last().unwrap();
            accesses.borrow_mut().push(access_tracking);
            let new_var = (var.clone(), Rc::new(accesses.as_ref().clone()));
            stack.push(new_var);
        }
        TargetOpcode::COMPARE_OP => {
            let (right, right_modifying_instrs) = stack.pop().unwrap();
            let (left, left_modifying_instrs) = stack.pop().unwrap();

            left_modifying_instrs.borrow_mut().push(access_tracking);

            let left_modifying_instrs = Rc::new(left_modifying_instrs.as_ref().clone());

            left_modifying_instrs
                .borrow_mut()
                .extend_from_slice(right_modifying_instrs.borrow().as_slice());

            if right.is_none() || left.is_none() {
                stack.push((None, left_modifying_instrs));
                return Ok(());
            }

            let left = left.unwrap();
            let right = right.unwrap();

            let op = compare_ops[instr.arg.unwrap() as usize];
            match op {
                "<" => match left {
                    Obj::Long(l) => match right {
                        Obj::Long(r) => stack.push((Some(Obj::Bool(l < r)), left_modifying_instrs)),
                        other => panic!("unsupported right-hand operand: {:?}", other.typ()),
                    },
                    Obj::String(left) => match right {
                        Obj::String(right) => {
                            for idx in 0..std::cmp::min(left.len(), right.len()) {
                                if left[idx] != right[idx] {
                                    stack.push((
                                        Some(Obj::Bool(left[idx] < right[idx])),
                                        left_modifying_instrs,
                                    ));
                                    return Ok(());
                                }
                            }
                            stack.push((
                                Some(Obj::Bool(left.len() < right.len())),
                                left_modifying_instrs,
                            ))
                        }
                        _other => {
                            stack.push((Some(Obj::Bool(false)), left_modifying_instrs));
                            //     panic!(
                            //     "unsupported right-hand operand for string >: {:?}",
                            //     other.typ()
                            // )
                        }
                    },
                    other => panic!(
                        "unsupported left-hand operand: {:?} for op {}",
                        other.typ(),
                        op
                    ),
                },
                "<=" => match left {
                    Obj::Long(l) => match right {
                        Obj::Long(r) => {
                            stack.push((Some(Obj::Bool(l <= r)), left_modifying_instrs))
                        }
                        Obj::Float(r) => stack.push((
                            Some(Obj::Bool(l.to_f64().unwrap() <= r)),
                            left_modifying_instrs,
                        )),
                        other => panic!(
                            "unsupported right-hand operand for Long <=: {:?}",
                            other.typ()
                        ),
                    },
                    other => panic!(
                        "unsupported left-hand operand: {:?} for op {}",
                        other.typ(),
                        op
                    ),
                },
                "==" => match left {
                    Obj::Long(l) => match right {
                        Obj::Long(r) => {
                            stack.push((Some(Obj::Bool(l == r)), left_modifying_instrs))
                        }
                        other => panic!(
                            "unsupported right-hand operand for Long ==: {:?}",
                            other.typ()
                        ),
                    },
                    Obj::Set(left_set) => match right {
                        Obj::Set(right_set) => {
                            let left_set_lock = left_set.read().unwrap();
                            let right_set_lock = right_set.read().unwrap();
                            stack.push((
                                Some(Obj::Bool(&*left_set_lock == &*right_set_lock)),
                                left_modifying_instrs,
                            ))
                        }
                        other => panic!(
                            "unsupported right-hand operand for Set == : {:?}",
                            other.typ()
                        ),
                    },
                    other => panic!(
                        "unsupported left-hand operand: {:?} for op {}",
                        other.typ(),
                        op
                    ),
                },
                "!=" => match left {
                    Obj::Long(l) => match right {
                        Obj::Long(r) => {
                            stack.push((Some(Obj::Bool(l != r)), left_modifying_instrs))
                        }
                        other => panic!(
                            "unsupported right-hand operand for Long !=: {:?}",
                            other.typ()
                        ),
                    },
                    Obj::Set(left_set) => match right {
                        Obj::Set(right_set) => {
                            let left_set_lock = left_set.read().unwrap();
                            let right_set_lock = right_set.read().unwrap();
                            stack.push((
                                Some(Obj::Bool(&*left_set_lock != &*right_set_lock)),
                                left_modifying_instrs,
                            ))
                        }
                        other => panic!("unsupported right-hand operand for !=: {:?}", other.typ()),
                    },
                    other => panic!(
                        "unsupported left-hand operand: {:?} for op {}",
                        other.typ(),
                        op
                    ),
                },
                ">" => match left {
                    Obj::Long(l) => match right {
                        Obj::Long(r) => stack.push((Some(Obj::Bool(l > r)), left_modifying_instrs)),
                        Obj::Float(r) => stack.push((
                            Some(Obj::Bool(l.to_f64().unwrap() > r)),
                            left_modifying_instrs,
                        )),
                        other => panic!(
                            "unsupported right-hand operand for Long >: {:?}",
                            other.typ()
                        ),
                    },
                    Obj::String(left) => match right {
                        Obj::String(right) => {
                            for idx in 0..std::cmp::min(left.len(), right.len()) {
                                if left[idx] != right[idx] {
                                    stack.push((
                                        Some(Obj::Bool(left[idx] > right[idx])),
                                        left_modifying_instrs,
                                    ));
                                    return Ok(());
                                }
                            }
                            stack.push((
                                Some(Obj::Bool(left.len() > right.len())),
                                left_modifying_instrs,
                            ))
                        }
                        _other => {
                            stack.push((Some(Obj::Bool(true)), left_modifying_instrs));
                            //     panic!(
                            //     "unsupported right-hand operand for string >: {:?}",
                            //     other.typ()
                            // )
                        }
                    },
                    other => panic!(
                        "unsupported left-hand operand: {:?} for op {}",
                        other.typ(),
                        op
                    ),
                },
                ">=" => match left {
                    Obj::Long(l) => match right {
                        Obj::Long(r) => {
                            stack.push((Some(Obj::Bool(l >= r)), left_modifying_instrs))
                        }
                        Obj::Float(r) => stack.push((
                            Some(Obj::Bool(l.to_f64().unwrap() >= r)),
                            left_modifying_instrs,
                        )),
                        other => {
                            panic!("unsupported right-hand operand for Long: {:?}", other.typ())
                        }
                    },
                    other => panic!(
                        "unsupported left-hand operand: {:?} for op {}",
                        other.typ(),
                        op
                    ),
                },
                "is not" => match left {
                    Obj::String(_left) => match right {
                        Obj::None => stack.push((Some(Obj::Bool(true)), left_modifying_instrs)),
                        other => panic!(
                            "unsupported right-hand operand for string {:?}: {:?}",
                            op,
                            other.typ()
                        ),
                    },
                    other => panic!(
                        "unsupported left-hand operand: {:?} for op {}",
                        other.typ(),
                        op
                    ),
                },
                "is" => match left {
                    Obj::String(_left) => match right {
                        // all => {
                        //     return Err(crate::error::ExecutionError::ComplexExpression(
                        //         instr.clone(),
                        //         Some(all.typ()),
                        //     )
                        //     .into())
                        // }
                        // Obj::None => stack.push((Some(Obj::Bool(true)), left_modifying_instrs)),
                        other => panic!(
                            "unsupported right-hand operand for string {:?}: {:?}",
                            op,
                            other.typ()
                        ),
                    },
                    Obj::None => match right {
                        Obj::None => {
                            stack.push((Some(Obj::Bool(true)), left_modifying_instrs));
                        }
                        other => panic!(
                            "unsupported right-hand operand for None {:?}: {:?}",
                            op,
                            other.typ()
                        ),
                    },
                    other => panic!(
                        "unsupported left-hand operand: {:?} for op {}",
                        other.typ(),
                        op
                    ),
                },
                other => panic!("unsupported comparison operator: {:?}", other),
            }
        }
        TargetOpcode::IMPORT_NAME => {
            let (_fromlist, fromlist_modifying_instrs) = stack.pop().unwrap();
            let (_level, level_modifying_instrs) = stack.pop().unwrap();

            level_modifying_instrs
                .borrow_mut()
                .extend_from_slice(fromlist_modifying_instrs.borrow_mut().as_slice());
            level_modifying_instrs.borrow_mut().push(access_tracking);

            let name = &code.names[instr.arg.unwrap() as usize];
            println!("importing: {}", name);

            stack.push((None, level_modifying_instrs));
        }
        TargetOpcode::IMPORT_FROM => {
            let (_module, accessing_instrs) = stack.last().unwrap();
            accessing_instrs.borrow_mut().push(access_tracking);

            stack.push((None, Rc::clone(accessing_instrs)));
        }
        TargetOpcode::LOAD_ATTR => {
            // we don't support attributes
            let (_obj, obj_modifying_instrs) = stack.pop().unwrap();
            let _name = &code.names[instr.arg.unwrap() as usize];

            obj_modifying_instrs.borrow_mut().push(access_tracking);

            stack.push((None, obj_modifying_instrs));
        }
        TargetOpcode::FOR_ITER => {
            // Top of stack needs to be something we can iterate over
            // get the next item from our iterator
            let top_of_stack_index = stack.len() - 1;
            let (tos, _modifying_instrs) = &mut stack[top_of_stack_index];
            let new_tos = match tos {
                Some(Obj::String(s)) => {
                    if let Some(byte) = unsafe { Arc::get_mut_unchecked(s) }.pop() {
                        Some(Obj::Long(Arc::new(byte.to_bigint().unwrap())))
                    } else {
                        // iterator is empty -- return
                        return Ok(());
                    }
                }
                Some(other) => panic!("stack object `{:?}` is not iterable", other),
                None => None,
            };

            stack.push((new_tos, Rc::new(RefCell::new(vec![]))))
        }
        TargetOpcode::STORE_FAST => {
            let (tos, accessing_instrs) = stack.pop().unwrap();
            accessing_instrs.borrow_mut().push(access_tracking);
            // Store TOS in a var slot
            vars.insert(instr.arg.unwrap(), (tos, accessing_instrs));
        }
        TargetOpcode::STORE_NAME => {
            let (tos, accessing_instrs) = stack.pop().unwrap();
            let name = &code.names[instr.arg.unwrap() as usize];
            accessing_instrs.borrow_mut().push(access_tracking);
            // Store TOS in a var slot
            names.insert(Arc::clone(name), (tos, accessing_instrs));
        }
        TargetOpcode::LOAD_NAME => {
            let name = &code.names[instr.arg.unwrap() as usize];
            names_loaded.borrow_mut().push(Arc::clone(name));
            if let Some((val, accesses)) = names.get(name) {
                accesses.borrow_mut().push(access_tracking);
                stack.push((val.clone(), Rc::clone(accesses)));
            } else {
                stack.push((None, Rc::new(RefCell::new(vec![access_tracking]))));
            }
        }
        TargetOpcode::LOAD_FAST => {
            if let Some((var, accesses)) = vars.get(&instr.arg.unwrap()) {
                accesses.borrow_mut().push(access_tracking);
                stack.push((var.clone(), accesses.clone()));
            } else {
                stack.push((None, Rc::new(RefCell::new(vec![access_tracking]))));
            }
        }
        TargetOpcode::LOAD_CONST => {
            stack.push((
                Some(code.consts[instr.arg.unwrap() as usize].clone()),
                Rc::new(RefCell::new(vec![access_tracking])),
            ));
        }
        TargetOpcode::INPLACE_ADD | TargetOpcode::BINARY_ADD => {
            apply_operator!(+);
        }
        TargetOpcode::INPLACE_MULTIPLY | TargetOpcode::BINARY_MULTIPLY => {
            apply_operator!(*);
        }
        TargetOpcode::INPLACE_SUBTRACT | TargetOpcode::BINARY_SUBTRACT => {
            apply_operator!(-);
        }
        TargetOpcode::STORE_SUBSCR => {
            return Err(
                crate::error::ExecutionError::ComplexExpression(instr.clone(), None).into(),
            );
            let (_tos, _accessing_instrs) = stack.pop().unwrap();
            let (_tos1, _tos1_accessing_instrs) = stack.pop().unwrap();
            let (_tos2, _tos2_accessing_instrs) = stack.pop().unwrap();
            // accessing_instrs
            //     .borrow_mut()
            //     .extend_from_slice(tos1_accessing_instrs.borrow().as_slice());
            // accessing_instrs
            //     .borrow_mut()
            //     .extend_from_slice(tos2_accessing_instrs.borrow().as_slice());
            // accessing_instrs.borrow_mut().push(access_tracking);

            // if tos.is_none() || tos2.is_none() {
            //     match tos1 {
            //         Some(Obj::Dict(list_lock)) => {
            //             let mut dict = list_lock.write().unwrap();
            //             let key = ObjHashable::try_from(&tos).unwrap();
            //             dict.insert(key, tos2);
            //         }
            //         Some(other) => {
            //             panic!("need to implement BINARY_SUBSC for set");
            //         }
            //         None => {
            //             stack.push((None, accessing_instrs));
            //         }
            //     }
            // }
            // let tos = tos.unwrap();
            // let tos2 = tos2.unwrap();

            // match tos1 {
            //     Some(Obj::Dict(list_lock)) => {
            //         let mut dict = list_lock.write().unwrap();
            //         let key = ObjHashable::try_from(&tos).unwrap();
            //         dict.insert(key, tos2);
            //     }
            //     Some(other) => {
            //         panic!("need to implement BINARY_SUBSC for set");
            //     }
            //     None => {
            //         stack.push((None, accessing_instrs));
            //     }
            // }
        }
        TargetOpcode::BINARY_SUBSC => {
            let (tos, accessing_instrs) = stack.pop().unwrap();
            let (tos1, tos1_accessing_instrs) = stack.pop().unwrap();
            accessing_instrs
                .borrow_mut()
                .extend_from_slice(tos1_accessing_instrs.borrow().as_slice());
            accessing_instrs.borrow_mut().push(access_tracking);

            if tos.is_none() {
                stack.push((None, accessing_instrs));
                return Ok(());
            }

            match tos1 {
                Some(Obj::List(list_lock)) => {
                    let list = list_lock.read().unwrap();
                    if let Obj::Long(long) = tos.unwrap() {
                        if long.to_usize().unwrap() >= list.len() {
                            stack.push((None, accessing_instrs));
                        } else {
                            stack.push((
                                Some(list[long.to_usize().unwrap()].clone()),
                                accessing_instrs,
                            ));
                        }
                    } else {
                        panic!("TOS must be a long");
                    }
                }
                Some(other) => {
                    return Err(crate::error::ExecutionError::ComplexExpression(
                        instr.clone(),
                        Some(other.typ()),
                    )
                    .into());
                }
                None => {
                    stack.push((None, accessing_instrs));
                }
            }
        }
        TargetOpcode::BINARY_DIVIDE => {
            apply_operator!(/);
        }
        TargetOpcode::BINARY_XOR => {
            apply_operator!(^);
        }
        TargetOpcode::BINARY_AND => {
            apply_operator!(&);
        }
        TargetOpcode::BINARY_OR => {
            apply_operator!(|);
        }
        TargetOpcode::UNARY_NOT => {
            apply_unary_operator!(!);
        }
        TargetOpcode::BINARY_RSHIFT => {
            let (tos, tos_accesses) = stack.pop().unwrap();
            let tos_value = tos.map(|tos| match tos {
                Obj::Long(l) => Arc::clone(&l),
                other => panic!("did not expect type: {:?}", other.typ()),
            });
            let (tos1, tos1_accesses) = stack.pop().unwrap();
            let tos1_value = tos1.map(|tos| match tos {
                Obj::Long(l) => Arc::clone(&l),
                other => panic!("did not expect type: {:?}", other.typ()),
            });

            tos_accesses
                .borrow_mut()
                .extend_from_slice(tos1_accesses.borrow().as_slice());

            if tos_value.is_some() && tos1_value.is_some() {
                stack.push((
                    Some(Obj::Long(Arc::new(
                        &*tos1_value.unwrap() >> tos_value.unwrap().to_usize().unwrap(),
                    ))),
                    tos_accesses,
                ));
            } else {
                stack.push((None, tos_accesses));
            }
        }
        TargetOpcode::BINARY_LSHIFT => {
            let (tos, tos_accesses) = stack.pop().unwrap();
            let tos_value = tos.map(|tos| match tos {
                Obj::Long(l) => Arc::clone(&l),
                other => panic!("did not expect type: {:?}", other.typ()),
            });
            let (tos1, tos1_accesses) = stack.pop().unwrap();
            let tos1_value = tos1.map(|tos| match tos {
                Obj::Long(l) => Arc::clone(&l),
                other => panic!("did not expect type: {:?}", other.typ()),
            });

            tos_accesses
                .borrow_mut()
                .extend_from_slice(tos1_accesses.borrow().as_slice());

            if tos_value.is_some() && tos1_value.is_some() {
                stack.push((
                    Some(Obj::Long(Arc::new(
                        &*tos1_value.unwrap() << tos_value.unwrap().to_usize().unwrap(),
                    ))),
                    tos_accesses,
                ));
            } else {
                stack.push((None, tos_accesses));
            }
        }
        TargetOpcode::LIST_APPEND => {
            let (tos, tos_modifiers) = stack.pop().unwrap();
            let tos_value = tos
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
            let (output, output_modifiers) = &mut stack[stack_len - instr.arg.unwrap() as usize];

            output_modifiers
                .borrow_mut()
                .extend_from_slice(tos_modifiers.borrow().as_slice());

            output_modifiers.borrow_mut().push(access_tracking);

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
        TargetOpcode::UNPACK_SEQUENCE => {
            let (tos, tos_modifiers) = stack.pop().unwrap();

            tos_modifiers.borrow_mut().push(access_tracking);

            match tos {
                Some(Obj::Tuple(t)) => {
                    for item in t.iter().rev().take(instr.arg.unwrap() as usize) {
                        stack.push((
                            Some(item.clone()),
                            Rc::new(RefCell::new(tos_modifiers.borrow().clone())),
                        ));
                    }
                }
                Some(other) => {
                    panic!("need to add UNPACK_SEQUENCE support for {:?}", other.typ());
                }
                None => {
                    for _i in 0..instr.arg.unwrap() {
                        stack.push((None, Rc::new(RefCell::new(tos_modifiers.borrow().clone()))));
                    }
                }
            }
        }
        TargetOpcode::BUILD_SET => {
            let mut set = std::collections::HashSet::new();
            let mut push_none = false;

            let mut set_accessors = vec![];
            for _i in 0..instr.arg.unwrap() {
                let (tos, tos_modifiers) = stack.pop().unwrap();
                set_accessors.extend_from_slice(tos_modifiers.borrow().as_slice());
                // we don't build the set if we can't resolve the args
                if tos.is_none() || push_none {
                    push_none = true;
                    continue;
                }

                tos_modifiers.borrow_mut().push(access_tracking);

                set.insert(py_marshal::ObjHashable::try_from(&tos.unwrap()).unwrap());
            }

            set_accessors.push(access_tracking);

            if push_none {
                stack.push((None, Rc::new(RefCell::new(set_accessors))));
            } else {
                stack.push((
                    Some(Obj::Set(Arc::new(std::sync::RwLock::new(set)))),
                    Rc::new(RefCell::new(set_accessors)),
                ));
            }
        }
        TargetOpcode::BUILD_TUPLE => {
            let mut tuple = Vec::new();
            let mut push_none = false;

            let mut tuple_accessors = vec![];
            for _i in 0..instr.arg.unwrap() {
                let (tos, tos_modifiers) = stack.pop().unwrap();
                tuple_accessors.extend_from_slice(tos_modifiers.borrow().as_slice());
                // we don't build the set if we can't resolve the args
                if tos.is_none() || push_none {
                    push_none = true;
                    continue;
                }

                tos_modifiers.borrow_mut().push(access_tracking);

                tuple.push(tos.unwrap());
            }

            tuple_accessors.push(access_tracking);
            if push_none {
                stack.push((None, Rc::new(RefCell::new(tuple_accessors))));
            } else {
                stack.push((
                    Some(Obj::Tuple(Arc::new(tuple))),
                    Rc::new(RefCell::new(tuple_accessors)),
                ));
            }
        }
        TargetOpcode::BUILD_MAP => {
            let map = Some(Obj::Dict(Arc::new(std::sync::RwLock::new(
                std::collections::HashMap::with_capacity(instr.arg.unwrap() as usize),
            ))));

            stack.push((map, Rc::new(RefCell::new(vec![access_tracking]))));
        }
        TargetOpcode::LOAD_GLOBAL => {
            stack.push((None, Rc::new(RefCell::new(vec![access_tracking]))));
        }
        TargetOpcode::LOAD_DEREF => {
            stack.push((None, Rc::new(RefCell::new(vec![access_tracking]))));
        }
        TargetOpcode::BUILD_LIST => {
            let mut list = Vec::new();
            let mut push_none = false;

            let mut tuple_accessors = vec![];
            for _i in 0..instr.arg.unwrap() {
                let (tos, tos_modifiers) = stack.pop().unwrap();
                tuple_accessors.extend_from_slice(tos_modifiers.borrow().as_slice());
                // we don't build the set if we can't resolve the args
                if tos.is_none() {
                    push_none = true;
                    break;
                }

                tos_modifiers.borrow_mut().push(access_tracking);

                list.push(tos.unwrap());
            }
            tuple_accessors.push(access_tracking);
            if push_none {
                stack.push((None, Rc::new(RefCell::new(tuple_accessors))));
            } else {
                stack.push((
                    Some(Obj::List(Arc::new(std::sync::RwLock::new(list)))),
                    Rc::new(RefCell::new(tuple_accessors)),
                ));
            }
        }
        TargetOpcode::BUILD_CLASS => {
            let (_tos, tos_accesses) = stack.pop().unwrap();
            let (_tos1, tos1_accesses) = stack.pop().unwrap();
            let (_tos2, tos2_accesses) = stack.pop().unwrap();
            tos_accesses
                .borrow_mut()
                .extend_from_slice(tos1_accesses.borrow().as_slice());
            tos_accesses
                .borrow_mut()
                .extend_from_slice(tos2_accesses.borrow().as_slice());
            tos_accesses.borrow_mut().push(access_tracking);

            stack.push((None, tos_accesses));
        }
        TargetOpcode::MAKE_FUNCTION => {
            let (_tos, tos_modifiers) = stack.pop().unwrap();
            let tos_modifiers = Rc::new(RefCell::new(tos_modifiers.borrow().clone()));
            tos_modifiers.borrow_mut().push(access_tracking);

            stack.push((None, tos_modifiers));
        }
        TargetOpcode::POP_TOP => {
            let (_tos, tos_modifiers) = stack.pop().unwrap();
            tos_modifiers.borrow_mut().push(access_tracking);
        }
        TargetOpcode::GET_ITER => {
            // nop
        }
        TargetOpcode::CALL_FUNCTION => {
            let mut accessed_instrs = vec![];

            let kwarg_count = (instr.arg.unwrap() >> 8) & 0xFF;
            let mut kwargs = std::collections::HashMap::with_capacity(kwarg_count as usize);
            for _ in 0..kwarg_count {
                let (value, value_accesses) = stack.pop().unwrap();
                accessed_instrs.extend_from_slice(value_accesses.borrow().as_slice());

                let (key, key_accesses) = stack.pop().unwrap();
                accessed_instrs.extend_from_slice(key_accesses.borrow().as_slice());
                let key = key.map(|key| ObjHashable::try_from(&key).unwrap());
                kwargs.insert(key, value);
            }

            let positional_args_count = instr.arg.unwrap() & 0xFF;
            let mut args = Vec::with_capacity(positional_args_count as usize);
            for _ in 0..positional_args_count {
                let (arg, arg_accesses) = stack.pop().unwrap();
                accessed_instrs.extend_from_slice(arg_accesses.borrow().as_slice());
                args.push(arg);
            }

            // Function code reference
            // NOTE: we skip the function accesses here since we don't really
            // want to be tracking across functions
            let function = stack.pop().unwrap();
            let result = function_callback(function.0, args, kwargs);

            accessed_instrs.push(access_tracking);

            stack.push((result, Rc::new(RefCell::new(accessed_instrs))));

            // No name resolution for now -- let's assume this is ord().
            // This function is a nop since it returns its input
            // panic!(
            //     "we're calling a function with {} args: {:#?}",
            //     instr.arg.unwrap(),
            //     stack[stack.len() - (1 + instr.arg.unwrap()) as usize]
            // );
        }
        TargetOpcode::CALL_FUNCTION_VAR => {
            let mut accessed_instrs = vec![];

            let (_additional_positional_args, arg_accesses) = stack.pop().unwrap();
            accessed_instrs.extend_from_slice(arg_accesses.borrow().as_slice());

            let kwarg_count = (instr.arg.unwrap() >> 8) & 0xFF;
            let mut kwargs = std::collections::HashMap::with_capacity(kwarg_count as usize);
            for _ in 0..kwarg_count {
                let (value, value_accesses) = stack.pop().unwrap();
                accessed_instrs.extend_from_slice(value_accesses.borrow().as_slice());

                let (key, key_accesses) = stack.pop().unwrap();
                accessed_instrs.extend_from_slice(key_accesses.borrow().as_slice());
                let key = key.map(|key| ObjHashable::try_from(&key).unwrap());
                kwargs.insert(key, value);
            }

            let positional_args_count = instr.arg.unwrap() & 0xFF;
            let mut args = Vec::with_capacity(positional_args_count as usize);
            for _ in 0..positional_args_count {
                let (arg, arg_accesses) = stack.pop().unwrap();
                accessed_instrs.extend_from_slice(arg_accesses.borrow().as_slice());
                args.push(arg);
            }

            // Function code reference
            // NOTE: we skip the function accesses here since we don't really
            // want to be tracking across functions
            let function = stack.pop().unwrap();
            let result = function_callback(function.0, args, kwargs);

            accessed_instrs.push(access_tracking);

            stack.push((result, Rc::new(RefCell::new(accessed_instrs))));
        }
        TargetOpcode::CALL_FUNCTION_KW => {
            let mut accessed_instrs = vec![];

            let (_additional_kw_args, arg_accesses) = stack.pop().unwrap();
            accessed_instrs.extend_from_slice(arg_accesses.borrow().as_slice());

            let kwarg_count = (instr.arg.unwrap() >> 8) & 0xFF;
            let mut kwargs = std::collections::HashMap::with_capacity(kwarg_count as usize);
            for _ in 0..kwarg_count {
                let (value, value_accesses) = stack.pop().unwrap();
                accessed_instrs.extend_from_slice(value_accesses.borrow().as_slice());

                let (key, key_accesses) = stack.pop().unwrap();
                accessed_instrs.extend_from_slice(key_accesses.borrow().as_slice());
                let key = key.map(|key| ObjHashable::try_from(&key).unwrap());
                kwargs.insert(key, value);
            }

            let positional_args_count = instr.arg.unwrap() & 0xFF;
            let mut args = Vec::with_capacity(positional_args_count as usize);
            for _ in 0..positional_args_count {
                let (arg, arg_accesses) = stack.pop().unwrap();
                accessed_instrs.extend_from_slice(arg_accesses.borrow().as_slice());
                args.push(arg);
            }

            // Function code reference
            // NOTE: we skip the function accesses here since we don't really
            // want to be tracking across functions
            let function = stack.pop().unwrap();
            let result = function_callback(function.0, args, kwargs);

            accessed_instrs.push(access_tracking);

            stack.push((result, Rc::new(RefCell::new(accessed_instrs))));
        }
        TargetOpcode::CALL_FUNCTION_VAR_KW => {
            let mut accessed_instrs = vec![];

            let (_additional_kw_args, arg_accesses) = stack.pop().unwrap();
            accessed_instrs.extend_from_slice(arg_accesses.borrow().as_slice());
            let (_additional_positional_args, arg_accesses) = stack.pop().unwrap();
            accessed_instrs.extend_from_slice(arg_accesses.borrow().as_slice());

            let kwarg_count = (instr.arg.unwrap() >> 8) & 0xFF;
            let mut kwargs = std::collections::HashMap::with_capacity(kwarg_count as usize);
            for _ in 0..kwarg_count {
                let (value, value_accesses) = stack.pop().unwrap();
                accessed_instrs.extend_from_slice(value_accesses.borrow().as_slice());

                let (key, key_accesses) = stack.pop().unwrap();
                accessed_instrs.extend_from_slice(key_accesses.borrow().as_slice());
                let key = key.map(|key| ObjHashable::try_from(&key).unwrap());
                kwargs.insert(key, value);
            }

            let positional_args_count = instr.arg.unwrap() & 0xFF;
            let mut args = Vec::with_capacity(positional_args_count as usize);
            for _ in 0..positional_args_count {
                let (arg, arg_accesses) = stack.pop().unwrap();
                accessed_instrs.extend_from_slice(arg_accesses.borrow().as_slice());
                args.push(arg);
            }

            // Function code reference
            // NOTE: we skip the function accesses here since we don't really
            // want to be tracking across functions
            let function = stack.pop().unwrap();
            let result = function_callback(function.0, args, kwargs);

            accessed_instrs.push(access_tracking);

            stack.push((result, Rc::new(RefCell::new(accessed_instrs))));
        }
        TargetOpcode::JUMP_ABSOLUTE => {
            // Looping again. This is fine.
        }
        other => {
            return Err(crate::error::ExecutionError::UnsupportedOpcode(other).into());
        }
    }

    Ok(())
}

#[derive(Debug, Clone, Eq, PartialEq)]
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
                    Ok(_instr) => {
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

        if instr.opcode != TargetOpcode::RETURN_VALUE && instr.opcode != TargetOpcode::RAISE_VARARGS
        {
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

#[cfg(test)]
pub(crate) mod tests {
    use super::*;
    use num_bigint::BigInt;
    use py_marshal::bstr::BString;
    use std::rc::Rc;
    use std::sync::Arc;

    type TargetOpcode = pydis::opcode::Python27;

    #[macro_export]
    macro_rules! Long {
        ($value:expr) => {
            py_marshal::Obj::Long(Arc::new(BigInt::from($value)))
        };
    }

    #[macro_export]
    macro_rules! Instr {
        ($opcode:expr) => {
            Instruction {
                opcode: $opcode,
                arg: None,
            }
        };
        ($opcode:expr, $arg:expr) => {
            Instruction {
                opcode: $opcode,
                arg: Some($arg),
            }
        };
    }

    #[test]
    fn binary_xor() {
        let (mut stack, mut vars, mut names, names_loaded) = setup_vm_vars();
        let mut code = default_code_obj();

        let left = 0b10101010_11111111;
        let right = 0b01010101_11111111;
        let expected = left ^ right;

        let consts = vec![Long!(left), Long!(right)];

        Arc::get_mut(&mut code).unwrap().consts = Arc::new(consts);

        let instrs = [
            Instr!(TargetOpcode::LOAD_CONST, 0),
            Instr!(TargetOpcode::LOAD_CONST, 1),
            Instr!(TargetOpcode::BINARY_XOR),
        ];

        for instr in &instrs {
            execute_instruction(
                instr,
                Arc::clone(&code),
                &mut stack,
                &mut vars,
                &mut names,
                Rc::clone(&names_loaded),
                |_f, _args, _kwargs| {
                    panic!("functions should not be invoked");
                },
                (),
            )
            .expect("unexpected error")
        }

        assert_eq!(stack.len(), 1);

        match &stack[0].0 {
            Some(Obj::Long(l)) => {
                assert_eq!(*l.as_ref(), expected.to_bigint().unwrap());
            }
            Some(other) => panic!("unexpected type: {:?}", other.typ()),
            _ => panic!("unexpected None value for TOS"),
        }
    }

    #[test]
    fn binary_lshift() {
        let (mut stack, mut vars, mut names, names_loaded) = setup_vm_vars();
        let mut code = default_code_obj();

        let left = 0b10101010_11111111;
        let right = 3;
        let expected = left << right;

        let consts = vec![Long!(left), Long!(right)];

        Arc::get_mut(&mut code).unwrap().consts = Arc::new(consts);

        let instrs = [
            Instr!(TargetOpcode::LOAD_CONST, 0),
            Instr!(TargetOpcode::LOAD_CONST, 1),
            Instr!(TargetOpcode::BINARY_LSHIFT),
        ];

        for instr in &instrs {
            execute_instruction(
                instr,
                Arc::clone(&code),
                &mut stack,
                &mut vars,
                &mut names,
                Rc::clone(&names_loaded),
                |_f, _args, _kwargs| {
                    panic!("functions should not be invoked");
                },
                (),
            )
            .expect("unexpected error")
        }

        assert_eq!(stack.len(), 1);

        match &stack[0].0 {
            Some(Obj::Long(l)) => {
                assert_eq!(*l.as_ref(), expected.to_bigint().unwrap());
            }
            Some(other) => panic!("unexpected type: {:?}", other.typ()),
            _ => panic!("unexpected None value for TOS"),
        }
    }
    #[test]
    fn binary_rshift() {
        let (mut stack, mut vars, mut names, names_loaded) = setup_vm_vars();
        let mut code = default_code_obj();

        let left = 0b10101010_11111111;
        let right = 3;
        let expected = left >> right;

        let consts = vec![Long!(left), Long!(right)];

        Arc::get_mut(&mut code).unwrap().consts = Arc::new(consts);

        let instrs = [
            Instr!(TargetOpcode::LOAD_CONST, 0),
            Instr!(TargetOpcode::LOAD_CONST, 1),
            Instr!(TargetOpcode::BINARY_RSHIFT),
        ];

        for instr in &instrs {
            execute_instruction(
                instr,
                Arc::clone(&code),
                &mut stack,
                &mut vars,
                &mut names,
                Rc::clone(&names_loaded),
                |_f, _args, _kwargs| {
                    panic!("functions should not be invoked");
                },
                (),
            )
            .expect("unexpected error")
        }

        assert_eq!(stack.len(), 1);

        match &stack[0].0 {
            Some(Obj::Long(l)) => {
                assert_eq!(*l.as_ref(), expected.to_bigint().unwrap());
            }
            Some(other) => panic!("unexpected type: {:?}", other.typ()),
            _ => panic!("unexpected None value for TOS"),
        }
    }

    pub(crate) fn setup_vm_vars() -> (VmStack<()>, VmVars<()>, VmNames<()>, LoadedNames) {
        (
            VmStack::new(),
            VmVars::new(),
            VmNames::new(),
            LoadedNames::default(),
        )
    }

    pub(crate) fn default_code_obj() -> Arc<Code> {
        Arc::new(py_marshal::Code {
            argcount: 0,
            nlocals: 0,
            stacksize: 0,
            flags: CodeFlags::OPTIMIZED,
            code: Arc::new(vec![]),
            consts: Arc::new(vec![]),
            names: vec![],
            varnames: vec![],
            freevars: vec![],
            cellvars: vec![],
            filename: Arc::new(BString::from("filename")),
            name: Arc::new(BString::from("name")),
            firstlineno: 0,
            lnotab: Arc::new(vec![]),
        })
    }
}
