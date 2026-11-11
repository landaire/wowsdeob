use std::collections::HashMap;
use std::collections::VecDeque;
use std::sync::Arc;
use std::sync::RwLock;

use log::trace;
use num_bigint::BigInt;
use num_traits::ToPrimitive;
use py27_marshal::Code;
use py27_marshal::Obj;
use py27_marshal::ObjHashable;
use py27_marshal::bstr::BString;
use pydis::opcode::Instruction;
use pydis::opcode::py27::Standard;
use unfuck::smallvm::InstructionTracker;
use unfuck::smallvm::LoadedNames;
use unfuck::smallvm::VmFrame;
use unfuck::smallvm::VmNames;
use unfuck::smallvm::VmStack;
use unfuck::smallvm::VmVar;
use unfuck::smallvm::VmVars;
use unfuck::smallvm::WalkerState;
use unfuck::smallvm::const_jmp_instruction_walker;

use crate::error::VmError;
use crate::lock::lock_mutex;
use crate::lock::read_lock;

#[derive(Clone)]
enum State {
    FindXorStart {
        make_functions_found: usize,
        function_index: u16,
    },
    FindSwapMap {
        remaining: VecDeque<Standard>,
        function_index: u16,
    },
    AssertInstructionSequence {
        remaining: VecDeque<Standard>,
        next: Box<State>,
    },
    ExecuteVm {
        stack: VmStack<()>,
        vars: VmVars<()>,
        names: VmNames<()>,
        globals: VmNames<()>,
        names_loaded: LoadedNames,
    },
}

/// Runs the stage2 unpacker program `code` over the `co_code` of `outer_code` and
/// returns the unpacked stage3 bytes.
pub(crate) fn exec_stage2(code: Arc<Code>, outer_code: Arc<Code>) -> Result<Vec<u8>, VmError> {
    let mut state = State::FindXorStart { make_functions_found: 0, function_index: 0 };
    let mut original_code = Vec::clone(&outer_code.code);
    let mut failure = None;

    const_jmp_instruction_walker(
        code.code.as_slice(),
        Arc::clone(&code.consts),
        |instr: &Instruction<Standard>, offset| {
            trace!("Instruction at {offset}: {instr:?}");
            match step(&mut state, &mut original_code, &code, instr, offset) {
                Ok(walker_state) => walker_state,
                Err(e) => {
                    failure = Some(e);
                    WalkerState::Break
                }
            }
        },
    )
    .map_err(|source| VmError::Walk { source })?;

    if let Some(e) = failure {
        return Err(e);
    }

    let State::ExecuteVm { stack, .. } = &state else {
        return Err(VmError::VmNotReached);
    };
    let table = largest_string(stack)?;
    let table = <[u8; 256]>::try_from(table).map_err(|table| VmError::TableLength { len: table.len() })?;

    // The unpacker consumes the payload reversed.
    let stage3 = original_code.iter().rev().map(|byte| table[usize::from(*byte)]).collect();

    Ok(stage3)
}

fn step(
    state: &mut State,
    original_code: &mut [u8],
    code: &Arc<Code>,
    instr: &Instruction<Standard>,
    offset: u64,
) -> Result<WalkerState, VmError> {
    match state {
        State::FindXorStart { make_functions_found, function_index } => {
            if instr.opcode == Standard::LOAD_CONST {
                *function_index = argument(instr, offset)?;
            }
            if instr.opcode == Standard::MAKE_FUNCTION {
                *make_functions_found += 1;
            }

            // The instructions after the third function invoke the swapmap function.
            if *make_functions_found == 3 {
                *state = State::FindSwapMap {
                    remaining: VecDeque::from([
                        Standard::STORE_FAST,
                        Standard::BUILD_LIST,
                        Standard::BUILD_LIST,
                        Standard::LOAD_FAST,
                        Standard::LOAD_FAST,
                        Standard::CALL_FUNCTION,
                    ]),
                    function_index: *function_index,
                };

                return Ok(WalkerState::ContinueIgnoreAnalyzedInstructions);
            }

            Ok(WalkerState::Continue)
        }
        State::FindSwapMap { remaining, function_index } => {
            expect_opcode(remaining, instr, offset)?;

            // The final CALL_FUNCTION invokes the swapmap function.
            if remaining.is_empty() {
                apply_swapmap(code, *function_index, original_code)?;

                // The unpacker loop transforms each byte on its own, so running it once
                // over every byte value yields a lookup table for the whole payload.
                // unfuck's FOR_ITER consumes a string from the front, so table index
                // and output position agree.
                let input: Vec<u8> = (0..=u8::MAX).collect();
                let output = BString::from(Vec::with_capacity(input.len()));
                let stack = vec![
                    (Some(Obj::String(Arc::new(RwLock::new(output)))), InstructionTracker::new()),
                    (Some(Obj::String(Arc::new(RwLock::new(BString::from(input))))), InstructionTracker::new()),
                ];

                // The FOR_ITER loop is skipped; the instructions after it run the VM.
                *state = State::AssertInstructionSequence {
                    remaining: VecDeque::from([Standard::GET_ITER, Standard::FOR_ITER, Standard::GET_ITER]),
                    next: Box::new(State::ExecuteVm {
                        stack,
                        vars: HashMap::new(),
                        names: HashMap::new(),
                        globals: HashMap::new(),
                        names_loaded: LoadedNames::default(),
                    }),
                };
            }

            Ok(WalkerState::ContinueIgnoreAnalyzedInstructions)
        }
        State::AssertInstructionSequence { remaining, next } => {
            expect_opcode(remaining, instr, offset)?;

            if remaining.is_empty() {
                let next = State::clone(next);
                *state = next;
            }

            if instr.opcode == Standard::FOR_ITER {
                let delta = argument(instr, offset)?;
                return Ok(WalkerState::JumpTo(offset + 3 + u64::from(delta)));
            }

            Ok(WalkerState::ContinueIgnoreAnalyzedInstructions)
        }
        State::ExecuteVm { stack, vars, names, globals, names_loaded } => {
            // The input string at stack[1] is drained once the unpacker loop finishes.
            if let Some((Some(Obj::String(input)), _)) = stack.get(1)
                && read_lock(input).is_empty()
                && instr.opcode == Standard::FOR_ITER
            {
                return Ok(WalkerState::Break);
            }

            let mut call_error = None;
            let mut frame = VmFrame {
                code: Arc::clone(code),
                stack,
                vars,
                names,
                globals,
                names_loaded: Arc::clone(names_loaded),
                access_tracking: (),
            };
            let executed = frame.execute(instr, |_function, args, _kwargs| match call_builtin(names_loaded, &args) {
                Ok(value) => value,
                Err(e) => {
                    call_error = Some(e);
                    None
                }
            });

            if let Some(e) = call_error {
                return Err(e);
            }
            executed.map_err(|source| VmError::Execute { opcode: instr.opcode, offset, source })?;

            // Execute sequentially rather than following queued branches.
            Ok(WalkerState::ContinueIgnoreAnalyzedInstructions)
        }
    }
}

fn argument(instr: &Instruction<Standard>, offset: u64) -> Result<u16, VmError> {
    instr.arg.ok_or(VmError::MissingArgument { opcode: instr.opcode, offset })
}

fn expect_opcode(
    remaining: &mut VecDeque<Standard>,
    instr: &Instruction<Standard>,
    offset: u64,
) -> Result<(), VmError> {
    match remaining.pop_front() {
        Some(expected) if expected == instr.opcode => Ok(()),
        Some(expected) => Err(VmError::UnexpectedOpcode { offset, expected, found: instr.opcode }),
        // Callers leave this state as soon as the sequence is empty.
        None => Ok(()),
    }
}

/// Finds the swapmap dict loaded by the function at `consts[function_index]` and
/// maps every byte of `original_code` through it.
fn apply_swapmap(code: &Code, function_index: u16, original_code: &mut [u8]) -> Result<(), VmError> {
    let index = usize::from(function_index);
    let Some(function_const) = code.consts.get(index) else {
        return Err(VmError::ConstOutOfRange { index, len: code.consts.len() });
    };
    let Obj::Code(function_code) = function_const else {
        return Err(VmError::SwapmapFunctionNotCode { index, found: function_const.typ() });
    };
    let function_code = read_lock(function_code);

    // The swapmap is the first const the function loads.
    let mut swapmap_index = None;
    const_jmp_instruction_walker(
        function_code.code.as_slice(),
        Arc::clone(&function_code.consts),
        |instr: &Instruction<Standard>, offset| {
            if instr.opcode != Standard::LOAD_CONST {
                return WalkerState::Continue;
            }

            swapmap_index = Some(argument(instr, offset).map(usize::from));
            WalkerState::Break
        },
    )
    .map_err(|source| VmError::Walk { source })?;
    let Some(swapmap_index) = swapmap_index else {
        return Err(VmError::SwapmapNotFound);
    };
    let swapmap_index = swapmap_index?;

    let Some(swapmap_const) = function_code.consts.get(swapmap_index) else {
        return Err(VmError::ConstOutOfRange { index: swapmap_index, len: function_code.consts.len() });
    };
    let Obj::Dict(swapmap) = swapmap_const else {
        return Err(VmError::SwapmapNotDict { index: swapmap_index, found: swapmap_const.typ() });
    };
    let swapmap = read_lock(swapmap);

    let mut resolved: [Option<u8>; 256] = [None; 256];
    for byte in original_code {
        let slot = &mut resolved[usize::from(*byte)];
        if let Some(swapped) = *slot {
            *byte = swapped;
            continue;
        }

        let key = ObjHashable::Long(Arc::new(BigInt::from(*byte)));
        let Some(value) = swapmap.get(&key) else {
            return Err(VmError::SwapmapMissingByte { byte: *byte });
        };
        let Obj::Long(value) = value else {
            return Err(VmError::SwapmapValueNotLong { byte: *byte, found: value.typ() });
        };

        let value = read_lock(value);
        let Some(swapped) = value.to_u8() else {
            return Err(VmError::SwapmapValueOutOfRange { byte: *byte, value: value.clone() });
        };
        *slot = Some(swapped);
        *byte = swapped;
    }

    Ok(())
}

/// Resolves a call made by the unpacker program. Only `chr` is used, and it is
/// modeled as returning its byte-sized argument.
fn call_builtin(names_loaded: &LoadedNames, args: &[VmVar]) -> Result<VmVar, VmError> {
    {
        let names = lock_mutex(names_loaded);
        let Some(name) = names.last() else {
            return Err(VmError::UnsupportedCall { name: None });
        };
        if name.as_slice() != b"chr" {
            return Err(VmError::UnsupportedCall { name: Some(BString::clone(name)) });
        }
    }

    let Some(Some(argument)) = args.first() else {
        return Err(VmError::ChrArgumentNotLong { found: None });
    };
    let Obj::Long(value) = argument else {
        return Err(VmError::ChrArgumentNotLong { found: Some(argument.typ()) });
    };

    let value = read_lock(value);
    let Some(byte) = value.to_u8() else {
        return Err(VmError::ChrArgumentOutOfRange { value: value.clone() });
    };

    Ok(Some(Obj::Long(Arc::new(RwLock::new(BigInt::from(byte))))))
}

/// The unpacked output is the longest string left on the VM stack. Ties go to the
/// lowest stack slot.
fn largest_string(stack: &VmStack<()>) -> Result<Vec<u8>, VmError> {
    trace!("Final stack size: {}", stack.len());

    let mut best: Option<(&RwLock<BString>, usize)> = None;
    for (obj, _) in stack {
        let Some(Obj::String(string)) = obj else {
            continue;
        };

        let len = read_lock(string).len();
        if best.is_none_or(|(_, best_len)| len > best_len) {
            best = Some((&**string, len));
        }
    }

    let Some((string, _)) = best else {
        return Err(VmError::NoOutput);
    };

    Ok(read_lock(string).to_vec())
}
