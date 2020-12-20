use thiserror::Error;

#[derive(Error, Debug)]
pub enum Error {
    #[error("unexpected data type while processing `{0}`: {1:?}")]
    ObjectError(&'static str, py_marshal::Obj),
    #[error("error disassembling bytecode: {0}")]
    DisassemblerError(#[from] pydis::error::DecodeError),
}
