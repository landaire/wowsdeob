use thiserror::Error;

#[derive(Error, Debug)]
pub enum DecodingError {
    #[error("unexpected data type while processing `{0}`: {1:?}")]
    ObjectError(&'static str, py_marshal::Obj),
}