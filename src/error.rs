use std::fmt;

use num_bigint::BigInt;
use py27_marshal::Type;
use py27_marshal::bstr::BString;
use py27_marshal::read::errors::ErrorKind;
use pydis::opcode::py27::Standard;
use thiserror::Error;

/// One layer of the encrypted module format.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Stage {
    One,
    Two,
    Three,
    Four,
}

impl fmt::Display for Stage {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let number = match self {
            Self::One => 1,
            Self::Two => 2,
            Self::Three => 3,
            Self::Four => 4,
        };

        write!(f, "stage{number}")
    }
}

#[derive(Debug, Error)]
pub enum UnpackError {
    #[error("pyc is {len} bytes, shorter than its 8-byte header")]
    TruncatedHeader { len: usize },

    #[error("{stage} is not valid marshal data")]
    Marshal {
        stage: Stage,
        #[source]
        source: ErrorKind,
    },

    #[error("{stage} root object is {found:?}, not a code object")]
    NotCode { stage: Stage, found: Type },

    #[error("stage1 has {const_count} consts, so the consts[3] key is missing")]
    MissingKey { const_count: usize },

    #[error("stage1 consts[3] key is {found:?}, not a string")]
    KeyNotString { found: Type },

    #[error("{stage} payload is not UTF-8 base64 text")]
    PayloadNotText {
        stage: Stage,
        #[source]
        source: std::str::Utf8Error,
    },

    #[error("{stage} payload is not valid base64")]
    Base64 {
        stage: Stage,
        #[source]
        source: base64::DecodeError,
    },

    #[error("{stage} payload is not a valid zlib stream")]
    Zlib {
        stage: Stage,
        #[source]
        source: std::io::Error,
    },

    #[error("stage3 code has no newline before the stage4 payload")]
    MissingNewline,

    #[error("stage2 VM failed")]
    Stage2Vm {
        #[from]
        source: VmError,
    },
}

/// Failure while running the stage2 unpacker program on the small VM.
#[derive(Debug, Error)]
pub enum VmError {
    #[error("walking stage2 bytecode failed")]
    Walk {
        #[source]
        source: unfuck::error::Error<Standard>,
    },

    #[error("{opcode:?} at {offset:#x} has no argument")]
    MissingArgument { opcode: Standard, offset: u64 },

    #[error("expected {expected:?} at {offset:#x}, found {found:?}")]
    UnexpectedOpcode { offset: u64, expected: Standard, found: Standard },

    #[error("const index {index} is out of range for {len} consts")]
    ConstOutOfRange { index: usize, len: usize },

    #[error("swapmap function const {index} is {found:?}, not code")]
    SwapmapFunctionNotCode { index: usize, found: Type },

    #[error("swapmap function loads no const")]
    SwapmapNotFound,

    #[error("swapmap const {index} is {found:?}, not a dict")]
    SwapmapNotDict { index: usize, found: Type },

    #[error("swapmap has no entry for byte {byte:#04x}")]
    SwapmapMissingByte { byte: u8 },

    #[error("swapmap value for byte {byte:#04x} is {found:?}, not a long")]
    SwapmapValueNotLong { byte: u8, found: Type },

    #[error("swapmap value {value} for byte {byte:#04x} does not fit in a byte")]
    SwapmapValueOutOfRange { byte: u8, value: BigInt },

    #[error("call to unsupported function {name:?}")]
    UnsupportedCall { name: Option<BString> },

    #[error("chr argument is {found:?}, not a long")]
    ChrArgumentNotLong { found: Option<Type> },

    #[error("chr argument {value} does not fit in a byte")]
    ChrArgumentOutOfRange { value: BigInt },

    #[error("executing {opcode:?} at {offset:#x} failed")]
    Execute {
        opcode: Standard,
        offset: u64,
        #[source]
        source: unfuck::error::Error<Standard>,
    },

    #[error("stage2 bytecode ended before the unpacker loop ran")]
    VmNotReached,

    #[error("stage2 VM produced {len} table entries instead of 256")]
    TableLength { len: usize },

    #[error("stage2 VM stack holds no string output")]
    NoOutput,
}
