use std::path::PathBuf;

use thiserror::Error;

use crate::UnpackError;
use crate::constants::game::BuildNumber;

#[derive(Debug, Error)]
pub enum ConstantsError {
    #[error("no game build under {path} has res/scripts.zip")]
    NoBuild { path: PathBuf },

    #[error("build {build} has no scripts archive at {path}")]
    MissingScripts { build: BuildNumber, path: PathBuf },

    #[error("{path} has no CPython built-in module table; it may not be a World of Warships client")]
    NoModuleTable { path: PathBuf },

    #[error("failed to open {path}")]
    Open {
        path: PathBuf,
        #[source]
        source: std::io::Error,
    },

    #[error("failed to read scripts archive {path}")]
    Archive {
        path: PathBuf,
        #[source]
        source: zip::result::ZipError,
    },

    #[error("failed to unpack client module {module}")]
    Unpack {
        module: String,
        #[source]
        source: UnpackError,
    },

    #[error("the Python interpreter failed to start: {detail}")]
    Bootstrap { detail: String },

    #[error("failed to start the interpreter thread")]
    Thread {
        #[source]
        source: std::io::Error,
    },

    #[error("{key}: evaluating {expression} failed: {detail}")]
    Evaluation { key: &'static str, expression: String, detail: String },

    #[error("{key}: the value at {path} depends on native client code the interpreter does not emulate ({origin})")]
    Unknown { key: &'static str, path: String, origin: String },

    #[error("{key}: the value at {path} has type {type_name}, which has no JSON form")]
    Unserializable { key: &'static str, path: String, type_name: String },

    #[error("{key}: the value at {path} contains itself")]
    Circular { key: &'static str, path: String },

    #[error("the scripts of build {expected} report no VERSION.BUILD build number")]
    MissingBuild { expected: BuildNumber },

    #[error("the scripts of build {expected} report build {found}")]
    BuildMismatch { expected: BuildNumber, found: BuildNumber },
}
