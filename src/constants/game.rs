//! Locating a build's files in a game installation.

use std::fmt;
use std::path::Path;
use std::path::PathBuf;

use crate::constants::error::ConstantsError;

/// A client build number, the name of its `bin/<build>` directory.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct BuildNumber(u32);

impl BuildNumber {
    pub fn new(build: u32) -> Self {
        Self(build)
    }

    pub fn get(self) -> u32 {
        self.0
    }
}

impl fmt::Display for BuildNumber {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}", self.0)
    }
}

/// The files of one game build the extractor reads.
#[derive(Debug, Clone)]
pub struct ClientBuild {
    build: BuildNumber,
    /// `bin/<build>/res/scripts.zip`.
    scripts: PathBuf,
    /// The client executable. Without it, every module the scripts import
    /// but do not contain is assumed to be linked into the client, and the
    /// constants of current clients then depend on modules nothing emulates.
    executable: Option<PathBuf>,
}

impl ClientBuild {
    /// A build whose files are not laid out as an installation, such as a
    /// scripts archive fetched on its own.
    pub fn new(build: BuildNumber, scripts: PathBuf, executable: Option<PathBuf>) -> Self {
        Self { build, scripts, executable }
    }

    /// The files of `build`, or of the newest build under `bin/` that has
    /// client scripts.
    pub fn find(game_dir: &Path, build: Option<BuildNumber>) -> Result<Self, ConstantsError> {
        if let Some(build) = build {
            let found = Self::installed(game_dir, build);
            if !found.scripts.is_file() {
                return Err(ConstantsError::MissingScripts { build, path: found.scripts });
            }

            return Ok(found);
        }

        let bin = game_dir.join("bin");
        let entries = std::fs::read_dir(&bin).map_err(|source| ConstantsError::Open { path: bin.clone(), source })?;

        let mut builds = Vec::new();
        for entry in entries {
            let entry = entry.map_err(|source| ConstantsError::Open { path: bin.clone(), source })?;
            if let Some(build) = entry.file_name().to_str().and_then(|name| name.parse::<u32>().ok()) {
                builds.push(BuildNumber(build));
            }
        }

        builds.sort_unstable();

        builds
            .into_iter()
            .rev()
            .map(|build| Self::installed(game_dir, build))
            .find(|found| found.scripts.is_file())
            .ok_or(ConstantsError::NoBuild { path: game_dir.to_path_buf() })
    }

    /// Only the 64-bit client is read: the module table lookup follows
    /// PE32+ pointers.
    fn installed(game_dir: &Path, build: BuildNumber) -> Self {
        let directory = game_dir.join("bin").join(build.to_string());
        let executable = Some(directory.join("bin64").join("WorldOfWarships64.exe")).filter(|path| path.is_file());

        Self { build, scripts: directory.join("res").join("scripts.zip"), executable }
    }

    pub fn build(&self) -> BuildNumber {
        self.build
    }

    pub fn scripts(&self) -> &Path {
        &self.scripts
    }

    pub fn executable(&self) -> Option<&Path> {
        self.executable.as_deref()
    }
}
