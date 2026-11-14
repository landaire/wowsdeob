//! The client's `res/scripts.zip`, served to the interpreter as module
//! bytecode.

use std::cell::RefCell;
use std::collections::HashMap;
use std::fs::File;
use std::io::Read;
use std::path::Path;
use std::path::PathBuf;

use unfuck::interp::ModuleCode;
use unfuck::interp::ModuleSource;
use zip::ZipArchive;

use crate::constants::error::ConstantsError;
use crate::module_name::ModuleName;

struct Entry {
    index: usize,
    is_package: bool,
    path: String,
}

pub struct ScriptArchive {
    archive: RefCell<ZipArchive<File>>,
    entries: HashMap<String, Entry>,
    unpacked: RefCell<HashMap<String, Vec<u8>>>,
    failures: RefCell<Vec<ConstantsError>>,
}

impl ScriptArchive {
    pub fn open(path: &Path) -> Result<Self, ConstantsError> {
        let file = File::open(path).map_err(|source| ConstantsError::Open { path: path.to_path_buf(), source })?;
        let archive =
            ZipArchive::new(file).map_err(|source| ConstantsError::Archive { path: path.to_path_buf(), source })?;

        let mut entries = HashMap::new();
        for index in 0..archive.len() {
            let Some(entry_path) = archive.name_for_index(index) else {
                continue;
            };
            let Some(name) = ModuleName::from_zip_path(entry_path) else {
                continue;
            };
            let entry = Entry { index, is_package: name.is_package(), path: entry_path.to_owned() };
            entries.insert(name.as_str().to_owned(), entry);
        }

        Ok(Self {
            archive: RefCell::new(archive),
            entries,
            unpacked: RefCell::new(HashMap::new()),
            failures: RefCell::new(Vec::new()),
        })
    }

    /// Errors from modules that exist in the archive but could not be
    /// unpacked. The interpreter treats such a module as absent, so the
    /// caller must reject the run when this is not empty.
    pub fn take_failures(&self) -> Vec<ConstantsError> {
        std::mem::take(&mut *self.failures.borrow_mut())
    }

    fn unpack(&self, name: &str, entry: &Entry) -> Result<Vec<u8>, ConstantsError> {
        // A client module is well under this. The declared size only sizes
        // the first allocation; reading stops at the real end of the entry.
        const MAX_PREALLOCATION: u64 = 16 << 20;

        let mut archive = self.archive.borrow_mut();
        let path = PathBuf::from(&entry.path);
        let mut file =
            archive.by_index(entry.index).map_err(|source| ConstantsError::Archive { path: path.clone(), source })?;

        let preallocation = usize::try_from(file.size().min(MAX_PREALLOCATION)).unwrap_or(0);
        let mut pyc = Vec::with_capacity(preallocation);
        file.read_to_end(&mut pyc).map_err(|source| ConstantsError::Open { path, source })?;

        let module =
            crate::unpack_module(&pyc).map_err(|source| ConstantsError::Unpack { module: name.to_owned(), source })?;

        Ok(module.code_bytes().to_vec())
    }
}

impl ModuleSource for ScriptArchive {
    fn find(&self, name: &str) -> Option<ModuleCode> {
        let entry = self.entries.get(name)?;

        if let Some(code) = self.unpacked.borrow().get(name) {
            return Some(ModuleCode { code: code.clone(), is_package: entry.is_package, filename: entry.path.clone() });
        }

        match self.unpack(name, entry) {
            Ok(code) => {
                self.unpacked.borrow_mut().insert(name.to_owned(), code.clone());
                Some(ModuleCode { code, is_package: entry.is_package, filename: entry.path.clone() })
            }
            Err(error) => {
                self.failures.borrow_mut().push(error);
                None
            }
        }
    }
}
