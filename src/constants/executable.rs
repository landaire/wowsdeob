//! The client executable, which statically links CPython and the engine's
//! native modules. Its built-in module table and strings tell the
//! interpreter which modules exist and what `sys` and `_ssl` report.

mod image;

use std::cell::RefCell;
use std::collections::BTreeSet;
use std::collections::HashMap;
use std::path::Path;

use memchr::memmem;
use unfuck::interp::HostFacts;
use unfuck::interp::OpensslDefaultPaths;
use unfuck::interp::OpensslVersion;

use crate::constants::error::ConstantsError;
use crate::constants::executable::image::Image;

pub struct ClientExecutable {
    image: Vec<u8>,
    /// The names in CPython's static built-in module table.
    builtin_modules: BTreeSet<String>,
    engine_answers: RefCell<HashMap<String, bool>>,
}

impl ClientExecutable {
    pub fn open(path: &Path) -> Result<Self, ConstantsError> {
        let image = std::fs::read(path).map_err(|source| ConstantsError::Open { path: path.to_path_buf(), source })?;
        let Some(builtin_modules) = Image::parse(&image).and_then(|parsed| parsed.builtin_module_table()) else {
            return Err(ConstantsError::NoModuleTable { path: path.to_path_buf() });
        };

        Ok(Self { image, builtin_modules, engine_answers: RefCell::new(HashMap::new()) })
    }

    /// Whether the client links in the module `name`. CPython's own
    /// extension modules are exactly those in its built-in module table.
    /// The engine registers its modules (`BigWorld`, `Sound.*`, ...) by
    /// name at startup without a table, so for other names a NUL-delimited
    /// copy of the name in the image is taken as its registration.
    pub fn links_module(&self, name: &str) -> bool {
        if self.builtin_modules.contains(name) {
            return true;
        }
        if let Some(answer) = self.engine_answers.borrow().get(name) {
            return *answer;
        }

        let answer = self.find_string(name.as_bytes()).is_some();
        self.engine_answers.borrow_mut().insert(name.to_owned(), answer);

        answer
    }

    /// The facts the image fixes at build time. Facts of the machine the
    /// client runs on (its time zone) stay unknown.
    pub fn host_facts(&self) -> HostFacts {
        HostFacts {
            sys_version: self.sys_version(),
            openssl: self.openssl_version(),
            openssl_default_paths: self.openssl_default_paths(),
            ..HostFacts::default()
        }
    }

    /// `Py_GetVersion()`: `"%.80s (%.80s) %.80s"` of `PY_VERSION`,
    /// `Py_GetBuildInfo()` and `Py_GetCompiler()`. The build info format
    /// `"%s%s%s, %.20s, %.9s"` is followed by its `__DATE__` and `__TIME__`
    /// arguments. A build without Mercurial ids reports the identifier
    /// `default` and an empty revision, and the image holds no revision.
    fn sys_version(&self) -> Option<String> {
        let version_format = self.find_string(b"%.80s (%.80s) %.80s")?;
        let (_, version) = self.next_string(version_format)?;

        let build_format = self.find_string(b"%s%s%s, %.20s, %.9s")?;
        let (date_offset, date) = self.next_string(build_format)?;
        let (_, time) = self.next_string(date_offset)?;

        let compiler = self.compiler()?;

        Some(format!("{version} (default, {date}, {time}) {compiler}"))
    }

    fn compiler(&self) -> Option<String> {
        let start = memmem::find(&self.image, b"[MSC v.")?;
        let length = self.image.get(start..)?.iter().position(|byte| *byte == 0)?;

        String::from_utf8(self.image.get(start..start + length)?.to_vec()).ok()
    }

    /// `OPENSSL_VERSION_TEXT`, such as `OpenSSL 1.1.1l  24 Aug 2021`, and the
    /// version number it spells.
    fn openssl_version(&self) -> Option<OpensslVersion> {
        let start = memmem::find(&self.image, b"\0OpenSSL ")? + 1;
        let length = self.image.get(start..)?.iter().position(|byte| *byte == 0)?;
        let text = String::from_utf8(self.image.get(start..start + length)?.to_vec()).ok()?;

        let number = openssl_version_number(&text)?;

        Some(OpensslVersion { number, text })
    }

    /// `X509_CERT_FILE` and `X509_CERT_DIR`: `OPENSSLDIR "/cert.pem"` and
    /// `OPENSSLDIR "/certs"`. Both must be present in the image.
    fn openssl_default_paths(&self) -> Option<OpensslDefaultPaths> {
        let marker = b"OPENSSLDIR: \"";
        let start = memmem::find(&self.image, marker)? + marker.len();
        let length = self.image.get(start..)?.iter().position(|byte| *byte == b'"')?;
        let directory = String::from_utf8(self.image.get(start..start + length)?.to_vec()).ok()?;

        let cert_file = format!("{directory}/cert.pem");
        let cert_dir = format!("{directory}/certs");
        self.find_string(cert_file.as_bytes())?;
        self.find_string(cert_dir.as_bytes())?;

        Some(OpensslDefaultPaths { cert_file, cert_dir })
    }

    /// Offset of `text` stored as a NUL-delimited string.
    fn find_string(&self, text: &[u8]) -> Option<usize> {
        let mut needle = Vec::with_capacity(text.len() + 2);
        needle.push(0);
        needle.extend_from_slice(text);
        needle.push(0);

        memmem::find(&self.image, &needle).map(|offset| offset + 1)
    }

    /// The string after the one at `offset`, skipping the NUL padding the
    /// compiler aligns string literals with, and where it starts.
    fn next_string(&self, offset: usize) -> Option<(usize, String)> {
        let tail = self.image.get(offset..)?;
        let end = tail.iter().position(|byte| *byte == 0)?;
        let next = end + tail.get(end..)?.iter().position(|byte| *byte != 0)?;
        let length = tail.get(next..)?.iter().position(|byte| *byte == 0)?;
        let text = String::from_utf8(tail.get(next..next + length)?.to_vec()).ok()?;

        Some((offset + next, text))
    }
}

/// `0xMNNFFPPS` for `OpenSSL M.NN.FFP`: `P` is the patch letter (`a` is 1)
/// and `S` is `f` for a release.
fn openssl_version_number(text: &str) -> Option<u32> {
    let version = text.strip_prefix("OpenSSL ")?.split(' ').next()?;
    let mut parts = version.splitn(3, '.');
    let major: u32 = parts.next()?.parse().ok()?;
    let minor: u32 = parts.next()?.parse().ok()?;
    let fix_and_patch = parts.next()?;

    let digits = fix_and_patch.trim_end_matches(|character: char| character.is_ascii_lowercase());
    let fix: u32 = digits.parse().ok()?;
    let patch = match &fix_and_patch[digits.len()..] {
        "" => 0,
        letter if letter.len() == 1 => u32::from(letter.as_bytes()[0] - b'a' + 1),
        _ => return None,
    };

    Some((major << 28) | (minor << 20) | (fix << 12) | (patch << 4) | 0xf)
}

#[cfg(test)]
mod tests {
    use super::openssl_version_number;

    #[test]
    fn openssl_numbers_follow_the_header_encoding() {
        assert_eq!(openssl_version_number("OpenSSL 1.1.1l  24 Aug 2021"), Some(0x1010_10cf));
        assert_eq!(openssl_version_number("OpenSSL 1.0.2h  3 May 2016"), Some(0x1000_208f));
    }
}
