use std::io::Read;
use std::sync::Arc;
use std::sync::PoisonError;

use flate2::read::ZlibDecoder;
use log::debug;
use py27_marshal::Code;
use py27_marshal::Obj;

use crate::error::Stage;
use crate::error::UnpackError;
use crate::lock::read_lock;
use crate::pyc::PycHeader;
use crate::smallvm;

/// The outer layer of a `.pyc` file, classified by whether its code is encrypted.
pub enum Stage1<'a> {
    Plain(PlainModule<'a>),
    Encrypted(Stage2),
}

impl<'a> Stage1<'a> {
    /// Parses a whole `.pyc` file. Encrypted modules (`co_filename == "Lesta"`) have
    /// their stage2 payload decrypted from `co_code` with the `consts[3]` key.
    pub fn parse(pyc: &'a [u8]) -> Result<Self, UnpackError> {
        let (header, body) = PycHeader::parse(pyc)?;
        debug!("Magic: {:#X}", header.magic.0);
        debug!("Mod Date: {:#X}", header.moddate.0);

        let code = load_code(body, Stage::One)?;
        debug!("Internal file name: {}", code.filename);

        if code.filename.as_slice() != b"Lesta" {
            return Ok(Self::Plain(PlainModule { header, body, code }));
        }

        let encoded = {
            let Some(key) = code.consts.get(3) else {
                return Err(UnpackError::MissingKey { const_count: code.consts.len() });
            };
            let Obj::String(key) = key else {
                return Err(UnpackError::KeyNotString { found: key.typ() });
            };

            let key = read_lock(key);
            key.iter()
                .zip(code.code.iter().cycle())
                .map(|(key_byte, code_byte)| key_byte ^ code_byte)
                .collect::<Vec<u8>>()
        };
        let bytes = unpack_b64_compressed_data(&encoded, Stage::One)?;

        Ok(Self::Encrypted(Stage2 { header, stage1_code: Arc::new(code), bytes }))
    }

    pub fn header(&self) -> PycHeader {
        match self {
            Self::Plain(plain) => plain.header,
            Self::Encrypted(stage2) => stage2.header,
        }
    }

    /// The marshalled code object one layer below the `.pyc` header: the decrypted
    /// stage2 program for encrypted modules, or the module body for plain ones.
    pub fn payload(&self) -> &[u8] {
        match self {
            Self::Plain(plain) => plain.body,
            Self::Encrypted(stage2) => &stage2.bytes,
        }
    }
}

/// A module whose stage1 code object is the module itself.
pub struct PlainModule<'a> {
    header: PycHeader,
    body: &'a [u8],
    code: Code,
}

impl PlainModule<'_> {
    pub fn header(&self) -> PycHeader {
        self.header
    }

    pub fn body(&self) -> &[u8] {
        self.body
    }

    pub fn code(&self) -> &Code {
        &self.code
    }
}

/// The decrypted stage2 unpacker program together with the stage1 code it unpacks.
pub struct Stage2 {
    header: PycHeader,
    stage1_code: Arc<Code>,
    bytes: Vec<u8>,
}

impl Stage2 {
    pub fn header(&self) -> PycHeader {
        self.header
    }

    pub fn bytes(&self) -> &[u8] {
        &self.bytes
    }

    pub fn into_bytes(self) -> Vec<u8> {
        self.bytes
    }

    /// Runs the stage2 program on the small VM, which unscrambles the stage1
    /// `co_code` into the marshalled stage3 code object.
    pub fn execute(&self) -> Result<Stage3, UnpackError> {
        let code = load_code(&self.bytes, Stage::Two)?;
        let bytes = smallvm::exec_stage2(Arc::new(code), Arc::clone(&self.stage1_code))?;

        Ok(Stage3 { bytes })
    }
}

pub struct Stage3 {
    bytes: Vec<u8>,
}

impl Stage3 {
    pub fn bytes(&self) -> &[u8] {
        &self.bytes
    }

    pub fn into_bytes(self) -> Vec<u8> {
        self.bytes
    }

    /// Extracts the marshalled stage4 module code. It is stored base64+zlib encoded and
    /// reversed in the stage3 `co_code`, after the first newline.
    pub fn extract_stage4(&self) -> Result<Vec<u8>, UnpackError> {
        let code = load_code(&self.bytes, Stage::Three)?;

        let Some(newline) = code.code.iter().position(|byte| *byte == b'\n') else {
            return Err(UnpackError::MissingNewline);
        };
        let encoded: Vec<u8> = code.code[newline + 1..].iter().rev().copied().collect();

        unpack_b64_compressed_data(&encoded, Stage::Three)
    }
}

/// A module's real top-level code object and the stage data that led to it.
pub struct UnpackedModule {
    header: PycHeader,
    code: Code,
    stages: Stages,
}

impl UnpackedModule {
    pub fn header(&self) -> PycHeader {
        self.header
    }

    pub fn code(&self) -> &Code {
        &self.code
    }

    pub fn into_code(self) -> Code {
        self.code
    }

    /// The marshalled form of [`Self::code`].
    pub fn code_bytes(&self) -> &[u8] {
        match &self.stages {
            Stages::Plain { body } => body,
            Stages::Encrypted(stages) => &stages.stage4,
        }
    }

    pub fn stages(&self) -> &Stages {
        &self.stages
    }
}

pub enum Stages {
    /// The `.pyc` body, which is the marshalled module code.
    Plain {
        body: Vec<u8>,
    },
    Encrypted(EncryptedStages),
}

/// Marshalled code objects of each layer below stage1.
pub struct EncryptedStages {
    pub stage2: Vec<u8>,
    pub stage3: Vec<u8>,
    pub stage4: Vec<u8>,
}

/// Unpacks a whole `.pyc` file into its real top-level code object.
pub fn unpack_module(pyc: &[u8]) -> Result<UnpackedModule, UnpackError> {
    let stage2 = match Stage1::parse(pyc)? {
        Stage1::Plain(plain) => {
            return Ok(UnpackedModule {
                header: plain.header,
                code: plain.code,
                stages: Stages::Plain { body: plain.body.to_vec() },
            });
        }
        Stage1::Encrypted(stage2) => stage2,
    };

    let stage3 = stage2.execute()?;
    let stage4 = stage3.extract_stage4()?;
    let code = load_code(&stage4, Stage::Four)?;

    Ok(UnpackedModule {
        header: stage2.header,
        code,
        stages: Stages::Encrypted(EncryptedStages { stage2: stage2.into_bytes(), stage3: stage3.into_bytes(), stage4 }),
    })
}

fn load_code(bytes: &[u8], stage: Stage) -> Result<Code, UnpackError> {
    let obj = py27_marshal::read::marshal_loads(bytes).map_err(|source| UnpackError::Marshal { stage, source })?;
    let Obj::Code(code) = obj else {
        return Err(UnpackError::NotCode { stage, found: obj.typ() });
    };

    // The root object is normally unshared once parsing finishes.
    let code = match Arc::try_unwrap(code) {
        Ok(lock) => lock.into_inner().unwrap_or_else(PoisonError::into_inner),
        Err(shared) => read_lock(&shared).clone(),
    };

    Ok(code)
}

fn unpack_b64_compressed_data(data: &[u8], stage: Stage) -> Result<Vec<u8>, UnpackError> {
    let text = std::str::from_utf8(data).map_err(|source| UnpackError::PayloadNotText { stage, source })?;
    let compressed = base64::decode(text.trim()).map_err(|source| UnpackError::Base64 { stage, source })?;

    let mut inflated = Vec::new();
    ZlibDecoder::new(compressed.as_slice())
        .read_to_end(&mut inflated)
        .map_err(|source| UnpackError::Zlib { stage, source })?;

    Ok(inflated)
}
