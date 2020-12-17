#![feature(get_mut_unchecked)]

use anyhow::Result;
use byteorder::{LittleEndian, ReadBytesExt};
use flate2::read::ZlibDecoder;
use flate2::Compression;
use log::{debug, error};
use memmap::MmapOptions;
use py_marshal::{Code, Obj};
use std::fs::File;
use std::io::prelude::*;
use std::io::{BufReader, Cursor};
use std::path::{Path, PathBuf};
use std::sync::Arc;
use structopt::StructOpt;

/// Deobfuscation module
mod deob;
mod error;
mod smallvm;

#[derive(Debug, StructOpt)]
#[structopt(name = "wowsdeob", about = "WoWs scripts deobfuscator")]
struct Opt {
    /// Input file
    #[structopt(parse(from_os_str))]
    input: PathBuf,

    /// Output directory
    #[structopt(parse(from_os_str))]
    output_dir: PathBuf,

    /// Enable debug logging
    #[structopt(short = "d", long = "debug")]
    debug: bool,

    /// Dry run only -- do not write any files
    #[structopt(long = "dry")]
    dry: bool,
}

fn main() -> Result<()> {
    let opt = Opt::from_args();

    // Set up our logger if the user passed the debug flag
    if opt.debug {
        simple_logger::SimpleLogger::new().init().unwrap();
    } else {
        simple_logger::SimpleLogger::new()
            .with_level(log::LevelFilter::Error)
            .init()
            .unwrap();
    }

    let file = File::open(opt.input)?;
    let mmap = unsafe { MmapOptions::new().map(&file)? };

    let mut reader = Cursor::new(&mmap);

    let mut zip = zip::ZipArchive::new(reader)?;

    let mut file_count = 0usize;

    for i in 0..zip.len() {
        let mut file = zip.by_index(i)?;
        let file_name = file.name();

        debug!("Filename: {:?}", file.name());

        if !file_name.ends_with("m032b8507.pyc") {
            continue;
        }

        let file_path = match file.enclosed_name() {
            Some(path) => path,
            None => {
                error!("File `{:?}` is not a valid path", file_name);
                continue;
            }
        };
        let target_path = opt.output_dir.join(file_path);
        if !opt.dry && file.is_dir() {
            std::fs::create_dir_all(&target_path)?;
            continue;
        }

        let mut decompressed_file = Vec::with_capacity(file.size() as usize);
        file.read_to_end(&mut decompressed_file)?;
        match decrypt_stage1(decompressed_file.as_slice()) {
            Ok(decrypted_data) => {
                if !opt.dry {
                    // Write the original data
                    std::fs::write(&target_path, decrypted_data.original.as_slice())?;

                    // Write the decrypted (stage1) data
                    let stage1_path = make_target_filename(&target_path, "_stage2");
                    std::fs::write(stage1_path, decrypted_data.original.as_slice())?;

                    if let Some(deob) = decrypted_data.deob {
                        // Write the decrypted (stage1) data
                        let stage1_path = make_target_filename(&target_path, "_stage2_deob");
                        std::fs::write(stage1_path, deob.as_slice())?;
                    }
                }
                decrypt_stage2(
                    decrypted_data.original.as_slice(),
                    decompressed_file.as_slice(),
                )?;
                file_count += 1;
            }
            Err(e) => {
                error!("Error decrypting stage1: {}", e);
            }
        }

        debug!("");
        break;
    }

    println!("Extracted {} files", file_count);

    Ok(())
}

fn make_target_filename<P: AsRef<Path>>(existing_file_name: P, file_suffix: &str) -> PathBuf {
    let path_ref = existing_file_name.as_ref();
    path_ref
        .parent()
        .expect("target has no parent directory?")
        .join(
            path_ref
                .file_stem()
                .expect("target has no file name?")
                .to_str()
                .unwrap()
                .to_owned()
                + file_suffix,
        )
        .with_extension(path_ref.extension().expect("target has no extension?"))
}

struct DeobfuscatedCode {
    original: Vec<u8>,
    deob: Option<Vec<u8>>,
}

fn decrypt_stage1(data: &[u8]) -> Result<DeobfuscatedCode> {
    let mut file_reader = Cursor::new(&data);
    let magic = file_reader.read_u32::<LittleEndian>()?;
    let moddate = file_reader.read_u32::<LittleEndian>()?;

    debug!("Magic: 0x{:X}", magic);
    debug!("Mod Date: 0x{:X}", moddate);

    let obj = py_marshal::read::marshal_loads(&data[file_reader.position() as usize..])?;
    if let py_marshal::Obj::Code(code) = obj {
        for name in &code.names {
            debug!(
                "Name: {}",
                std::str::from_utf8(name).unwrap_or("BAD_UNICODE_DATA")
            );
        }

        let internal_filename =
            std::str::from_utf8(code.filename.as_ref()).unwrap_or("BAD_UNICODE_DATA");

        let is_encrypted = internal_filename == "Lesta";
        if !is_encrypted {
            return Ok(DeobfuscatedCode {
                original: data.to_vec(),
                deob: None,
            });
        }

        let consts = if let py_marshal::Obj::String(b) = &code.consts[3] {
            b
        } else {
            error!("{:#?}", code.consts);
            return Err(
                crate::error::Error::ObjectError("consts[3]", code.consts[3].clone()).into(),
            );
        };

        debug!(
            "Internal file name: {}",
            std::str::from_utf8(code.filename.as_ref()).unwrap_or("BAD_UNICODE_DATA")
        );

        let mut decrypted_code: Vec<u8> = Vec::with_capacity(code.code.len());
        for i in 0..consts.len() {
            decrypted_code.push(code.code[i % code.code.len()] ^ consts[i])
        }

        let b64_data = std::str::from_utf8(&decrypted_code)?;
        let decoded_data = base64::decode(&b64_data.trim())?;

        let mut zlib_decoder = ZlibDecoder::new(decoded_data.as_slice());
        let mut inflated_data: Vec<u8> = Vec::new();
        inflated_data.extend_from_slice(&magic.to_le_bytes()[..]);
        inflated_data.extend_from_slice(&moddate.to_le_bytes()[..]);
        zlib_decoder.read_to_end(&mut inflated_data)?;

        // println!("{}", pretty_hex::pretty_hex(&&decrypted_code[0..0x20]));
        if let py_marshal::Obj::Code(code) =
            py_marshal::read::marshal_loads(&inflated_data[8..]).unwrap()
        {
            let mut deobfuscated_code = vec![];
            deobfuscate_nested_code_objects(&mut deobfuscated_code, &code)?;

            let mut new_obj =
                crate::deob::rename_vars(&inflated_data[8..], deobfuscated_code.as_slice())
                    .unwrap();
            let mut output_data = Vec::with_capacity(new_obj.len() + 8);
            output_data.extend_from_slice(&magic.to_le_bytes()[..]);
            output_data.extend_from_slice(&moddate.to_le_bytes()[..]);
            output_data.append(&mut new_obj);

            Ok(DeobfuscatedCode {
                original: inflated_data,
                deob: Some(output_data),
            })
        } else {
            Ok(DeobfuscatedCode {
                original: inflated_data,
                deob: None,
            })
        }
    } else {
        Err(crate::error::Error::ObjectError("root obj", obj.clone()).into())
    }
}

fn deobfuscate_nested_code_objects(output_bytecodes: &mut Vec<Vec<u8>>, code: &Code) -> Result<()> {
    output_bytecodes.push(crate::deob::deobfuscate_bytecode(
        code.code.as_slice(),
        Arc::clone(&code.consts),
    )?);

    // We need to find and replace the code sections which may also be in the const data
    for c in code.consts.iter() {
        if let Obj::Code(const_code) = c {
            // Call deobfuscate_bytecode first since the bytecode comes before consts and other data
            deobfuscate_nested_code_objects(output_bytecodes, const_code)?;
        }
    }

    Ok(())
}

fn decrypt_stage2(stage2: &[u8], stage1: &[u8]) -> Result<()> {
    if let py_marshal::Obj::Code(stage1_code) =
        py_marshal::read::marshal_loads(&stage1[8..]).unwrap()
    {
        if let py_marshal::Obj::Code(stage2_code) =
            py_marshal::read::marshal_loads(&stage2[8..]).unwrap()
        {
            crate::smallvm::exec_stage2(stage2_code, stage1_code)?;
        } else {
            error!("stage2 is not a code object?");
        }
    } else {
        error!("stage1 is not a code object?");
    }

    Ok(())
}
