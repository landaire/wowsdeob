#![feature(get_mut_unchecked)]
#![feature(map_first_last)]

use anyhow::Result;
use byteorder::{LittleEndian, ReadBytesExt};
use flate2::read::ZlibDecoder;

use log::{debug, error};
use memmap::MmapOptions;
use py_marshal::{Code, Obj};
use std::collections::HashMap;
use std::fs::File;
use std::io::prelude::*;
use std::io::Cursor;
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

    /// Enable verbose logging
    #[structopt(short = "v")]
    verbose: bool,

    /// Enable verbose debug logging
    #[structopt(short = "mv")]
    more_verbose: bool,

    /// Dry run only -- do not write any files
    #[structopt(long = "dry")]
    dry: bool,
}

fn main() -> Result<()> {
    let opt = Opt::from_args();

    // Set up our logger if the user passed the debug flag
    if opt.more_verbose {
        simple_logger::SimpleLogger::new()
            .with_level(log::LevelFilter::Trace)
            .init()
            .unwrap();
    } else if opt.verbose {
        simple_logger::SimpleLogger::new()
            .with_level(log::LevelFilter::Debug)
            .init()
            .unwrap();
    } else {
        simple_logger::SimpleLogger::new()
            .with_level(log::LevelFilter::Error)
            .init()
            .unwrap();
    }

    let file = File::open(&opt.input)?;
    let mmap = unsafe { MmapOptions::new().map(&file)? };

    let reader = Cursor::new(&mmap);

    let mut file_count = 0usize;
    println!("{:?}", opt.input);
    let _zip_ext = std::ffi::OsStr::new("zip");
    if let Some(_zip_ext) = opt.input.extension() {
        let mut zip = zip::ZipArchive::new(reader)?;

        for i in 0..zip.len() {
            let mut file = zip.by_index(i)?;
            let file_name = file.name();

            debug!("Filename: {:?}", file.name());

            //if !file_name.ends_with("m032b8507.pyc") {
            if !file_name.ends_with("md40d9a59.pyc") {
                //if !file_name.contains("m07329f60.pyc") {
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

            if dump_pyc(decompressed_file.as_slice(), &target_path, &opt)? {
                file_count += 1;
            }

            debug!("");
            break;
        }
    } else {
        let target_path = opt.output_dir.join(opt.input.file_name().unwrap());
        if dump_pyc(&mmap, &target_path, &opt)? {
            file_count += 1;
        }
    }

    println!("Extracted {} files", file_count);

    Ok(())
}

fn dump_pyc(decompressed_file: &[u8], target_path: &Path, opt: &Opt) -> Result<bool> {
    use std::convert::TryInto;
    let magic = u32::from_le_bytes(decompressed_file[0..4].try_into().unwrap());
    let moddate = u32::from_le_bytes(decompressed_file[4..8].try_into().unwrap());
    match decrypt_stage1(decompressed_file) {
        Ok(decrypted_data) => {
            if !opt.dry {
                let mut original_file = File::create(&target_path)?;
                original_file.write_all(decompressed_file)?;

                // Write the decrypted (stage2) data
                let stage2_path = make_target_filename(&target_path, "_stage2");
                let mut stage2_file = File::create(stage2_path)?;
                stage2_file.write_all(&magic.to_le_bytes()[..])?;
                stage2_file.write_all(&moddate.to_le_bytes()[..])?;
                stage2_file.write_all(decrypted_data.original.as_slice())?;

                if let Some(deob) = &decrypted_data.deob {
                    // Write the decrypted (stage2) data
                    let stage2_path = make_target_filename(&target_path, "_stage2_deob");

                    let mut stage2_file = File::create(stage2_path)?;
                    stage2_file.write_all(&magic.to_le_bytes()[..])?;
                    stage2_file.write_all(&moddate.to_le_bytes()[..])?;
                    stage2_file.write_all(deob.as_slice())?;

                    //panic!("done");
                    // if let py_marshal::Obj::Code(code) =
                    //     py_marshal::read::marshal_loads(deob.as_slice()).unwrap()
                    // {
                    //     panic!("{:?}", crate::decompile::decompile(Arc::clone(&code)));
                    // }
                }
            }

            if decrypted_data.deob.is_some() {
                let stage3_data =
                    decrypt_stage2(decrypted_data.original.as_slice(), &decompressed_file[8..])?;

                if !opt.dry {
                    let stage3_path = make_target_filename(&target_path, "_stage3");
                    let mut stage3_file = File::create(stage3_path)?;
                    stage3_file.write_all(&magic.to_le_bytes()[..])?;
                    stage3_file.write_all(&moddate.to_le_bytes()[..])?;
                    stage3_file.write_all(stage3_data.as_slice())?;
                }

                if let py_marshal::Obj::Code(code) =
                    py_marshal::read::marshal_loads(stage3_data.as_slice()).unwrap()
                {
                    let b64_string: Vec<u8> = code.code
                        [code.code.iter().position(|b| *b == b'\n').unwrap() + 1..]
                        .iter()
                        .rev()
                        .copied()
                        .collect();

                    let stage4_data = unpack_b64_compressed_data(b64_string.as_slice())?;
                    let stage4_deob = deobfuscate_codeobj(stage4_data.as_slice())?;

                    let stage4_path = make_target_filename(&target_path, "_stage4");
                    let mut stage4_file = File::create(stage4_path)?;
                    stage4_file.write_all(&magic.to_le_bytes()[..])?;
                    stage4_file.write_all(&moddate.to_le_bytes()[..])?;
                    stage4_file.write_all(stage4_data.as_slice())?;

                    let stage4_path = make_target_filename(&target_path, "_stage4_deob");
                    let mut stage4_file = File::create(stage4_path)?;
                    stage4_file.write_all(&magic.to_le_bytes()[..])?;
                    stage4_file.write_all(&moddate.to_le_bytes()[..])?;
                    stage4_file.write_all(stage4_deob.deob.unwrap().as_slice())?;
                }
            }

            // if let Some(deob) = decrypted_data.deob {
            //     // Write the decrypted (stage1) data
            //     let stage1_path = make_target_filename(&target_path, "_stage2_deob");
            //     std::fs::write(stage1_path, deob.as_slice())?;
            // }

            return Ok(true);
        }
        Err(e) => {
            error!("Error decrypting stage1: {}", e);
        }
    }

    Ok(false)
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

fn unpack_b64_compressed_data(data: &[u8]) -> Result<Vec<u8>> {
    let b64_data = std::str::from_utf8(data)?;
    let decoded_data = base64::decode(&b64_data.trim())?;

    let mut zlib_decoder = ZlibDecoder::new(decoded_data.as_slice());
    let mut inflated_data: Vec<u8> = Vec::new();
    zlib_decoder.read_to_end(&mut inflated_data)?;

    Ok(inflated_data)
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

        let inflated_data = unpack_b64_compressed_data(decrypted_code.as_slice())?;

        // println!("{}", pretty_hex::pretty_hex(&&decrypted_code[0..0x20]));
        deobfuscate_codeobj(inflated_data.as_slice())
    } else {
        Err(crate::error::Error::ObjectError("root obj", obj.clone()).into())
    }
}

fn deobfuscate_codeobj(data: &[u8]) -> Result<DeobfuscatedCode> {
    if let py_marshal::Obj::Code(code) = py_marshal::read::marshal_loads(data).unwrap() {
        let mut deobfuscated_code = vec![];
        let mapped_names =
            deobfuscate_nested_code_objects(&mut deobfuscated_code, Arc::clone(&code))?;

        let output_data =
            crate::deob::rename_vars(data, deobfuscated_code.as_slice(), &mapped_names).unwrap();

        Ok(DeobfuscatedCode {
            original: data.to_vec(),
            deob: Some(output_data),
        })
    } else {
        Ok(DeobfuscatedCode {
            original: data.to_vec(),
            deob: None,
        })
    }
}

fn deobfuscate_nested_code_objects(
    output_bytecodes: &mut Vec<Vec<u8>>,
    code: Arc<Code>,
) -> Result<HashMap<String, String>> {
    let (new_bytecode, mut mapped_functions) = crate::deob::deobfuscate_code(Arc::clone(&code))?;
    output_bytecodes.push(new_bytecode);

    // We need to find and replace the code sections which may also be in the const data
    for c in code.consts.iter() {
        if let Obj::Code(const_code) = c {
            // Call deobfuscate_bytecode first since the bytecode comes before consts and other data
            mapped_functions.extend(deobfuscate_nested_code_objects(
                output_bytecodes,
                Arc::clone(const_code),
            )?);
        }
    }

    Ok(mapped_functions)
}

fn decrypt_stage2(stage2: &[u8], stage1: &[u8]) -> Result<Vec<u8>> {
    if let py_marshal::Obj::Code(stage1_code) = py_marshal::read::marshal_loads(stage1).unwrap() {
        if let py_marshal::Obj::Code(stage2_code) = py_marshal::read::marshal_loads(stage2).unwrap()
        {
            crate::smallvm::exec_stage2(stage2_code, stage1_code)
        } else {
            panic!("stage2 is not a code object?");
        }
    } else {
        panic!("stage1 is not a code object?");
    }
}
