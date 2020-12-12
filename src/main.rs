use anyhow::Result;
use byteorder::{LittleEndian, ReadBytesExt};
use flate2::read::ZlibDecoder;
use flate2::Compression;
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
    let file = File::open(opt.input)?;
    let mmap = unsafe { MmapOptions::new().map(&file)? };

    let mut reader = Cursor::new(&mmap);

    let mut zip = zip::ZipArchive::new(reader)?;

    let mut file_count = 0usize;

    for i in 0..zip.len() {
        let mut file = zip.by_index(i)?;
        let file_name = file.name();

        if opt.debug {
            println!("Filename: {:?}", file.name());
        }

        let file_path = match file.enclosed_name() {
            Some(path) => path,
            None => {
                eprintln!("File `{:?}` is not a valid path", file_name);
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
        match decrypt_file(decompressed_file.as_slice(), opt.debug) {
            Ok(decrypted_data) => {
                if !opt.dry {
                    std::fs::write(target_path, decrypted_data.as_slice())?;
                }
                file_count += 1;
            }
            Err(e) => {
                eprintln!("Error: {}", e);
            }
        }

        if opt.debug {
            println!("");
        }
    }

    if opt.debug {
        println!("Extracted {} files", file_count);
    }

    Ok(())
}

fn decrypt_file(data: &[u8], debug: bool) -> Result<Vec<u8>> {
    let mut file_reader = Cursor::new(&data);
    let magic = file_reader.read_u32::<LittleEndian>()?;
    let moddate = file_reader.read_u32::<LittleEndian>()?;

    if debug {
        println!("Magic: 0x{:X}", magic);
        println!("Mod Date: 0x{:X}", moddate);
    }

    // fucking error_chain library
    let obj = py_marshal::read::marshal_loads(&data[file_reader.position() as usize..]).unwrap();
    if let py_marshal::Obj::Code(code) = obj {
        if debug {
            for name in &code.names {
                println!(
                    "Name: {}",
                    std::str::from_utf8(name).unwrap_or("BAD_UNICODE_DATA")
                );
            }
        }

        let consts = if let py_marshal::Obj::Bytes(b) = &code.consts[3] {
            b
        } else {
            return Err(
                crate::error::Error::ObjectError("consts[3]", code.consts[3].clone()).into(),
            );
        };

        assert!(code.nlocals == 0);

        if debug {
            println!(
                "Internal file name: {}",
                std::str::from_utf8(code.filename.as_ref()).unwrap_or("BAD_UNICODE_DATA")
            );
        }

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
            let mut new_bytecode = Vec::with_capacity(inflated_data.len());

            // Replace main bytecode
            let mut offset = new_bytecode.len();
            while offset < inflated_data.len() {
                if &inflated_data[offset..offset + code.code.len()] == code.code.as_slice() {
                    new_bytecode.append(&mut crate::deob::deobfuscate_bytecode(
                        code.code.as_slice(),
                    )?);
                    break;
                } else {
                    new_bytecode.push(inflated_data[offset]);
                    offset += 1;
                }
            }

            // We need to find and replace the code sections which may also be in the const data
            for c in code.consts.iter() {
                if let Obj::Code(const_code) = c {
                    let mut offset = new_bytecode.len();
                    while offset < inflated_data.len() {
                        if &inflated_data[offset..offset + const_code.code.len()]
                            == const_code.code.as_slice()
                        {
                            new_bytecode.append(&mut crate::deob::deobfuscate_bytecode(
                                const_code.code.as_slice(),
                            )?);
                            break;
                        } else {
                            new_bytecode.push(inflated_data[offset]);
                            offset += 1;
                        }
                    }
                }
            }

            if new_bytecode.len() < inflated_data.len() {
                new_bytecode.extend_from_slice(&inflated_data[new_bytecode.len()..]);
            }

            Ok(new_bytecode)
        } else {
            Ok(inflated_data)
        }
    } else {
        Err(crate::error::Error::ObjectError("root obj", obj.clone()).into())
    }
}
