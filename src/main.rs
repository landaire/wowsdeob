use anyhow::Result;
use byteorder::{LittleEndian, ReadBytesExt};
use flate2::read::ZlibDecoder;
use flate2::Compression;
use memmap::MmapOptions;
use std::fs::File;
use std::io::prelude::*;
use std::io::{BufReader, Cursor};
use std::path::{Path, PathBuf};
use structopt::StructOpt;

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
        if file.is_dir() {
            std::fs::create_dir_all(&target_path)?;
            continue;
        }

        let mut decompressed_file = Vec::with_capacity(file.size() as usize);
        file.read_to_end(&mut decompressed_file)?;
        match decrypt_file(decompressed_file.as_slice(), opt.debug) {
            Ok(decrypted_data) => {
                std::fs::write(target_path, decrypted_data.as_slice())?;
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
        let consts = if let py_marshal::Obj::Bytes(b) = &code.consts[3] {
            b
        } else {
            return Err(crate::error::DecodingError::ObjectError(
                "consts[3]",
                code.consts[3].clone(),
            )
            .into());
        };

        if debug {
            println!(
                "Internal file name: {}",
                std::str::from_utf8(code.filename.as_ref())?
            );
        }

        let mut decrypted_code = Vec::with_capacity(code.code.len());
        for i in 0..consts.len() {
            decrypted_code.push(code.code[i % code.code.len()] ^ consts[i])
        }

        let b64_data = std::str::from_utf8(&decrypted_code)?;
        let decoded_data = base64::decode(&b64_data.trim())?;

        let mut zlib_decoder = ZlibDecoder::new(decoded_data.as_slice());
        let mut inflated_data = Vec::new();
        zlib_decoder.read_to_end(&mut inflated_data)?;

        Ok(inflated_data)
    } else {
        Err(crate::error::DecodingError::ObjectError("root obj", obj.clone()).into())
    }
}
