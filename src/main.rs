#![feature(get_mut_unchecked)]
#![feature(map_first_last)]

use anyhow::Result;
use byteorder::{LittleEndian, ReadBytesExt};
use csv::WriterBuilder;
use flate2::read::ZlibDecoder;
use rayon::prelude::*;

use log::{debug, error};
use memmap::MmapOptions;
use once_cell::sync::OnceCell;
use py_marshal::{Code, Obj};
use rayon::Scope;
use std::collections::HashMap;
use std::fs::File;
use std::io::prelude::*;
use std::io::Cursor;
use std::path::{Path, PathBuf};
use std::sync::atomic::{AtomicUsize, Ordering};
use std::sync::{Arc, Mutex};
use strings::CodeObjString;
use structopt::StructOpt;

/// Representing code as a graph of basic blocks
mod code_graph;
/// Deobfuscation module
mod deob;
/// Errors
mod error;
/// Provides code for partially executing a code object and identifying const conditions
mod partial_execution;
/// Python VM
mod smallvm;
/// Management of Python strings for string dumping
mod strings;

pub(crate) static ARGS: OnceCell<Opt> = OnceCell::new();
pub(crate) static FILES_PROCESSED: OnceCell<AtomicUsize> = OnceCell::new();

#[derive(Debug, Clone, StructOpt)]
#[cfg_attr(not(feature = "reduced_functionality"), structopt(name = "wowsdeob", about = "WoWs scripts deobfuscator"))]
#[cfg_attr(feature = "reduced_functionality", structopt(name = "wowsdeob", about = "WoWs scripts deobfuscator (string dumping only edition)"))]
struct Opt {
    /// Input file. This may be either a `scripts.zip` file containing many
    /// obfuscated .pyc files, or this argument may be a single .pyc file.
    #[structopt(parse(from_os_str))]
    input: PathBuf,

    /// Output directory
    #[structopt(parse(from_os_str))]
    #[cfg(not(feature = "reduced_functionality"))]
    output_dir: PathBuf,

    /// Enable verbose logging
    #[structopt(short = "v")]
    verbose: bool,

    /// Enable verbose debug logging
    #[structopt(short = "mv")]
    more_verbose: bool,

    /// Disable all logging
    #[structopt(short = "q")]
    quiet: bool,

    /// Enable outputting code graphs to dot format
    #[structopt(short = "g")]
    #[cfg(not(feature = "reduced_functionality"))]
    graphs: bool,

    /// Dry run only -- do not write any files
    #[structopt(long = "dry")]
    dry: bool,

    /// Only dump strings frmo the stage4 code. Do not do any further processing
    #[structopt(subcommand)]
    #[cfg(not(feature = "reduced_functionality"))]
    cmd: Option<Command>,
}

#[derive(Debug, Clone, StructOpt)]
enum Command {
    StringsOnly,
}

fn main() -> Result<()> {
    let opt = Opt::from_args();

    // initialize our globals
    ARGS.set(opt.clone()).unwrap();
    FILES_PROCESSED
        .set(std::sync::atomic::AtomicUsize::new(0))
        .unwrap();

    // Set up our logger if the user passed the debug flag. With reduced
    // functionality enabled we don't want any logging to avoid outputting info
    // for how obfuscation works.
    if cfg!(feature = "reduced_functionality") || opt.quiet {
        // do not initialize the logger
    } else if opt.more_verbose {
        simple_logger::SimpleLogger::new()
            .with_level(log::LevelFilter::Trace)
            .with_module_level("wowsdeob::smallvm", log::LevelFilter::Debug)
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

    #[cfg(not(feature = "reduced_functionality"))]
    crate::code_graph::DISABLE_GRAPHS.set(!opt.graphs);

    let file = File::open(&opt.input)?;
    let mmap = unsafe { MmapOptions::new().map(&file)? };

    let reader = Cursor::new(&mmap);

    let file_count = Arc::new(AtomicUsize::new(0));
    #[cfg(not(feature = "reduced_functionality"))]
    let csv_output = if matches!(opt.cmd, Some(Command::StringsOnly)) {
        Some(Arc::new(Mutex::new(
            csv::WriterBuilder::new().from_path("strings.csv")?,
        )))
    } else {
        None
    };
    #[cfg(feature = "reduced_functionality")]
    let csv_output = Some(Arc::new(Mutex::new(
            csv::WriterBuilder::new().from_path("strings.csv")?,
        )));


    match opt.input.extension().map(|ext| ext.to_str().unwrap()) {
        Some("zip") => {
            let mut zip = zip::ZipArchive::new(reader)?;

            let results = Arc::new(Mutex::new(vec![]));
            let scope_result = rayon::scope(|s| -> Result<()> {
                for i in 0..zip.len() {
                    let mut file = zip.by_index(i)?;

                    let file_name = file.name().to_string();
                    debug!("Filename: {:?}", file_name);

                    //if !file_name.ends_with("m032b8507.pyc") {
                    //if !file_name.ends_with("md40d9a59.pyc") {
                    //if !file_name.contains("m07329f60.pyc") {
                    // if !file_name.ends_with("random.pyc") {
                    //     continue;
                    // }

                    let file_path = match file.enclosed_name() {
                        Some(path) => path,
                        None => {
                            error!("File `{:?}` is not a valid path", file_name);
                            continue;
                        }
                    };
                    #[cfg(not(feature = "reduced_functionality"))]
                    let target_path = opt.output_dir.join(file_path);

                    #[cfg(feature = "reduced_functionality")]
                    let target_path = PathBuf::from(file_path);

                    if !opt.dry && file.is_dir() {
                        #[cfg(not(feature = "reduced_functionality"))]
                        std::fs::create_dir_all(&target_path)?;
                        continue;
                    }

                    let mut decompressed_file = Vec::with_capacity(file.size() as usize);
                    file.read_to_end(&mut decompressed_file)?;

                    let file_count = Arc::clone(&file_count);
                    let csv_output = csv_output.clone();

                    let results = Arc::clone(&results);
                    s.spawn(move |_| {
                        let res = dump_pyc(decompressed_file.as_slice(), &target_path, csv_output);
                        if res.is_ok() {
                            file_count.fetch_add(1, Ordering::Relaxed);
                        }

                        results.lock().unwrap().push((file_name, res))
                    });

                    //break;
                }

                Ok(())
            });

            scope_result?;

            let results = results.lock().unwrap();
            for (filename, result) in &*results {
                if let Err(err) = result {
                    eprintln!("Error dumping {:?}: {}", filename, err);
                }
            }
        }
        _ => {
            #[cfg(not(feature = "reduced_functionality"))]
            let target_path = opt.output_dir.join(opt.input.file_name().unwrap());
            #[cfg(feature = "reduced_functionality")]
            let target_path = PathBuf::from(opt.input.file_name().unwrap());
            if dump_pyc(&mmap, &target_path, csv_output)? {
                file_count.fetch_add(1, Ordering::Relaxed);
            }
        }
    }

    println!("Extracted {} files", file_count.load(Ordering::Relaxed));

    Ok(())
}

fn dump_pyc(
    decompressed_file: &[u8],
    target_path: &Path,
    strings_output: Option<Arc<Mutex<csv::Writer<std::fs::File>>>>,
) -> Result<bool> {
    use std::convert::TryInto;
    let magic = u32::from_le_bytes(decompressed_file[0..4].try_into().unwrap());
    let moddate = u32::from_le_bytes(decompressed_file[4..8].try_into().unwrap());
    let opt = ARGS.get().unwrap();
    match decrypt_stage1(decompressed_file) {
        Ok(decrypted_data) => {
            if !opt.dry {
                // Don't use `cfg!()` to avoid putting this code block in the binary for ez patching.
                #[cfg(not(feature = "reduced_functionality"))]
                {
                    let mut original_file = File::create(&target_path)?;
                    original_file.write_all(decompressed_file)?;

                    // Write the decrypted (stage2) data
                    let stage2_path = make_target_filename(&target_path, "_stage2");
                    let mut stage2_file = File::create(stage2_path)?;
                    stage2_file.write_all(&magic.to_le_bytes()[..])?;
                    stage2_file.write_all(&moddate.to_le_bytes()[..])?;
                    stage2_file.write_all(decrypted_data.original.as_slice())?;
                }

                if let Some(deob) = &decrypted_data.deob {
                    #[cfg(not(feature = "reduced_functionality"))]
                    {
                        // Write the decrypted (stage2) data
                        let stage2_path = make_target_filename(&target_path, "_stage2_deob");

                        let mut stage2_file = File::create(stage2_path)?;
                        stage2_file.write_all(&magic.to_le_bytes()[..])?;
                        stage2_file.write_all(&moddate.to_le_bytes()[..])?;
                        stage2_file.write_all(deob.as_slice())?;
                    }

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

                #[cfg(not(feature = "reduced_functionality"))]
                {
                    if !opt.dry {
                        let stage3_path = make_target_filename(&target_path, "_stage3");
                        let mut stage3_file = File::create(stage3_path)?;
                        stage3_file.write_all(&magic.to_le_bytes()[..])?;
                        stage3_file.write_all(&moddate.to_le_bytes()[..])?;
                        stage3_file.write_all(stage3_data.as_slice())?;
                    }
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

                    #[cfg(not(feature = "reduced_functionality"))]
                    {
                        let stage4_path = make_target_filename(&target_path, "_stage4");
                        let mut stage4_file = File::create(stage4_path)?;
                        stage4_file.write_all(&magic.to_le_bytes()[..])?;
                        stage4_file.write_all(&moddate.to_le_bytes()[..])?;
                        stage4_file.write_all(stage4_data.as_slice())?;
                    }

                    #[cfg(not(feature = "reduced_functionality"))]
                    let cmd = opt.cmd.as_ref();
                    #[cfg(feature = "reduced_functionality")]
                    let cmd = Some(Command::StringsOnly);

                    match cmd {
                        Some(Command::StringsOnly) => {
                            // Dump strings for this file
                            #[cfg(not(feature = "reduced_functionality"))]
                            let pyc_filename = target_path
                                .strip_prefix(&ARGS.get().unwrap().output_dir)
                                .unwrap()
                                .to_str()
                                .unwrap();
                            #[cfg(feature = "reduced_functionality")]
                            let pyc_filename = target_path
                                .to_str()
                                .unwrap();
                            if let py_marshal::Obj::Code(code) =
                                py_marshal::read::marshal_loads(stage4_data.as_slice()).unwrap()
                            {
                                let strings =
                                    dump_codeobject_strings(pyc_filename, Arc::clone(&code));

                                let strings_output = strings_output.as_ref().unwrap();

                                strings.par_iter().for_each(|s| {
                                    strings_output
                                        .lock()
                                        .unwrap()
                                        .serialize(s)
                                        .expect("failed to serialize output string");
                                });
                            }
                        }
                        None => {
                            // Deobfuscate stage4
                            #[cfg(not(feature = "reduced_functionality"))]
                            {
                                let stage4_deob = deobfuscate_codeobj(stage4_data.as_slice())?;

                                let stage4_path = make_target_filename(&target_path, "_stage4_deob");
                                let mut stage4_file = File::create(stage4_path)?;
                                stage4_file.write_all(&magic.to_le_bytes()[..])?;
                                stage4_file.write_all(&moddate.to_le_bytes()[..])?;
                                stage4_file.write_all(stage4_deob.deob.unwrap().as_slice())?;
                            }
                        }
                    }
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
        let mut results = vec![];
        let mut mapped_names = HashMap::new();
        let mut out_results = Arc::new(Mutex::new(vec![]));
        rayon::scope(|scope| {
            deobfuscate_nested_code_objects(Arc::clone(&code), scope, Arc::clone(&out_results));
        });

        let out_results = Arc::try_unwrap(out_results).unwrap().into_inner().unwrap();
        for result in out_results {
            let result = result?;
            results.push((result.0, result.1));
            mapped_names.extend(result.2);
        }

        // sort these items by their file number. ordering matters since python pulls it as a
        // stack
        results.sort_by(|a, b| a.0.cmp(&b.0));

        let output_data = crate::deob::rename_vars(
            data,
            &mut results.iter().map(|result| result.1.as_slice()),
            &mapped_names,
        )
        .unwrap();

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
    code: Arc<Code>,
    scope: &Scope,
    out_results: Arc<Mutex<Vec<Result<(usize, Vec<u8>, HashMap<String, String>)>>>>,
) {
    let file_number = FILES_PROCESSED
        .get()
        .unwrap()
        .fetch_add(1, Ordering::Relaxed);

    let task_code = Arc::clone(&code);
    let thread_results = Arc::clone(&out_results);
    scope.spawn(
        move |scope| match crate::deob::deobfuscate_code(task_code, file_number) {
            Ok((new_bytecode, mapped_functions)) => {
                thread_results.lock().unwrap().push(Ok((
                    file_number,
                    new_bytecode,
                    mapped_functions,
                )));
            }
            Err(e) => {
                thread_results.lock().unwrap().push(Err(e));
            }
        },
    );

    // We need to find and replace the code sections which may also be in the const data
    for c in code.consts.iter() {
        if let Obj::Code(const_code) = c {
            let thread_results = Arc::clone(&out_results);
            let thread_code = Arc::clone(const_code);
            // Call deobfuscate_bytecode first since the bytecode comes before consts and other data

            deobfuscate_nested_code_objects(thread_code, scope, thread_results);
        }
    }
}

fn dump_codeobject_strings(pyc_filename: &str, code: Arc<Code>) -> Vec<CodeObjString> {
    let new_strings = Mutex::new(vec![]);
    code.names.par_iter().for_each(|name| {
        new_strings.lock().unwrap().push(CodeObjString::new(
            code.as_ref(),
            pyc_filename,
            crate::strings::StringType::Name,
            name.to_string().as_ref(),
        ))
    });

    code.varnames.par_iter().for_each(|name| {
        new_strings.lock().unwrap().push(CodeObjString::new(
            code.as_ref(),
            pyc_filename,
            crate::strings::StringType::VarName,
            name.to_string().as_ref(),
        ))
    });

    code.consts.as_ref().par_iter().for_each(|c| {
        if let py_marshal::Obj::String(s) = c {
            new_strings.lock().unwrap().push(CodeObjString::new(
                code.as_ref(),
                pyc_filename,
                crate::strings::StringType::Const,
                s.to_string().as_ref(),
            ))
        }
    });

    // We need to find and replace the code sections which may also be in the const data
    code.consts.par_iter().for_each(|c| {
        if let Obj::Code(const_code) = c {
            // Call deobfuscate_bytecode first since the bytecode comes before consts and other data
            let mut strings = dump_codeobject_strings(pyc_filename, Arc::clone(&const_code));
            new_strings.lock().unwrap().append(&mut strings);
        }
    });

    new_strings.into_inner().unwrap()
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
