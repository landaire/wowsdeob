#![feature(get_mut_unchecked)]
#![feature(map_first_last)]

use anyhow::Result;
use byteorder::{LittleEndian, ReadBytesExt};

use flate2::read::ZlibDecoder;
use log::trace;
use py27_marshal::bstr::BString;
use pydis::opcode::py27::Mnemonic;
use pydis::opcode::py27::Standard;
use rayon::prelude::*;

use log::{debug, error};
use memmap::MmapOptions;
use once_cell::sync::OnceCell;
use py27_marshal::{Code, Obj};
use pydis::opcode::Opcode;
use rayon::Scope;
use std::collections::HashMap;
use std::fs::File;
use std::io;
use std::io::prelude::*;
use std::io::Cursor;
use std::path::{Path, PathBuf};
use std::sync::atomic::{AtomicUsize, Ordering};
use std::sync::{Arc, Mutex};
use structopt::StructOpt;

/// Python VM
mod smallvm;

#[derive(Debug, Clone, StructOpt)]
#[cfg_attr(
    not(feature = "reduced_functionality"),
    structopt(name = "wowsdeob", about = "WoWs scripts deobfuscator")
)]
#[cfg_attr(
    feature = "reduced_functionality",
    structopt(
        name = "wowsdeob",
        about = "WoWs scripts deobfuscator (string dumping only edition)"
    )
)]
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
    #[structopt(short = "v", parse(from_occurrences))]
    verbose: usize,

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

    /// Your favorite Python 2.7 bytecode decompiler. This program assumes the decompiler's
    /// first positional argument is the file to decompile, and it prints the decompiled output
    /// to stdout
    #[structopt(long, default_value = "uncompyle6", env = "UNFUCK_DECOMPILER")]
    decompiler: String,

    /// Only dump strings frmo the stage4 code. Do not do any further processing
    #[structopt(subcommand)]
    #[cfg(not(feature = "reduced_functionality"))]
    cmd: Option<Command>,
}

#[derive(Debug, Clone, StructOpt)]
enum Command {
    StringsOnly,
    ModuleMap,
}

fn main() -> Result<()> {
    let opt = Arc::new(Opt::from_args());

    // Set up our logger if the user passed the debug flag. With reduced
    // functionality enabled we don't want any logging to avoid outputting info
    // for how obfuscation works.
    if opt.quiet {
        // do not initialize the logger
    } else if opt.verbose >= 2 {
        simple_logger::SimpleLogger::new()
            .with_level(log::LevelFilter::Trace)
            .with_module_level("unfuck::smallvm", log::LevelFilter::Debug)
            .init()
            .unwrap();
    } else if opt.verbose >= 1 {
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

    let module_map = Arc::new(Mutex::new(HashMap::new()));
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
                    let target_path = opt.output_dir.join(file_path);

                    if !opt.dry && file.is_dir() {
                        std::fs::create_dir_all(&target_path)?;
                        continue;
                    }

                    let mut decompressed_file = Vec::with_capacity(file.size() as usize);
                    file.read_to_end(&mut decompressed_file)?;

                    let file_count = Arc::clone(&file_count);
                    let csv_output = csv_output.clone();

                    let opt = Arc::clone(&opt);
                    let results = Arc::clone(&results);
                    let module_map = Arc::clone(&module_map);
                    s.spawn(move |_| {
                        let res = dump_pyc(
                            decompressed_file.as_slice(),
                            &target_path,
                            csv_output,
                            Arc::clone(&opt),
                            Arc::clone(&module_map),
                        );
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
            if dump_pyc(
                &mmap,
                &target_path,
                csv_output,
                Arc::clone(&opt),
                Arc::clone(&module_map),
            )? {
                file_count.fetch_add(1, Ordering::Relaxed);
            }
        }
    }

    if let Some(Command::ModuleMap) = opt.cmd.as_ref() {
        let target_path = opt.output_dir.join("module_map.json");
        let mut module_map = module_map.lock().unwrap();
        let serialized_data =
            serde_json::to_string_pretty(&*module_map).expect("failed to serialize module_map");
        std::fs::write(target_path, serialized_data.as_bytes())?;
    }

    println!("Extracted {} files", file_count.load(Ordering::Relaxed));

    Ok(())
}

fn dump_pyc(
    decompressed_file: &[u8],
    target_path: &Path,
    strings_output: Option<Arc<Mutex<csv::Writer<std::fs::File>>>>,
    opt: Arc<Opt>,
    module_map: Arc<Mutex<HashMap<String, String>>>,
) -> Result<bool> {
    use std::convert::TryInto;
    let magic = u32::from_le_bytes(decompressed_file[0..4].try_into().unwrap());
    let moddate = u32::from_le_bytes(decompressed_file[4..8].try_into().unwrap());
    let cmd = opt.cmd.as_ref();
    let write_deobfuscated_files = cmd.is_none() || opt.dry;
    match decrypt_stage1(decompressed_file, Arc::clone(&opt)) {
        Ok(decrypted_data) => {
            if write_deobfuscated_files {
                let mut original_file = File::create(&target_path)?;
                original_file.write_all(decompressed_file)?;

                // Write the decrypted (stage2) data
                let stage2_path = make_target_filename(&target_path, "_stage2");
                let mut stage2_file = File::create(stage2_path)?;
                stage2_file.write_all(&magic.to_le_bytes()[..])?;
                stage2_file.write_all(&moddate.to_le_bytes()[..])?;
                stage2_file.write_all(decrypted_data.original.as_slice())?;

                if let Some(stage_2_data) = &decrypted_data.deob {
                    // Write the decrypted (stage2) data
                    let stage2_path = make_target_filename(&target_path, "_stage2_deob");

                    let mut stage2_file = File::create(stage2_path)?;
                    stage2_file.write_all(&magic.to_le_bytes()[..])?;
                    stage2_file.write_all(&moddate.to_le_bytes()[..])?;
                    stage2_file.write_all(stage_2_data.as_slice())?;
                }
            }

            if decrypted_data.has_next_stage {
                let stage3_data =
                    decrypt_stage2(&decrypted_data.original, &decompressed_file[8..])?;

                let deobfuscator = unfuck::Deobfuscator::<Standard>::new(stage3_data.as_slice());
                let deobfuscator = if opt.graphs {
                    deobfuscator
                        .enable_graphs()
                        .on_graph_generated(|name, data| {
                            std::fs::write(name, data.as_bytes()).expect("failed to write graph")
                        })
                } else {
                    deobfuscator
                };

                let x = deobfuscator.deobfuscate().unwrap().data;
                if write_deobfuscated_files {
                    let stage3_path = make_target_filename(&target_path, "_stage3");
                    let mut stage3_file = File::create(stage3_path)?;
                    stage3_file.write_all(&magic.to_le_bytes()[..])?;
                    stage3_file.write_all(&moddate.to_le_bytes()[..])?;
                    stage3_file.write_all(stage3_data.as_slice())?;

                    let stage3_path = make_target_filename(&target_path, "_stage3_deob");
                    let mut stage3_file = File::create(stage3_path)?;
                    stage3_file.write_all(&magic.to_le_bytes()[..])?;
                    stage3_file.write_all(&moddate.to_le_bytes()[..])?;
                    stage3_file.write_all(x.as_slice())?;
                }

                if let py27_marshal::Obj::Code(code) =
                    py27_marshal::read::marshal_loads(stage3_data.as_slice()).unwrap()
                {
                    let b64_string: Vec<u8> = code.code
                        [code.code.iter().position(|b| *b == b'\n').unwrap() + 1..]
                        .iter()
                        .rev()
                        .copied()
                        .collect();

                    let stage4_data = unpack_b64_compressed_data(b64_string.as_slice())?;

                    if write_deobfuscated_files {
                        let stage4_path = make_target_filename(&target_path, "_stage4");
                        let mut stage4_file = File::create(&stage4_path)?;
                        stage4_file.write_all(&magic.to_le_bytes()[..])?;
                        stage4_file.write_all(&moddate.to_le_bytes()[..])?;
                        stage4_file.write_all(stage4_data.as_slice())?;
                    }

                    match cmd {
                        Some(Command::StringsOnly) => {
                            // Dump strings for this file
                            let pyc_filename = target_path
                                .strip_prefix(&opt.output_dir)
                                .unwrap()
                                .to_str()
                                .unwrap();

                            let path = PathBuf::from(pyc_filename);

                            let strings = unfuck::dump_strings(&path, stage4_data.as_slice())?;

                            let strings_output = strings_output.as_ref().unwrap();
                            strings.par_iter().for_each(|s| {
                                strings_output
                                    .lock()
                                    .unwrap()
                                    .serialize(s)
                                    .expect("failed to serialize output string");
                            });
                        }
                        Some(Command::ModuleMap) | None => {
                            let write_module_map = matches!(cmd, Some(Command::ModuleMap));
                            // Deobfuscate stage4
                            let deobfuscator =
                                unfuck::Deobfuscator::<Standard>::new(stage4_data.as_slice());
                            let module_map = Arc::clone(&module_map);
                            let deobfuscator = if opt.graphs {
                                deobfuscator
                                    .enable_graphs()
                                    .on_graph_generated(|name, data| {
                                        std::fs::write(name, data.as_bytes())
                                            .expect("failed to write graph")
                                    })
                            } else if write_module_map {
                                deobfuscator.on_store_to_named_var(
                                    move |code_obj, plain_modules, code_graph, store_instr, (obj, accessing_instructions)| {
                                        trace!("Found a STORE_NAME or STORE_FAST");
                                        let graph = code_graph.read().unwrap();
                                        // this is the data we're storing. where does it originate?
                                        let import_name_instr = accessing_instructions
                                            .0
                                            .lock()
                                            .unwrap()
                                            .iter()
                                            .find_map(|(source_node, idx)| {
                                                let source_instruction =
                                                    graph.instr_at(*source_node, *idx).unwrap();
                                                if source_instruction.opcode.mnemonic()
                                                    == Mnemonic::IMPORT_NAME {
                                                        Some(source_instruction)
                                                    } else {
                                                        None
                                                    }
                                            });


                                        // Does the data originate from an IMPORT_NAME?
                                        if let Some(import_name_instr) = import_name_instr {
                                            trace!(
                                                "An IMPORT_NAME preceded the STORE_NAME/STORE_FAST"
                                            );

                                                let import_name_idx =
                                                    import_name_instr.arg.unwrap() as usize;

                                                // TODO: figure out why this Arc::clone is needed and we cannot
                                                // just take a reference...
                                                let name = if store_instr.opcode.mnemonic()
                                                    == Mnemonic::STORE_FAST
                                                    && (store_instr.arg.unwrap() as usize)
                                                        < code_obj.varnames.len()
                                                {
                                                    Some(Arc::clone(
                                                        &code_obj.varnames
                                                            [store_instr.arg.unwrap() as usize],
                                                    ))
                                                } else if (store_instr.arg.unwrap() as usize)
                                                    < code_obj.names.len()
                                                {
                                                    Some(Arc::clone(
                                                        &code_obj.names
                                                            [store_instr.arg.unwrap() as usize],
                                                    ))
                                                } else {
                                                    None
                                                };

                                                if let Some(name) = name {
                                                    let obfuscated_name =
                                                        code_obj.names[import_name_idx].to_string();

                                                    if plain_modules.contains(obfuscated_name.as_str()) {

                                                    module_map
                                                        .lock()
                                                        .unwrap()
                                                        .insert(obfuscated_name, name.to_string());
                                                    }
                                                }
                                        }
                                    },
                                )
                            } else {
                                deobfuscator
                            };

                            let stage4_deob = deobfuscator.deobfuscate()?;

                            if write_deobfuscated_files {
                                let stage4_path =
                                    make_target_filename(&target_path, "_stage4_deob");
                                let mut stage4_file = File::create(&stage4_path)?;
                                stage4_file.write_all(&magic.to_le_bytes()[..])?;
                                stage4_file.write_all(&moddate.to_le_bytes()[..])?;
                                stage4_file.write_all(stage4_deob.data.as_slice())?;

                                decompile_pyc(&stage4_path, opt.decompiler.as_ref());
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
    has_next_stage: bool,
}

fn unpack_b64_compressed_data(data: &[u8]) -> Result<Vec<u8>> {
    let b64_data = std::str::from_utf8(data)?;
    let decoded_data = base64::decode(&b64_data.trim())?;

    let mut zlib_decoder = ZlibDecoder::new(decoded_data.as_slice());
    let mut inflated_data: Vec<u8> = Vec::new();
    zlib_decoder.read_to_end(&mut inflated_data)?;

    Ok(inflated_data)
}

fn decrypt_stage1(data: &[u8], opt: Arc<Opt>) -> Result<DeobfuscatedCode> {
    let mut file_reader = Cursor::new(&data);
    let magic = file_reader.read_u32::<LittleEndian>()?;
    let moddate = file_reader.read_u32::<LittleEndian>()?;

    debug!("Magic: 0x{:X}", magic);
    debug!("Mod Date: 0x{:X}", moddate);

    let obj = py27_marshal::read::marshal_loads(&data[file_reader.position() as usize..])?;
    if let py27_marshal::Obj::Code(code) = obj {
        for name in &code.names {
            debug!(
                "Name: {}",
                std::str::from_utf8(name).unwrap_or("BAD_UNICODE_DATA")
            );
        }

        let internal_filename =
            std::str::from_utf8(code.filename.as_ref()).unwrap_or("BAD_UNICODE_DATA");

        debug!("Internal file name: {}", internal_filename);

        let is_encrypted = internal_filename == "Lesta";
        let payload_to_deob = if is_encrypted {
            // If the payload is encrypted we need to to decrypt and decompress
            // the data
            let consts = if let py27_marshal::Obj::String(b) = &code.consts[3] {
                b
            } else {
                error!("{:#?}", code.consts);
                return Err(unfuck::error::Error::ObjectError::<Standard>(
                    "consts[3]",
                    code.consts[3].clone(),
                )
                .into());
            };

            debug!(
                "Internal file name: {}",
                std::str::from_utf8(code.filename.as_ref()).unwrap_or("BAD_UNICODE_DATA")
            );

            let mut decrypted_code: Vec<u8> = Vec::with_capacity(code.code.len());
            for i in 0..consts.len() {
                decrypted_code.push(code.code[i % code.code.len()] ^ consts[i])
            }

            unpack_b64_compressed_data(decrypted_code.as_slice())?
        } else {
            data[8..].to_vec()
        };

        // println!("{}", pretty_hex::pretty_hex(&&decrypted_code[0..0x20]));
        let deobfuscator = unfuck::Deobfuscator::<Standard>::new(payload_to_deob.as_slice());
        let deobfuscator = if opt.graphs {
            deobfuscator
                .enable_graphs()
                .on_graph_generated(|name, data| {
                    std::fs::write(name, data.as_bytes()).expect("failed to write graph")
                })
        } else {
            deobfuscator
        };

        let x = deobfuscator.deobfuscate().map(|deob| DeobfuscatedCode {
            original: payload_to_deob,
            deob: Some(deob.data),
            has_next_stage: is_encrypted,
        })?;

        Ok(x)
    } else {
        Err(unfuck::error::Error::ObjectError::<Standard>("root obj", obj.clone()).into())
    }
}

fn decrypt_stage2(stage2: &[u8], stage1: &[u8]) -> Result<Vec<u8>> {
    if let py27_marshal::Obj::Code(stage1_code) = py27_marshal::read::marshal_loads(stage1).unwrap()
    {
        if let py27_marshal::Obj::Code(stage2_code) =
            py27_marshal::read::marshal_loads(stage2).unwrap()
        {
            crate::smallvm::exec_stage2(stage2_code, stage1_code)
        } else {
            panic!("stage2 is not a code object?");
        }
    } else {
        panic!("stage1 is not a code object?");
    }
}

/// Runs the decompiler on the provided PYC file
fn decompile_pyc(path: &Path, decompiler: &str) {
    match std::process::Command::new(decompiler).arg(path).output() {
        Ok(output) => {
            let mut decomp_path = path.parent().unwrap().join(format!(
                "{}_decomp",
                path.file_stem().unwrap().to_str().unwrap()
            ));
            decomp_path.set_extension("py");
            let mut output_file = File::create(decomp_path).expect("failed to create deob file");

            output_file
                .write_all(output.stdout.as_slice())
                .expect("failed to write stdout");

            output_file
                .write_all(output.stderr.as_slice())
                .expect("failed to write stderr");
        }
        Err(e) => {
            error!("Could not run decompiler: {}", e);
        }
    }
}
