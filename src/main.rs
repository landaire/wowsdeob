use std::collections::HashMap;
use std::fs::File;
use std::io::Cursor;
use std::io::Read;
use std::io::Write;
use std::path::Path;
use std::path::PathBuf;
use std::sync::Arc;
use std::sync::Mutex;
use std::sync::atomic::AtomicUsize;
use std::sync::atomic::Ordering;

use anyhow::Result;
use log::debug;
use log::error;
use log::trace;
use memmap::MmapOptions;
use pydis::opcode::Opcode;
use pydis::opcode::py27::Mnemonic;
use pydis::opcode::py27::Standard;
use rayon::iter::IntoParallelRefIterator;
use rayon::iter::ParallelIterator;
use structopt::StructOpt;
use unfuck::Deobfuscator;
use wowsdeob::stage::Stage1;

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

    /// Write only the final stage4 artifact per input, skipping every intermediate
    /// stage dump: the recovered Python source (`.py`) when stage4 decompiles 100%,
    /// otherwise the deobfuscated stage4 bytecode (`.pyc`) for further work.
    #[structopt(long = "final-only")]
    #[cfg(not(feature = "reduced_functionality"))]
    final_only: bool,

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

fn dump_pyc(
    decompressed_file: &[u8],
    target_path: &Path,
    strings_output: Option<Arc<Mutex<csv::Writer<std::fs::File>>>>,
    opt: Arc<Opt>,
    module_map: Arc<Mutex<HashMap<String, String>>>,
) -> Result<bool> {
    let cmd = opt.cmd.as_ref();
    // In final-only mode we emit just one artifact per input (the recovered `.py` or
    // the stage4 `.pyc`), so suppress every intermediate stage dump.
    let final_only = opt.final_only && cmd.is_none();
    let write_deobfuscated_files = (cmd.is_none() || opt.dry) && !final_only;

    let stage1 = match Stage1::parse(decompressed_file) {
        Ok(stage1) => stage1,
        Err(e) => {
            error!("Error decrypting stage1: {}", e);
            return Ok(false);
        }
    };
    let header = stage1.header().to_bytes();

    let payload_deob = match stage_deobfuscator(stage1.payload(), opt.graphs).deobfuscate() {
        Ok(deob) => deob.data,
        Err(e) => {
            error!("Error decrypting stage1: {}", e);
            return Ok(false);
        }
    };

    if write_deobfuscated_files {
        let mut original_file = File::create(target_path)?;
        original_file.write_all(decompressed_file)?;

        let stage2_path = make_target_filename(target_path, "_stage2");
        let mut stage2_file = File::create(stage2_path)?;
        stage2_file.write_all(&header)?;
        stage2_file.write_all(stage1.payload())?;

        let stage2_path = make_target_filename(target_path, "_stage2_deob");
        let mut stage2_file = File::create(stage2_path)?;
        stage2_file.write_all(&header)?;
        stage2_file.write_all(payload_deob.as_slice())?;
    }

    let Stage1::Encrypted(stage2) = stage1 else {
        return Ok(true);
    };

    let stage3 = stage2.execute()?;
    let stage3_data = stage3.bytes();
    if write_deobfuscated_files {
        let _ = std::fs::write(
            make_target_filename(target_path, "_stage3_raw"),
            stage3_data,
        );
    }
    debug!(
        "stage3_data: len={}, first4={:02x?}, last4={:02x?}",
        stage3_data.len(),
        &stage3_data[..stage3_data.len().min(4)],
        &stage3_data[stage3_data.len().saturating_sub(4)..],
    );

    let stage3_deob = stage_deobfuscator(stage3_data, opt.graphs)
        .deobfuscate()?
        .data;
    if write_deobfuscated_files {
        let stage3_path = make_target_filename(target_path, "_stage3");
        let mut stage3_file = File::create(stage3_path)?;
        stage3_file.write_all(&header)?;
        stage3_file.write_all(stage3_data)?;

        let stage3_path = make_target_filename(target_path, "_stage3_deob");
        let mut stage3_file = File::create(stage3_path)?;
        stage3_file.write_all(&header)?;
        stage3_file.write_all(stage3_deob.as_slice())?;
    }

    let stage4_data = stage3.extract_stage4()?;
    if write_deobfuscated_files {
        let stage4_path = make_target_filename(target_path, "_stage4");
        let mut stage4_file = File::create(&stage4_path)?;
        stage4_file.write_all(&header)?;
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
            let deobfuscator = Deobfuscator::<Standard>::new(stage4_data.as_slice());
            let module_map = Arc::clone(&module_map);
            let deobfuscator = if opt.graphs {
                deobfuscator
                    .enable_graphs()
                    .on_graph_generated(|name, data| {
                        std::fs::write(name, data.as_bytes()).expect("failed to write graph")
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

            if final_only {
                // Keep the recovered source only when stage4 decompiles
                // 100%; otherwise keep the deobfuscated stage4 bytecode as
                // a real .pyc (magic + moddate header) for further work.
                if let py27_marshal::Obj::Code(root) =
                    py27_marshal::read::marshal_loads(stage4_deob.data.as_slice())?
                {
                    // `decompile_module_body_ok` reports whole-module
                    // recovery (every nested object inlined without an
                    // `__unrecovered__` marker); only then is the emitted
                    // source faithful enough to keep as .py.
                    let fully_recovered = unfuck::ir::decompile_module_body_ok(Arc::new(
                        root.read().unwrap().clone(),
                    ));
                    if fully_recovered {
                        let source = unfuck::ir::decompile_module(&root);
                        let decomp_path = target_path.with_extension("py");
                        std::fs::write(&decomp_path, source)?;
                    } else {
                        let mut pyc_file = File::create(target_path)?;
                        pyc_file.write_all(&header)?;
                        pyc_file.write_all(stage4_deob.data.as_slice())?;
                    }
                }
            }

            if write_deobfuscated_files {
                let stage4_path = make_target_filename(target_path, "_stage4_deob");
                let mut stage4_file = File::create(&stage4_path)?;
                stage4_file.write_all(&header)?;
                stage4_file.write_all(stage4_deob.data.as_slice())?;

                // Decompile the deobfuscated module with our own IR
                // decompiler and write the recovered Python source beside
                // the .pyc. Each code object that cannot be recovered is
                // emitted as a comment, so output is always produced.
                if let py27_marshal::Obj::Code(root) =
                    py27_marshal::read::marshal_loads(stage4_deob.data.as_slice())?
                {
                    let source = unfuck::ir::decompile_module(&root);
                    let decomp_path = stage4_path.with_extension("py");
                    std::fs::write(&decomp_path, source)?;
                }
            }
        }
    }

    Ok(true)
}

fn stage_deobfuscator(data: &[u8], graphs: bool) -> Deobfuscator<'_, Standard> {
    let deobfuscator = Deobfuscator::<Standard>::new(data);
    if !graphs {
        return deobfuscator;
    }

    deobfuscator
        .enable_graphs()
        .on_graph_generated(|name, data| {
            std::fs::write(name, data.as_bytes()).expect("failed to write graph")
        })
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
                        // Isolate each file: a panic deep in the deobfuscator (a bad
                        // instruction, an unhandled shape) must skip that one file, not
                        // abort the whole archive.
                        let res = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
                            dump_pyc(
                                decompressed_file.as_slice(),
                                &target_path,
                                csv_output,
                                Arc::clone(&opt),
                                Arc::clone(&module_map),
                            )
                        }))
                        .unwrap_or_else(|_| {
                            error!("panic while deobfuscating {}; skipped", file_name);
                            Ok(false)
                        });
                        if matches!(res, Ok(true)) {
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
        let module_map = module_map.lock().unwrap();
        let serialized_data =
            serde_json::to_string_pretty(&*module_map).expect("failed to serialize module_map");
        std::fs::write(target_path, serialized_data.as_bytes())?;
    }

    println!("Extracted {} files", file_count.load(Ordering::Relaxed));

    Ok(())
}
