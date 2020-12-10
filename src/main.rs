use memmap::MmapOptions;
use std::fs::File;
use std::io::prelude::*;
use std::io::{BufReader, Cursor};
use std::path::{Path, PathBuf};
use structopt::StructOpt;
use byteorder::{LittleEndian, ReadBytesExt};

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

fn main() -> std::io::Result<()> {
    let opt = Opt::from_args();
    let file = File::open(opt.input)?;
    let mmap = unsafe { MmapOptions::new().map(&file)? };

    let mut reader = Cursor::new(&mmap);

    let mut zip = zip::ZipArchive::new(reader)?;

    for i in 0..zip.len() {
        let mut file = zip.by_index(i)?;
        let file_name = file.name();
        println!("Filename: {:?}", file.name());

        let file_path = match file.enclosed_name() {
            Some(path) => path,
            None => {
                eprintln!("File `{:?}` is not a valid path", file_name);
                continue;
            }
        };
        let target_path = opt.output_dir.join(file_path);
        if file.is_dir() {
            std::fs::create_dir_all(&target_path.parent().unwrap())?;
            continue;
        }
        
        if !file_path.ends_with("constants.pyc") {
            continue;
        }

        let mut decompressed_file = Vec::with_capacity(file.size() as usize);
        file.read_to_end(&mut decompressed_file)?;
        let mut file_reader = Cursor::new(&decompressed_file);
        let magic = file_reader.read_u32::<LittleEndian>()?;
        let moddate = file_reader.read_u32::<LittleEndian>()?;

        println!("0x{:X}", magic);
        println!("0x{:X}", moddate);

        println!("{:X?}", &decompressed_file[8..8+0x10]);

        println!("{:?}", py_marshal::read::marshal_loads(&decompressed_file[file_reader.position() as usize..]));
        //println!("{:?}", pyo3::marshal::loads(gil.python(), &decompressed_file[file_reader.position() as usize..]));
        return Ok(());
    }

    println!("Hello, world!");

    Ok(())
}
