# wowsdeob

A deobfuscator for World of Warships script files.

## Current Status

Deobfuscation:

- [x] Unpacking stage 1 Python files automatically
- [x] Unpacking stage 2 Python files automatically
- [x] Unpacking stage 3 Python files automatically
- [x] Unpacking stage 4 Python files automatically
- [x] Removing const predicates
- [x] Removing garbage instructions
- [x] Deoptimizing returns
- [ ] Stack reordering

A blog post covering the techniques in this application can be found here: [https://landaire.net/world-of-warships-deobfuscation/](https://landaire.net/world-of-warships-deobfuscation/).

Most Python VM instructions are supported with the exception of some that mutate lists, dicts, or other data types

Right now this tool can deobfuscate many of the game files. There are still some that do not cleanly deobfuscate and cause issues with the decompiler that will need work. There are also some cases where the deobfuscator enter an infinite loop or take a very, very long time. Please do not file an issue for these files unless you have done work to figure out what the gaps are or what is causing the decompiler to trip up.

## Installation

### Prebuilt Windows binary

Each tagged release attaches `wowsdeob_<version>_win64.zip` to the [Releases](https://github.com/landaire/wowsdeob/releases) page. Download it and extract `wowsdeob.exe`.

### Nix

This repository is a Nix flake, so you can run or install it without a local Rust toolchain.

Run it directly:

```
nix run github:landaire/wowsdeob -- file.pyc ./output
```

Get a shell with `wowsdeob` on `PATH`:

```
nix shell github:landaire/wowsdeob
```

Build the binary (lands at `./result/bin/wowsdeob`):

```
nix build github:landaire/wowsdeob
```

Develop against a local checkout:

```
nix develop
cargo build --release
```

## Prerequisites

In order to use this application you will probably want the following:

- Python 2.7 in your `$PATH`
- `uncompyle6` installed (`pip install uncompyle6`) for automatic decompilation.

## Usage

The general usecase will be:

```bash
$ wowsdeob file.pyc ./output
```

This will create multiple files in the `./output` directory. The one you're likely looking for is `./file_stage4_deob_decomp.py`

If you are looking for a specific file and aren't sure where it is, the `strings-only` command will probably be useful:

```bash
$ wowsdeob scripts.zip ./output strings-only
```

This will create a `strings.csv` file containing all constant strings, varnames, etc. from all game scripts.

The `constants` command writes the game's `constants.json` for a build. It runs the client scripts in an emulated Python 2.7, so you do not need Python installed. Point it at a game install to read its newest build, or pass `--build`:

```bash
$ wowsdeob /path/to/World_of_Warships ./output constants --build 13533378
```

It also takes a build's `scripts.zip`, with `--build` naming that build and `--executable` pointing at that build's `bin64/WorldOfWarships64.exe`. Current clients need the executable, since it tells which native modules the client links in. The emulated interpreter never reads files, opens sockets or starts processes on your machine. Libraries can use the same extraction through the `constants` cargo feature, without the CLI's dependencies.

Full output of `--help`:

```
wowsdeob 0.1.0
WoWs scripts deobfuscator

USAGE:
    wowsdeob [FLAGS] <input> <output-dir> [SUBCOMMAND]

FLAGS:
        --dry           Dry run only -- do not write any files
        --final-only    Write only the final stage4 artifact per input, skipping every intermediate stage dump: the
                        recovered Python source (`.py`) when stage4 decompiles 100%, otherwise the deobfuscated stage4
                        bytecode (`.pyc`) for further work
    -g                  Enable outputting code graphs to dot format
    -h, --help          Prints help information
    -q                  Disable all logging
    -V, --version       Prints version information
    -v                  Enable verbose logging

ARGS:
    <input>         Input file. This may be either a `scripts.zip` file containing many obfuscated .pyc files, or
                    this argument may be a single .pyc file. The `constants` command also takes a game install
                    directory
    <output-dir>    Output directory

SUBCOMMANDS:
    constants       Write constants.json for a game build by running its client scripts. The input is a game install
                    directory or a build's scripts.zip
    help            Prints this message or the help of the given subcommand(s)
    module-map      
    strings-only    
```

Example:

```bash
wowsdeob ./scripts.zip ./decrypted_scripts
```

## Credits

Thanks to lpcvoid for their blog documenting the decryption process: https://lpcvoid.com/blog/0007_wows_python_reversing/index.html

Thank you to folks from the WoWs Datamining Discord for helping with research and testing:

- notyourfather
- TTaro
- Trackpad
- Scout1Treia
- 901234
- EdibleBug

My friend @gabe_k for helping early on with looking at the files and providing assistance with pyasm.

## License

Licensed under either of [Apache License, Version 2.0](LICENSE-APACHE) or [MIT license](LICENSE-MIT) at your option.