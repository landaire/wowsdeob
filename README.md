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

Full output of `--help`:

```
wowsdeob 0.1.0
WoWs scripts deobfuscator

USAGE:
    wowsdeob [FLAGS] [OPTIONS] <input> <output-dir> [SUBCOMMAND]

FLAGS:
        --dry        Dry run only -- do not write any files
    -g               Enable outputting code graphs to dot format
    -h, --help       Prints help information
    -q               Disable all logging
    -V, --version    Prints version information
    -v               Enable verbose logging

OPTIONS:
        --decompiler <decompiler>    Your favorite Python 2.7 bytecode decompiler. This program assumes the decompiler's
                                     first positional argument is the file to decompile, and it prints the decompiled
                                     output to stdout [env: UNFUCK_DECOMPILER=]  [default: uncompyle6]

ARGS:
    <input>         Input file. This may be either a `scripts.zip` file containing many obfuscated .pyc files, or
                    this argument may be a single .pyc file
    <output-dir>    Output directory

SUBCOMMANDS:
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