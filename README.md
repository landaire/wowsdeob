# wowsdeob

(soon to be a) deobfuscator for World of Warships script files.

## Current Status

Currently this project supports reading a `scripts.zip` file and will write the decrypted `.pyc` file to the specified output directory

## Usage

```
wowsdeob 0.1.0
WoWs scripts deobfuscator

USAGE:
    wowsdeob [FLAGS] <input> <output-dir>

FLAGS:
    -d, --debug      Enable debug logging
    -h, --help       Prints help information
    -V, --version    Prints version information

ARGS:
    <input>         Input file
    <output-dir>    Output directory
```

Example:

```bash
wowsdeob ./scripts.zip ./decrypted_scripts
```