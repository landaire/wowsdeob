# Agent guide: wowsdeob

Deobfuscator for World of Warships Python 2.7 script files. Blog background:
https://landaire.net/world-of-warships-deobfuscation/

## Repos and roles

All are local sibling checkouts under `G:\dev` and are wired together by path:

- `wowsdeob` (this repo): CLI driver. Unwraps the staged payloads, drives the
  deobfuscator, and decompiles each module in-process with unfuck's own raising
  IR (`unfuck::ir::decompile_module`). uncompyle6 has been dropped: there is no
  longer an external decompiler subprocess or `UNFUCK_DECOMPILER` option.
- `unfuck` (`G:\dev\unfuck`): the core library. CFG (`code_graph.rs`), the
  symbolic VM (`smallvm/`), partial execution, the deobfuscation passes
  (`deob.rs`), and the new raising IR (`ir/`).
- `py-marshal` (`G:\dev\py-marshal`): Python 2.7 marshal reader. Defines `Obj`
  (the constant/value type) and `ObjHashable`. `wowsdeob`'s `Cargo.toml` patches
  `py27-marshal` to this path.
- `pickled` (`G:\dev\pickled`): standalone pickle (de)serializer with its own
  `Value`/`HashableValue` model. Not currently a dependency. Its value model is
  built around object identity/memo and a `PickleObject` instance protocol, so
  it does not share a concrete value type with py-marshal (only the scalar
  leaves overlap).

## The staged payload pipeline

A game `.pyc` is several nested layers. `main.rs` walks them:

1. Stage 1: marshalled code object. If `co_filename == "Lesta"` the body is
   XOR-encrypted with `consts[3]` then base64+zlib packed (`decrypt_stage1`).
2. Stage 2: a tiny bytecode program that, run on a small VM, XORs/swaps the real
   payload. `smallvm::exec_stage2` (in `wowsdeob/src/smallvm.rs`) finds the
   swapmap (3rd `MAKE_FUNCTION`), applies it, then executes the unpacker VM.
3. Stage 3: marshalled, deobfuscated by `unfuck`, then a base64+zlib blob is
   pulled from the reversed `co_code` tail and inflated.
4. Stage 4: the real module bytecode, obfuscated with control-flow flattening
   (basic blocks shuffled and rejoined with `JUMP_ABSOLUTE`) plus opaque
   predicates and junk. `unfuck::Deobfuscator` cleans it.

Outputs land in the `--output` dir as `<name>_stageN[_deob][_decomp]`.

## How obfuscation works and what the decompiler needs

Stage 4 obfuscation is mainly **basic-block reordering / control-flow
flattening**: the original blocks are present but shuffled, connected by
`JUMP_ABSOLUTE`, with opaque-predicate junk. `unfuck` rebuilds the CFG, removes
const conditions and dead code, and relinearizes.

Critical finding: **uncompyle6 needs the exact jumps the Python 2.7 compiler
emits**, not merely semantically-correct bytecode. The compiler terminates every
`if`/`elif` body with a jump to the merge point, even a no-op `JUMP_FORWARD 0`
when the merge is the next instruction. uncompyle6 uses those to place
`COME_FROM`s and recover structure; without them it fails with
`ParserError(..., 0)` at the first instruction. The deob's relinearization drops
these "redundant" jumps because the body falls through.

`code_graph::insert_decompiler_jumps` re-inserts them. Empirically validated
against system Python 2.7:

- A simple `if` body ending at the merge needs one trailing `JUMP_FORWARD` (a
  `JUMP_ABSOLUTE` there does NOT parse; the trailing jump must be `JUMP_FORWARD`).
- K nested `if`s closing at one merge need `K-1` `JUMP_ABSOLUTE` then one
  `JUMP_FORWARD`, all targeting the merge (the inner reachable ones are
  `JUMP_ABSOLUTE`, the outermost dead one is `JUMP_FORWARD`).
- Consecutive guards sharing a merge are one `and`-chain (count once); a guard
  whose block also holds body statements starts a new group.

This took Avatar stage 4 from 136 to 48 failing code objects. The remaining 48
are nested/converging ifs, loops (`SETUP_LOOP`/`FOR_ITER`), `try/except`
(`SETUP_EXCEPT`), and comprehensions, which local jump heuristics cannot
structure. Recovering the merge from a flattened CFG is the control-flow
structuring problem; the heuristics are inherently lossy there.

## The raising IR (the production decompiler)

`unfuck/src/ir/` is a typed, pass-based IR that structures deobfuscated bytecode
and emits Python 2.7 source directly. It is now the decompiler wowsdeob uses
(uncompyle6 is gone). Entry points: `decompile_function` for one code object,
`decompile_module` for a whole module (every nested code object, with
unrecoverable ones emitted as comments so output is always produced). Pipeline:

```
DecodedFunction -> Unstacked -> Ssa -> Simplified -> Structured -> source
```

- `expr.rs`: newtype value ids (`ValueId`/`VarId`/`NameId`/`ConstId`/`Offset`),
  an `ExprArena` of pure expressions, and the statement IR. Carrying `ValueId`s
  (not concrete `Obj`s) on the symbolic stack sidesteps the `Obj`/`ObjHashable`
  conversion friction and makes taint implicit in SSA def-use.
- `unstack.rs`: symbolic stack execution lowers a straight-line block to
  statements. Unknown opcodes return a typed `IrError` so coverage gaps surface.
- `emit.rs`: precedence-aware Python 2.7 printer.
- `mod.rs`: the typestate pipeline. Control flow currently returns
  `IrError::HasControlFlow`.

## Measuring coverage and validating changes

Coverage is measured over a corpus of deobfuscated stage-4 modules, not ad hoc
files. The dated history of every recovery and fix lives in `status-doc/`
(grouped by area); this section is the standing procedure.

Corpus:
- Canonical corpus: `G:\deob_guard\scripts` (it carries the `*_stage4.pyc`
  sources, so it is re-deobbable in place). Full regenerate source:
  `G:\deob\scripts.zip`.
- The cached `*_stage4_deob.pyc` output goes stale whenever the deobfuscator
  changes. Re-deob the corpus first (`deob_archive G:/deob_guard/scripts`)
  before measuring, or the numbers reflect an old deob.

Metrics (there are two, and they disagree on purpose):
- `honest_stats <dir>` mirrors the real `decompile_module` artifact: a module
  whose root recovers counts every nested object inlined and marker-free. This
  is the metric to optimize.
- `sweep_stats <dir>` decompiles every code object standalone via
  `decompile_function`, which wraps each in a `def`. It MISMEASURES module roots
  (`import *`, `from __future__`) and class bodies, so treat it as a
  panic/regression check, not the coverage number.
- `probe_agg <dir> [signature]` bins the failure buckets by marker context when
  you need to find the next lever.

Before trusting any number, rebuild ALL examples (`cargo build --release
--examples`), never a single `--example`. A partial rebuild can leave a reverted
change compiled into one binary while you measure with another -- that is what
past "non-determinism" always turned out to be. The deob and IR are
deterministic on a fixed corpus.

Validating a deobfuscator change (the deob feeds every object, so a bad change
is high blast radius): re-deob the whole corpus, dump the IR before and after,
diff in isolation (snapshot old-deob IR, re-deob, diff), and confirm zero
per-object regressions and zero new recompile failures before landing. For
IR/decompiler changes, recompile the output under Python 2.7 and run the
snapshot/unit suites (`cargo test --test corpus --test ir_m1`).

## Environment and tooling

Do NOT touch global Python state (no `pip install` into system Python). Use an
isolated `uv` venv if you need third-party packages. Keep scratch work in a
wipeable temp dir on `G:\` (e.g. `G:\tmp\...`):

- `C:\Python27\python2.exe`: system Python 2.7, used READ-ONLY to compile
  reference source and validate decompiled output. Never install into it.
- Helper scripts in `G:\wowsdeob_tmp` (recreate as needed):
  - `probe.py <pyc>`: recursively try to decompile every code object, report
    OK/FAIL with the parse error. The fastest signal for "did the fix help."
  - `toks.py <pyc> <name>`: dump uncompyle6 scanner tokens (with COME_FROMs) for
    a named code object.
  - `asm2.py <variant>`: assemble py2.7 code objects to test exactly which jump
    shapes uncompyle6 accepts. The `pydisasm` in the venv disassembles pyc files.

Sample input: `E:\WoWsStable\World_of_Warships\bin\11791718\res\scripts.zip`.
The committed `output/Avatar.pyc` is a raw stage-1 file usable as direct input.

## Build and run

```
cargo build --release
./target/release/wowsdeob.exe output/Avatar.pyc <out_dir>
./target/release/wowsdeob.exe <scripts.zip> <out_dir>
```

Each module is deobfuscated and decompiled in-process; the recovered Python is
written next to the stage-4 `.pyc` as `*_stage4_deob.py`. There is no external
decompiler to configure.

The py-marshal `Mutex`->`RwLock` migration (py-marshal 0.5) is complete, and full
32-thread runs over the whole `scripts.zip` now complete without the old
intermittent rayon deadlock. If a hang with near-zero CPU ever recurs, run with
`RAYON_NUM_THREADS=1` to confirm it is a lock race and bisect from there.

## Known tech debt

- The in-tree `#[cfg(test)]` modules in `unfuck` (`smallvm/mod.rs`,
  `code_graph.rs`, `deob.rs`) still call `.lock()` and construct `Mutex::new`
  for `Obj`, so `cargo test --lib` does not compile. New tests go in
  `unfuck/tests/` (integration tests build against the public API and skip those
  modules). Finishing that migration is a separate cleanup.
- The current `insert_decompiler_jumps` group-counting heuristic underfires on
  Avatar (never produces a group count > 1 there); the structuring pass will
  supersede it, after which it and `if_group_count` should be deleted.

## Conventions

These are the standing rules for working in this workspace. Follow them without
being re-asked.

Version control:
- Commit with `jj` (Jujutsu), never raw `git`. Use conventional-commit subjects
  (`feat:`, `fix:`, `refactor:`, `docs:`, `build:`, ...). Keep one concern per
  commit; `jj split <paths> -m ...` to separate mixed working-copy changes.
- Do NOT add `Co-Authored-By` trailers or any other AI/agent attribution.
- No "milestone" labels or other LLM artifacts anywhere: not in commit messages,
  code comments, file names, or docs.
- Avoid interactive commands (no `-i` flags, no editor-driven `jj`/`git`).

Code style:
- Prefer newtypes (e.g. `ValueId`, `Offset`, `NameId`) over bare integers, and
  typestate (consuming-stage pipelines like `DecodedFunction -> StructuredFunction`)
  over flag-checked mutable state.
- Match the surrounding code's idiom, naming, and comment density. Comments
  explain *why*, not *what*.
- No LLM-style comments: no section-divider banners, no em/en dashes, no unicode
  arrows. Use plain ASCII (`->`, `--`).
- Do not introduce unverified default or fallback values. A fallback is only
  acceptable when the fallback itself is verified correct for the case; otherwise
  fail loud (typed error, explicit skip with a logged reason) rather than guess.
- When a path must tolerate bad input, skip it explicitly and gracefully rather
  than `panic!`/`unwrap()` on it (see `ParsedInstr::get`). Goal: no panics on any
  archive input.

Python and environment:
- Do NOT touch global Python state: no `pip install` into system Python. Use an
  isolated `uv` venv. `C:\Python27\python2.exe` is used READ-ONLY to compile
  reference source and to validate decompiled output (`py_compile`).
- Keep scratch work in a wipeable temp dir on `G:\` (e.g. `G:\tmp\...` or
  `G:\wowsdeob_tmp`); never write throwaway files into the repos.

Testing and fixtures:
- Never commit game `.pyc` files. Test fixtures are our own `.py` compiled with
  Python 2.7 (`tests/fixtures/cases.py` -> `cases.pyc`).
- Validate decompiler changes by recompiling output under Python 2.7 and by the
  snapshot/unit suites (`cargo test --test corpus --test ir_m1`). Rerun
  `sweep_stats`/`sweep_deob` over the archive to catch coverage or panic
  regressions.
- Do adversarial review of your own changes at the end of each step before
  moving on.
