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

Status: decompiles 346/348 Avatar code objects from scratch, including functions
uncompyle6 cannot (e.g. getDriftAngle). Every decompiled function is verified to
compile under Python 2.7 (see validation below); anything not fully recoverable
returns a typed error rather than wrong or invalid source. Done: branch-free
lowering, if/else via post-dominators, while and for loops (including tuple
targets) via back-edge/natural-loop detection, break/continue (BREAK_LOOP/
CONTINUE_LOOP), raise, deref vars, keyword and splat call arguments, tuple
assignment, dict literals, short-circuit and/or, ternaries (POP_JUMP_IF_FALSE and
the negated POP_JUMP_IF_TRUE form), augmented assignment (name/attr/subscript via
INPLACE + ROT_TWO/ROT_THREE) and chained-comparison rotations, two- and
three-element parallel assignment (`t1, t2 = v1, v2` via ROT_TWO; `t1, t2, t3 =
v1, v2, v3` via ROT_THREE then ROT_TWO -- recovered as one tuple assignment so an
aliasing swap is never mis-ordered), the `print` statement (PRINT_ITEM/PRINT_NEWLINE,
with trailing-comma suppression), slices and del
(SLICE_*/STORE_SLICE_*/DELETE_*), default arguments, closures (LOAD_CLOSURE/
MAKE_CLOSURE), nested defs, lambdas (any inline MakeFunction never bound by a
STORE, whose body is a single return, rendered as `lambda args: expr` -- the name
is not relied on since the obfuscator rewrites `<lambda>` to a numeric one;
recovered as positional and keyword call arguments, e.g. `sort(key=lambda p: p[0])`,
and when bound to a name), decorated defs (the `name = deco(...(make_function))`
shape, matched to the store target through the deobfuscator's `_orig_<id>` rename
suffix and emitted as `@deco` + `def`), imports including `import a.b as c` (the
LOAD_ATTR-into-submodule shape, lowered by walking the attribute chain down to the
imported module), try/except, the comprehension family (generator expressions and
set/dict/list
comprehensions), imports, classes, docstrings, and identifier sanitization. A
post-structuring cleanup prunes unreachable statements and redundant loop-tail
`continue`s. The 346 recovered objects contain zero `__unrecovered__` markers, and
the concatenated `--dump` of all 348 parses as one module. The two failures are
standalone `<dictcomp>`/`<setcomp>` code objects, correctly rejected (only valid
inlined). The Avatar module body decompiles in full -- every class,
method, comprehension, and nested construct inlined -- to a 3653-line source with
zero `__unrecovered__` that compiles as a Python 2.7 module. Avatar.pyc is
completely recovered. ArtilleryGun.pyc (the gun dispersion / hoopRanging code) is
likewise fully recovered, 55/55. Across the 27 stage-4 modules deobfuscated so far the
IR recovers 1050/1102 code objects (~95%), 15 of them fully; comprehensions are folded
even when the obfuscator rewrites the `<dictcomp>`/`<setcomp>`/`<genexpr>`/`<lambda>`
co_name to a number, since these are detected by structure (the `.0` argument and the
GENERATOR flag) rather than name.

Full-archive status, measured by `sweep_stats` over a clean run (all 5093 files of
scripts.zip): the IR decompiles **93.3% of 93391 code objects** with **zero panics**
in either the deobfuscator or the IR, at ~1.1GB peak across 32 threads (no OOM).
Measure on a freshly-written output directory: `*_stage4_deob.pyc` are
overwritten by name, so a directory reused across different binary builds
accumulates a stale, inflated mix (one such dir read 123k objects at 94%). A clean
run is deterministic -- two clean 32-thread runs produce byte-identical counts.

Merge-less try/except/with/finally (body always raises or returns, so the deob drops
the unreachable `POP_BLOCK; JUMP merge` body exit) is now recovered: `recover_try`
carries the merge as `Option` (`None` = no merge of its own; its handlers follow the
enclosing region's stop, so a falling-through handler absorbs only the post-try code
bounded at that stop). Merge-less try/except is rejected when the code object
contains any SETUP_FINALLY/SETUP_WITH, because the relinearizer scatters the
protected region and a handler falling through into an enclosing finally/with cleanup
would double-emit it (the finally/with structurer also emits it); objects with
neither cannot enclose. `recover_with`/`recover_finally` keep the merge (derived from
the cleanup/END_FINALLY, not the body POP_BLOCK) and simply make the POP_BLOCK
optional. This took the archive 92.7 -> 93.3% (SETUP_EXCEPT 585 -> 229, SETUP_WITH
525 -> 463, SETUP_FINALLY 455 -> 334), validated by recompiling thousands of the
newly-recovered functions under Python 2.7 and two adversarial review passes.

The biggest remaining buckets, in order: `construct only partially recovered` (a
parent fails when any nested object does, so it shrinks as leaf gaps close, ~2965),
`symbolic stack underflow` (~533) and `cfg did not reduce to regions` (~513, mostly
deob residue and irreducible CFGs), the non-merge-less try/with/finally shape
variants (SETUP_WITH/SETUP_FINALLY/END_FINALLY/SETUP_EXCEPT, the harder cases left
after merge-less), IMPORT_FROM (~202)/BUILD_CLASS (~188)/STORE_MAP (~130) cross-block
residue (producer and consumer split across blocks by the deob, underflowing the
block-at-a-time unstacker), `instruction operand out of range` (~143), and
cross-block short-circuit (JUMP_IF_FALSE_OR_POP as a block terminator, ~100). A known
emit bug: a binary operator with a `not`/low-precedence operand is emitted without
parentheses (`'%d' % not x`), which is a Python 2.7 SyntaxError.

Key finding for whoever pushes coverage further: the remaining gaps are a mix of
genuine feature gaps and **deobfuscation residue**, and the only reliable way to
tell them apart is to disassemble the failing example (`dis_one.py`/`dis_all.py`
in the scratch dir) and compare against a clean compile of the same construct. A
gap that looks like residue can be a real feature: the bulk of the
`UNPACK_SEQUENCE` failures turned out to be inline list comprehensions with a
tuple target (`[e for a, b, c in it]`), a clean win once folded. The residue
cases are the obfuscator interleaving live code the deob does not fully strip: a
second `IMPORT_FROM` whose module is buried under unrelated pushes, a dead
`LOAD; LOAD; INPLACE_ADD` on the stack just before a `BUILD_CLASS`, a dict literal
(`STORE_MAP`) whose values span blocks. Those underflow or confuse the
block-at-a-time unstacker; the high-leverage fix for them is deob-side (dead
stack-computation elimination so the regions come out clean). Done this session
as clean wins (each with a corpus snapshot and a Python 2.7 recompile check):
BUILD_SLICE (extended slices), EXEC_STMT (all three `exec` forms), nested unpack
targets (`(a, b), c = ...`), `print >>f` (PRINT_ITEM_TO/PRINT_NEWLINE_TO), and
inline list comprehensions with a tuple target. Standalone comprehension code
objects, and nested list comprehensions (two LIST_APPENDs), are not folded.

An IR deobfuscation engine (ir/simplify.rs) constant-folds opaque-predicate
branches: a forward constant-propagation dataflow (sound at joins/loops) resolves
conditions, a folded CondBranch becomes an unconditional Jump, and the structurer
emits only reachable blocks, so guarded junk is dropped with no instruction removal
(and so no over-removal, unlike the bytecode deob's remove_const_conditions). A
block that will not lower becomes a poison dead-end (Block::poison) that is pruned
if unreachable and only errors if actually reached. This is a no-op on the
already-deobfuscated corpus.

The bridge for running the IR on raw obfuscated input exists as Deobfuscator's
`minimal` mode (lib.rs/deob.rs): it decodes and fixes basic blocks but skips
remove_const_conditions and the uncompyle6 jump insertion. The `minimal_deob`
example writes a loadable pyc from it. The experiment is conclusive and negative:
the IR decompiles only 94/348 of minimal output (vs 333/348 full), because its
symbolic execution clears the stack at each block boundary (`start_block`) and
walks blocks in offset order, so control-flow flattening's dispatch and reordered
layout underflow the stack before `simplify` can fold the opaque predicates. Folding
on the IR cannot replace bytecode-level un-flattening without CFG-driven stack
propagation. processConsoleCommand is genuinely corrupted by the full deob (a taint
over-removal strips its call/unpack and leaves JUMP_ABSOLUTE into mid-instruction),
which the IR correctly rejects rather than mis-emitting.

Short-circuit and ternaries are recovered inside a single block by an offset-keyed
pending stack (see unstack.rs and the find_ternaries pre-pass in cfg.rs) rather
than by a general stack dataflow. try/except is recovered by a find_ternaries-style
pre-pass in cfg.rs (recover_tries) that pattern-matches the SETUP_EXCEPT region:
the body and each handler become a Terminator::Try whose body and handler arms
converge at the merge (so the existing dominator structurer treats it like a
diamond), while the handler dispatch (DUP_TOP/COMPARE exception-match/POP_JUMP
chain), the exception triple pops, the `as name` binding, and every END_FINALLY are
recovered into HandlerArms and excluded from blocks. Comprehensions: YIELD_VALUE
lowers to Expr::Yield; a <genexpr>/<setcomp>/<dictcomp> code object is decompiled
(set/dict via an accumulator-aware comp lowering mode that keeps the leading
BUILD off the stack and turns SET_ADD/MAP_ADD into element statements), folded by
recognize_comprehension in emit.rs into element-plus-clauses, and inlined at the
MAKE_FUNCTION + GET_ITER + CALL_FUNCTION 1 call site; inline list comprehensions
(LIST_APPEND, no separate code object) are folded in place by find_list_comps +
parse_list_comp into one Expr::ListComp. Only clean CPython 2.7 shapes are
accepted; anything else rejects the function. Imports (IMPORT_NAME/IMPORT_FROM/
IMPORT_STAR) lower to Stmt::Import/FromImport with raw (dotted) module and
attribute names; classes (BUILD_CLASS) lower to Stmt::ClassDef whose body is the
class-body code object decompiled with the `__module__ = __name__` boilerplate and
trailing `return locals()` dropped. Default values are rendered in the enclosing
scope and injected into the nested signature; closures drop the capture tuple (the
capture is implicit in source). Augmented assignment lowers INPLACE_* to a distinct
Expr::Inplace so a store back to the same operand recovers `x op= y` (round-trips to
INPLACE_*, not BINARY_*); a true simultaneous assignment (`a, b = b, a`) matches no
recognised ROT pattern and is rejected rather than mis-emitted.

Compound `and`-chain ternary conditions (`X = A if c1 and c2 else B`) are folded by
extending find_ternaries backward over the chain's POP_JUMPs so the diamond stays in
one block. Chained comparisons (`a < b < c`) are recovered when stored: the DUP_TOP
makes the middle operand a shared value, so the short-circuit yields `cmp1 and cmp2`
with that operand shared, find_chained_comparisons overrides the short-circuit merge
past the ROT_TWO/POP_TOP cleanup, and an emit peephole renders the chained form only
when the operand is literally shared (so it round-trips faithfully).

Remaining failures (`decompile_one --stats`): just two false negatives, the
standalone `<dictcomp>`/`<setcomp>` code objects, correctly rejected (only valid
inlined; they are recovered at their inline use sites). Every real method is
recovered. The chain that got here: vehicleInsideSelection (returned
chained-comparison-and) -- at a RETURN with short-circuit operators still pending,
fold them into the returned value (force_resolve_shortcircuits); the unreachable
false-exit blocks are pruned. _processChatMessage was the last real method, with two
distinct issues: (a) its typed `except Exception as e: ... return None` handler
RETURNS instead of converging, defeating post-dominance for the enclosing if -- FIXED
by computing post-dominators over normal (non-exceptional) flow
(Block::normal_successors: a Try reaches only its body); (b) a list comprehension as
a ternary then-arm, `[f(x) for x in d['k']] if 'k' in d else []`, where the else arm
sits between the comp back-edge and the FOR_ITER exit (the ternary merge) -- FIXED by
locating the back-edge by scanning, marking the condition a ternary so the diamond
stays in one block, folding the comp, and making the folded ListComp the diamond's
then with the FOR_ITER exit as the merge (set_comp_ternary_then; the comp stands in
for the JUMP_FORWARD an ordinary ternary uses). Recovering it cascaded into the
PlayerAvatar class body and the module body. The Avatar module body now decompiles in
full (3653 lines, zero `__unrecovered__`, compiles as a Python 2.7 module). (2) processConsoleCommand is now FULLY RECOVERED; it
took a chain of four deob fixes, each a distinct soundness bug exposed by the next:
(a) remove_const_conditions taint over-removal -- the access tracker shares its Arc
and accumulates the full transitive history, so a folded opaque predicate's removal
set was polluted with live instructions from other blocks (it had stripped this
function's `cmdCode, cmdInfo, errorInfo = validateAndParseCmd(...)` call and unpack);
now only the folded jump's local in-block condition slice is removed, cross-block taint
is left in place. (b) join_block re-added a merged block's outgoing edges by a stale
start_offset lookup; now by stable NodeIndex. (c) node removal used an execution-
coverage heuristic that dropped live unwalked blocks; now reachability-from-root. (d)
the decisive one -- the empty-block cleanup. When the opaque predicate folds, its
condition block is emptied (the whole block was the condition slice). The cleanup
removed the empty block by `join_block(empty, child)`, merging its single child IN and
deleting the child, which silently dropped the child's OTHER predecessors. Here the
child was a forwarding block (`JUMP_FORWARD 0` -> `return cmdStartsWithSlash`) shared by
the folded condition AND the `addBan`/`removeBan` jumps, so those jumps lost their
successor; ensure_terminal_returns then appended a spurious `return None` after the now-
orphaned jump and write_bytecode emitted the stale jump, landing inside the reassembled
`LOG_INFO` call (a stack underflow). Fix: splice the empty block out -- redirect its
predecessors straight to its single child, then drop it -- so the child keeps all its
edges. Each fix was byte-identical on the rest of Avatar; the chain took the count
335 -> 336 with addBan/removeBan correctly flowing to `return cmdStartsWithSlash`. A
fifth deob fix (fixup_fallthrough_jumps) then recovered drawProjectileTraces (336 ->
337): the relinearizer can place a block whose fall-through (NonJump) successor is not
physically adjacent -- e.g. a ternary else arm laid out after its merge -- so without
a jump the block falls into the wrong instruction. The pass appends an explicit
JUMP_ABSOLUTE to any non-jump-terminated block whose fall-through target is not the
next block. (A principled alternative -- deferring a block in update_bb_offsets until
its fall-through predecessor is placed -- was tried and regressed badly (337 -> 313):
the layout heuristic's invariants do not tolerate it.) (3) The reordered nested
ternary is now FIXED in the IR (find_reordered_ternaries, 337 -> 338, recovered
cacheGunsState). fixup_fallthrough makes the bytecode valid but non-contiguous -- the
else arm sits after the merge and jumps back to it -- which the offset-based
find_ternaries cannot fold. find_reordered_ternaries detects the shape (POP_JUMP whose
then arm is pure and ends in JUMP_FORWARD to an immediately-following merge, and whose
else arm is pure, after the merge, rejoining it), marks the diamond jumps so the cond
block absorbs the merge, excludes the else arm from block formation, and feeds the else
arm's value instructions at the merge -- just before resolve_pending -- so the existing
in-block ternary folding applies. receiveDamageReport (same ternary, plus a bare-except
try inside a for loop) is now FULLY recovered: recover_try no longer assumes the body
exit `POP_BLOCK; JUMP end` sits immediately before the handler (the relinearizer can put
post-try code and the ternary else arm between them, and can place the merge before the
handler entirely). It locates the body's POP_BLOCK by scanning the body with block-nesting
depth and reads the merge from the jump after it; the END_FINALLY scan is clamped to a
forward span. A standalone class body decompiled on its own now renders its trailing
`return locals()` (LOAD_LOCALS) as the builtin instead of __unrecovered__.
(4) ROT_TWO/ROT_THREE simultaneous assignment is deliberately
rejected (ambiguous). Standalone <genexpr>/<setcomp>/<dictcomp> objects are correctly
rejected (only valid inlined). The module body and the Avatar/PlayerAvatar class
bodies are gated on the above (every method must decompile). uncompyle6 has been
dropped: wowsdeob decompiles in-process with `decompile_module`.

Tooling and validation:
- `cargo run --release --example decompile_one -- <pyc> <name>` decompiles one
  function; `<pyc> --stats` sweeps a module and tallies errors by kind;
  `<pyc> --dump <out.py>` writes the whole module; `<pyc> --validate <dir>` writes
  every decompilable function's source to `<dir>`.
- `cargo run --release --example sweep_stats -- <dir>` sweeps the IR over every
  `*_stage4_deob.pyc` under a directory and reports aggregate coverage, error
  types, and any IR panic locations (single-threaded for unambiguous locations).
  `sweep_deob -- <dir>` does the same for the deobfuscator over raw `*_stage4.pyc`,
  reporting deob panic locations. These drove coverage and the no-panics goal to
  their current state; rerun them after IR/deob changes to catch regressions.
  Generate the `*_stage4*.pyc` inputs by running wowsdeob on `scripts.zip`.
- Validate correctness by recompiling those with Python 2.7, e.g.
  `for f in <dir>/*.py: py_compile.compile(f, doraise=True)`. This is how the
  invalid-output bugs (reserved-word/illegal identifiers, leaked placeholders)
  were found; keep it green.
- Snapshot tests in `unfuck/tests/corpus.rs` over the self-compiled fixture
  `tests/fixtures/cases.py` (`INSTA_UPDATE=always cargo test` to regenerate).
  Synthetic unit tests in `tests/ir_m1.rs` use a label-based bytecode builder
  (no hand-written offsets).
- Never commit game `.pyc` files; fixtures are our own compiled `.py`.

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
