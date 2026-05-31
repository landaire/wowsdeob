# Agent guide: wowsdeob

Deobfuscator for World of Warships Python 2.7 script files. Blog background:
https://landaire.net/world-of-warships-deobfuscation/

## Repos and roles

All are local sibling checkouts under `G:\dev` and are wired together by path:

- `wowsdeob` (this repo): CLI driver. Unwraps the staged payloads, drives the
  deobfuscator, and shells out to a Python decompiler.
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

## The raising IR (the real fix, in progress)

`unfuck/src/ir/` is a typed, pass-based IR meant to eventually replace uncompyle6
with a structuring decompiler that emits Python source directly. Plan:

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

Status: decompiles 335/348 Avatar code objects from scratch, including functions
uncompyle6 cannot (e.g. getDriftAngle). Every decompiled function is verified to
compile under Python 2.7 (see validation below); anything not fully recoverable
returns a typed error rather than wrong or invalid source. Done: branch-free
lowering, if/else via post-dominators, while and for loops (including tuple
targets) via back-edge/natural-loop detection, break/continue (BREAK_LOOP/
CONTINUE_LOOP), raise, deref vars, keyword and splat call arguments, tuple
assignment, dict literals, short-circuit and/or, ternaries (POP_JUMP_IF_FALSE and
the negated POP_JUMP_IF_TRUE form), augmented assignment (name/attr/subscript via
INPLACE + ROT_TWO/ROT_THREE) and chained-comparison rotations, slices and del
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
`continue`s. The 335 recovered objects contain zero `__unrecovered__` markers, and
the concatenated `--dump` of all 348 parses as one module.

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

Remaining gaps (`decompile_one --stats`), each needing a larger piece. (1) Returned
boolean expressions with no merge: `return a < b < c` / `return x and y` compile to
multiple RETURNs (no single value to fold), so the chained-comparison/short-circuit
recovery does not apply (vehicleInsideSelection). The general fix is cross-block
value/phi reconstruction (SSA). (2) processConsoleCommand had two independent deob
bugs. The first, the remove_const_conditions taint over-removal, is FIXED: the access
tracker shares its Arc and accumulates the full transitive history, so a folded
opaque predicate's removal set was polluted with live instructions from other blocks
(it had stripped this function's `cmdCode, cmdInfo, errorInfo = validateAndParseCmd(...)`
call and unpack). remove_const_conditions now removes only the local in-block slice
that computes a folded jump's condition; cross-block taint is left in place. The fix
is strictly conservative (full Avatar dump byte-identical, all 335 still recompile)
and restored this function's prologue. Two further node/edge-cleanup soundness fixes
followed (both byte-identical on Avatar): join_block now re-adds a merged block's
outgoing edges by stable NodeIndex instead of a stale start_offset lookup, and node
removal is now reachability-from-root instead of an execution-coverage heuristic that
dropped live unwalked blocks. The second processConsoleCommand bug still blocks it and
is now fully traced: the obfuscator splits the `LOG_INFO(...)` statement across offsets
and reconnects it with no-op forwarding trampolines (`JUMP_FORWARD 0`). The
`addBan`/`removeBan` blocks end in `JUMP_ABSOLUTE` to such a trampoline, which forwards
to `return cmdStartsWithSlash`. During un-flattening that trampoline's
`addBan -> trampoline -> return` forwarding edge is dropped (the trampoline becomes
unreachable while the partial executor is still folding the surrounding opaque
predicate), so `addBan` is left with no successor; `ensure_terminal_returns` then
appends `LOAD_CONST None; RETURN` *after* the now-orphaned `JUMP_ABSOLUTE`, and
`write_bytecode` emits the stale jump, which (after offsets shift) lands inside the
reassembled `LOG_INFO` CALL and underflows. The reachability node-removal fix did not
recover it because the forwarding edge is severed earlier, during the opaque-predicate
edge fold itself, not at node removal. The remaining fix must preserve the forwarding
edge through the fold (redirect `addBan` to the trampoline's destination before the
trampoline is disconnected), or strip orphaned mid-block jumps before
ensure_terminal_returns runs. A naive forward-trampoline collapse pass was prototyped
and regressed a function (334/348), so it needs the redirect done at the right point
with fallthrough-edge handling. (3) A
reordered nested ternary whose merge the deob placed before the else: find_ternaries
expects the merge after both arms, so it does not match. This blocks cacheGunsState
and is also the real root of receiveDamageReport, where the ternary sits inside the
try body and its relocated else arm falls into the handler's POP_TOP triple (a
stack-underflow/SETUP_EXCEPT symptom, not a try-in-loop bug). The layout does not
reconcile soundly enough to recover without dedicated reordered-diamond detection.
(4) One structurer limitation: a deeply nested loop CFG that does not reduce to
regions (drawProjectileTraces). ROT_TWO/ROT_THREE simultaneous assignment is deliberately
rejected (ambiguous). Standalone <genexpr>/<setcomp>/<dictcomp> objects are correctly
rejected (only valid inlined). The module body and the Avatar/PlayerAvatar class
bodies are gated on the above (every method must decompile), so a single clean module
file awaits these + the bridge. Then drop uncompyle6.

Tooling and validation:
- `cargo run --release --example decompile_one -- <pyc> <name>` decompiles one
  function; `<pyc> --stats` sweeps a module and tallies errors by kind;
  `<pyc> --validate <dir>` writes every decompilable function's source to `<dir>`.
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
isolated `uv` venv. The working scratch dir is `G:\wowsdeob_tmp` (safe to wipe):

- `G:\wowsdeob_tmp\.venv`: isolated venv with `uncompyle6` and `decompyle3`
  (`uv venv` + `uv pip install --python .venv uncompyle6 decompyle3`).
- `C:\Python27\python2.exe`: system Python 2.7, used READ-ONLY to compile
  reference source and compare canonical compiler output. Never install into it.
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
UNFUCK_DECOMPILER=<path-to-uncompyle6> ./target/release/wowsdeob.exe ...
```

Known bug: the deobfuscator can **deadlock intermittently under rayon** (a
read/write race exposed by the in-progress `Mutex`->`RwLock` migration in
py-marshal). Symptom: process hangs with near-zero CPU. Workaround: run with
`RAYON_NUM_THREADS=1`. This needs a real fix before any parallel corpus run.

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

- Commit with `jj` (Jujutsu), not raw git. Use conventional-commit messages
  (`feat:`, `fix:`, `refactor:`, ...). Do NOT add `Co-Authored-By` trailers.
- No LLM-style comments in code: no section-divider banners, no em/en dashes, no
  unicode arrows.
