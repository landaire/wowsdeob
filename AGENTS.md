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
scripts.zip): the IR decompiles **97.1% of 93399 code objects** (90684) with **zero
panics** in either the deobfuscator or the IR, at ~1.1GB peak across 32 threads (no
OOM). (The object count rose from 93391 and the rate dipped from a falsely-inflated
97.2% when the pydis STORE_DEREF opcode bug was fixed -- see below; the prior figure
counted corrupt truncated stubs as recoveries.) On the larger
`G:\dev\wows-toolkit\.scratch\allscripts` corpus (5159 files, 93964 objects) the
cross-block ternary-arm fix below took ok from 91214 to 91242 (+28), the
jump-to-shared-return fix a further 91242 -> 91248 (+6), regenerating the corpus with
the current deob (see STALE CORPUS below) 91248 -> 91296 (+48), and the
inline-list-comp ternary-arm fix 91296 -> 91313 (+17), the chained-ternary fix
91313 -> 91384 (+71), the dict-display ternary-arm fix 91384 -> 91399 (+15), and the
deob never-taken const-condition fold 91399 -> 91404 (+5), the deob class-creation
junk strip 91404 -> 91414 (+10), the deob import-name junk strip 91414 -> 91418 (+4),
the IR for...else recovery 91418 -> 91564 (+146), the nested-ternary-in-value-region
fix 91564 -> 91567 (+3), the out-of-range-branch opaque-predicate strip 91567 ->
91585 (+18), the chained-comparison-in-ternary-arm fix 91585 -> 91586 (+1), and the
reordered-ternary dict-display/lambda-arm fix 91586 -> 91590 (+4, preceded by a
short-circuit-wrapped-ternary parenthesisation correctness fix), and the
both-arms-terminate region fix 91590 -> 91704 (+114), the split-loop-cleanup
break-target fix 91704 -> 91728 (+24, plus ~95 mis-structured files corrected), a lambda-operand
parenthesisation correctness fix, and the trampolined-for...else fix 91728 -> 91745 (+17), and the FOR_ITER-exit-trampolines-to-follow
break fix 91745 -> 91748 (+3, MissionsComponent.onVehicleDeath), the extended-slice/tuple-subscript
rendering fix, and complex/bytes/ellipsis/stopiteration constant rendering 91748 -> 91879 (+131), and
tuple-parameter lambdas 91879 -> 91895 (+16), then a faithfulness correction that REJECTS lost-body
loop garbage 91895 -> 91855 (-40, removing semantically-wrong recoveries), and the while-True
read-loop recovery 91855 -> 91883 (+28; the proper count-positive AND correct fix for the loops the
lost-body guard had reduced to honest failures), now **97.8% (honest)**. Three readability/faithfulness
fixes followed (no headline change -- they improve output, not the recovery count): elif collapsing,
triple-quoted docstrings, and junk-name renaming (see below).

**Corpus moved (2026-06-04):** `G:\dev\wows-toolkit\.scratch\allscripts` (the old 5159-file corpus)
was deleted externally. The working corpus is now **`G:\deob_guard\scripts`** (4215 files, 71603
objects); it carries the `*_stage4.pyc` sources so it is re-deobbable in place with
`deob_archive G:/deob_guard/scripts` (do that first -- its cached deob output was stale). Fresh
re-deob with the current deobfuscator: **70311/71603 = 98.2%, zero panics**. Different/smaller corpus
than before, so this number is not directly comparable to the old 97.8%. Canonical source for a full
regenerate: `G:\deob\scripts.zip`. **Now 70562/71603 = 98.5%** after the merge-redirect, narrowed
merge-less-try, decorated-renamed-method, degenerate-predicate, empty-finally, nested-finally, and
END_FINALLY-edge-remap fixes below.

**Decorated methods renamed to `<comprehension>` RECOVERED (+94, 98.2%->98.3%).** A class method the
obfuscator renamed (co_name rewritten to `<dictcomp>`/`<genexpr>`) and decorated compiles to
`name = deco(MAKE_FUNCTION(<obfuscated code>))`. `try_decorated_def` rejected every inner co_name
starting with `<`, so these fell through to ordinary assignment rendering and emitted
`classmethod(__unrecovered__)`, poisoning the whole class object. `function_def` already de-obfuscates
such renamed methods (it renames the def header to the store target), so the decorated path now accepts
the `<...>` case too -- except `<lambda>` (an assignment, not a def -- `@deco` cannot attach) and a
genuine comprehension body (`.0` arg, no standalone def form). Dropped the partially-recovered bucket
818->724; 0 regressions; verified `_getMiscAnimations` -> `@classmethod def _getMiscAnimations`.
DIAGNOSTIC: `examples/probe_agg <dir> [signature]` bins that bucket by marker context -- it showed the
818 split as ~314 derived (a class method that itself fails another bucket, marker after `return`),
~100 obfuscated-`<>` decorated methods (this fix), and ~88 name-mismatch stores (synthetic `unknown_N`
target, left alone). So most of the *remaining* 724 are DERIVED: a class poisoned by one nested method
that fails for a root-cause reason (SETUP_EXCEPT 52, CFG-not-reduced 75, JUMP_IF_FALSE_OR_POP 36, ...);
fixing those root buckets clears the parent too.

**Degenerate opaque predicates STRIPPED (+11, 98.3%).** The "unsupported opcode JUMP_IF_FALSE_OR_POP"
bucket is a misnomer -- it is the catch-all error for an unresolved short-circuit/ternary at a block
terminator (cfg.rs), not a literal opcode. Many of those 36 are an obfuscator opaque predicate: a
conditional jump whose taken target IS its own fall-through (`POP_JUMP_IF_FALSE` to the next
instruction), testing a junk value (`a % 2`, `x != x`). It can never divert control, so
`strip_degenerate_predicates` (cfg.rs, run from `DecodedFunction::decode`) removes the WHOLE dead
predicate: walk backward over side-effect-free value opcodes (`opaque_value_delta`) until they balance
to the jump's single popped operand, then NOP that run and the jump (offset-preserving). Conservative --
stops at the first non-pure-value opcode (a call, a store), so a real computation is never disturbed and
a non-degenerate object is left byte-identical. Recovered +11 (JUMP_IF_FALSE_OR_POP 36->32 directly,
plus 7 derived class parents 724->717), 0 regressions, 0 new recompile failures; also a faithfulness win
on already-recovered code (dead `if <junk>: pass` blocks dropped: abc `if x is None: pass`, aifc
`if x != x: pass`). The remaining 32 are predicates whose value involves a call or a non-degenerate
shape (calcGunPitch, TargetInfo.update). NOTE: an earlier attempt that rewrote only the jump to POP_TOP
(leaving the junk as a dead expr statement) recovered nothing and was reverted -- the whole predicate
must be excised.

**Empty finally (`finally: pass`) RECOVERED (+9, 98.4%).** A `try`/`finally` whose cleanup is empty --
its only instruction the `END_FINALLY` at the SETUP_FINALLY target, which recovery drops -- left no block
at the finalbody offset, so the structurer's `cfg.target(finalbody)` failed the whole object with
`BadOperand` ("instruction operand out of range"), e.g. setuptools `_read_utf8_file`
(`try: return codecs.open(path).read() finally: pass`; the deob had stripped the real `f.close()`). Fix
(unfuck cf86f02d): `Terminator::Finally.finalbody` and `FinallyShape.finalbody` are now `Option<Offset>`;
`recover_finally` sets `None` when `finalbody_idx == end_idx` (body empty), and the structurer emits an
empty suite (`block()` renders `pass`) and converges the protected body straight at the merge. Dropped
operand-out-of-range 80->75 (+5 direct, +4 derived parents 717->713), 0 reg, 0 new recompile failures.

**Nested finally merge past the enclosing END_FINALLY RECOVERED (+6).** A nested `try/finally` whose
inner clause ends exactly where the outer's does -- the stdlib `close` idiom (`try: flush() finally: try:
unlock() finally: file.close()`, in mailbox/logging.handlers/multiprocessing/...) -- had the inner
finally's merge sit immediately behind the OUTER finally's END_FINALLY, which recovery drops, so the
inner `end` named a removed instruction (`BadOperand`). The enclosing finally has a lower SETUP offset so
`recover_finallys` recovers it first and its END_FINALLY is already excluded; the inner `end` now skips
past any already-excluded END_FINALLY (and NOP) to the real merge block (unfuck fc8340eb). +6
(operand-out-of-range 75->72, +3 derived parents); mailbox/logging.handlers `close` match canonical. 88
tests, 0 reg. mailbox/logging.handlers `close` match canonical.

**Jump edges to an excluded END_FINALLY REMAPPED (+119, 98.5% -- the big one).** A try/EXCEPT that is the
SOLE body of an enclosing finally has its body-exit and handler-exit `JUMP_FORWARD`s both target the outer
finally's `END_FINALLY`, which recovery drops -- so those CFG EDGES named a non-existent block and
`cfg.target()` missed (`BadOperand`). Fixing the try shape's `end` is NOT enough (the raw JUMP edges still
point at the dropped offset -- confirmed via temp eprintln in `target()`). Fix (unfuck cd57f4ee): a
post-pass over every block's terminator (`end_finally_remap` builds excluded-END_FINALLY -> post-run-merge;
`Terminator::remap_targets` applies it to all successor offsets). SOUND because break/continue/return
through a finally use the block-stack opcodes (BREAK_LOOP/CONTINUE_LOOP/RETURN_VALUE), NOT an explicit jump
to END_FINALLY, and the exception-dispatch re-raise jump sits in an excluded (terminator-less) block -- so
the only edges landing on an END_FINALLY are normal flow resuming after the construct. +119
(operand-out-of-range 72 -> 7, plus ~54 derived parents 710 -> 656); mailbox/httplib/Tkinter `close`-family
match canonical. 89 tests, 0 reg, 0 new recompile failures. The remaining 7 operand-out-of-range are a
different `continue`-related cause (py2_test_grammar `testContinueStmt`).

**Bare `except:` as the whole finally body RECOVERED (+6, 98.5%).** `recover_finally` finds a finally's
own `END_FINALLY` by depth-counting nested `SETUP_`/`END_FINALLY` pairs. A bare `except:` clears the
exception with `POP_TOP`s and never re-raises, so (unlike `except T:`) it emits NO `END_FINALLY` -- but the
scan counted its `SETUP_EXCEPT`, leaving depth non-zero and consuming the finally's own `END_FINALLY`,
rejecting any `finally: try: cleanup() except: pass` (tkCommonDialog.show). Fix (unfuck 3606cb68): skip a
bare-except `SETUP_EXCEPT` in the end-scan (`is_bare_except` = handler starts with `POP_TOP`, not the
`DUP_TOP` of a typed clause); typed-except/with/finally/loop bracketing is unchanged, so the change is inert
elsewhere. The END_FINALLY-edge remap then redirects the inner except's exits. SETUP_FINALLY 25->22.
LESSON: a first attempt that depth-counted ONLY `SETUP_FINALLY` and relied on prior exclusions to skip
except/with END_FINALLYs regressed 3 objects -- those exclusions are NOT always complete -- so the minimal
behavior-preserving skip is the right shape.

**Finally-RETURNS (`finally: return`/`raise`) RECOVERED (+2).** A cleanup that unconditionally exits emits
no END_FINALLY and has no merge; recover_finally's end-scan found none and rejected (`translation`:
`try: <try/except> finally: return text`). Made `Terminator::Finally.end`/`FinallyShape.end` `Option<Offset>`;
when the end-scan finds no END_FINALLY but the body reaches a return/raise via straight-line code
(`clause_terminates`), accept with `end = None` -- the structurer bounds the clause at the enclosing `stop`
and emits nothing after (unfuck 67a91b33). Only +2 (SETUP_FINALLY 22->21): most `finally: return` sites were
already in recovering objects; a branching no-END_FINALLY cleanup stays rejected (conservative). RESIDUAL
SETUP_FINALLY (21): heterogeneous -- finally body containing a LOOP (lock_tests `unknown_2`:
`finally: ...; while not self._can_exit: _wait()`), and others. Each is a distinct intricate shape, low yield.

**The 142 stack-underflow bucket is CROSS-BLOCK/scramble, confirmed via instrumentation.** Probed
`pulldom.processingInstruction` (DBG_STEP env in unstack.rs step()): underflow at a `CALL_FUNCTION` entering
a block with stack_depth=0 -- a call expression split across an if-merge where the two predecessors reach the
merge with inconsistent stacks (one empty, one mid-expression). Same hard class as the email/ttk scrambles;
the per-block unstacker doesn't carry partial expressions across block boundaries. Not a cheap lever.

**Buckets that are obfuscator control-flow SCRAMBLES, not IR bugs (investigated, hard).** The
stack-underflow (142) and many SETUP_EXCEPT (52) failures are the obfuscator pointing a jump INTO THE
MIDDLE of an expression: ttk `LabeledScale.destroy`'s `except: pass` does `JUMP_FORWARD` to a bare
`CALL_FUNCTION` (args not on the stack); email `encode_7or8bit`'s except does a complete
`msg['CTE']='8bit'` store then jumps into the middle of the else branch's store (offset 95,
`STORE_SUBSCR` with an empty stack). These do not correspond to clean source and fail gracefully -- the
fix belongs in the deobfuscator (un-scramble), not the IR. Not a cheap lever.

**While-True loops whose header breaks** (+1): `while 1: <stmts>; break` whose loop header block ends
in `BREAK_LOOP` (optimized, no POP_BLOCK) was rejected -- the infinite-loop structurer only accepted a
Jump/Fallthrough header and could not find the loop exit (the break's edge is its fallback = the back
edge). Now handles a `Break`-terminated header and derives the follow from the break it carries, so
`while True: break` recovers with the after-loop code intact. Rare shape (the read-loop test-header
case is handled separately), but a clean correctness fix.

**If-arm over-walk duplication FIXED (partial)** (+11, faithfulness): when one arm of an `if`
terminates (return/raise/break/continue), no block post-dominates the `if`, so its post-dominator is the
function exit and the non-terminating arm was structured with `stop == Exit` -- letting it walk PAST the
enclosing region boundary and re-emit a following loop that was also emitted after the region
(duplicated). Fix: when the post-dominator is the exit, bound the arms at the enclosing region's `stop`.
De-duplicated 148 files (net -4049 lines, all recompile), recovered 11 objects whose over-walk had
failed structuring, zero regressions; verified vs canonical (asyncore.poll3) and game code (WeaponUtils
`if A: x; continue` chains collapse to clean elif).

**Duplicated-loop merge redirect FIXED (faithfulness, net -918K lines/106 files).** The larger class
(`if`/`try` with a RETURNING path whose other arms converge on a following loop -- chunk.skip:
`if seekable: try: seek; return except: pass` then `while ...`) is now structured by finding the real
merge instead of bounding at `Exit`. In `region()`'s CondBranch arm, when the immediate post-dominator
is the function exit, check whether one arm forward-reaches the block the other arm begins at
(`reaches`, with the `if` block as a back-edge barrier) AND that block enters a loop (`enters_loop`:
it is a loop header or its fall-through successor is one); if so, bound BOTH arms there so the loop is
emitted once. Scoped to LOOP merges only -- a non-loop rejoin is left to the enclosing `stop`, because
redirecting it splits a value region (inContext-type) and regressed 16 objects. chunk.skip fully
de-duplicated; ShipFilterItemSystem 16->4 copies; BattleHintsSystem 1.9M->1.0M lines (pathological
exponential dup, still bloated but halved). 86 tests, 0 marker regressions, 0 new recompile failures.

**Residual:** the redirect catches loop merges; non-loop tail duplication still remains in some files
(ShipFilter's 4 surviving copies, urllib.retrieve's read loop replicated across mutually-exclusive
branches). Recompilable and semantically equivalent, but not minimal -- a full structural merge-point
pass (not just Exit-postdom redirection) is the eventual fix.

**Merge-less-try rejection narrowed (+3, whichdb byte-exact).** `recover_try` rejected every merge-less
try whenever the object contained ANY SETUP_FINALLY/SETUP_WITH (to avoid double-emitting an enclosing
cleanup). Narrowed to an ACTUALLY-enclosing cleanup: one whose SETUP precedes the SETUP_EXCEPT and whose
protected range (its branch target) extends past it. Recovered whichdb byte-exact and urllib.retrieve
(previously `# control flow not yet structured (SETUP_EXCEPT)` stubs); retrieve's read loop is still
branch-duplicated (the residual above) but recompiles and is equivalent -- strictly better than the stub.

**Readability fixes (2026-06-04, no recovery-count change).** (1) **elif collapsing** (emit.rs): an
`else` whose whole body is a single `if` is now emitted as `elif`, recursing so a long conditional
ladder (e.g. BatterySystem.__getBatteryState) renders flat instead of marching the indent rightward;
the empty-then (`if not c:`) and terminal-flatten (`if guard: return`) cases are preserved. (2)
**Triple-quoted docstrings** (emit.rs): a multi-line function/method docstring renders as `"""..."""`
with real newlines instead of a one-line `\n`/`\t`-escaped string. The nested-def re-indenter
(`emit_reindented`) is now docstring-aware -- it leaves a triple-quoted docstring's interior verbatim,
so the literal's bytes survive being nested into a class/module (verified byte-exact corpus-wide); it
falls back to the escaped form when triple-quoting would not round-trip (a backslash, an embedded
`"""`, a trailing quote). (3) **Junk-name renaming** (deob.rs fix_one_varname): an all-underscore name
(`_`, `__`) or a digit-leading name (`4`, which the emitter mangled into `_`) is now normalized to
`unknown_N` like the other junk names -- BatterySystem.__getBatteryState's accumulator (really the
co_varname `4`) was rendering as `_`. The synthetic `<dictcomp>`/`<genexpr>`/`<lambda>` names and the
comprehension arg `.0` are deliberately exempt (the decompiler keys comprehension/lambda recovery on
them; renaming them cascaded ~4200 class/module-body failures in a first over-broad attempt). Re-deob
of the whole corpus confirmed recovery byte-identical.

**While-True read-loop recovery** (+28, the lever the lost-body guard was a stopgap for): a
relinearized read-loop (`while 1: x = self.read(); if x == s: break; ...`) keeps its per-iteration
computation and exit test in the loop *header* block, with one test arm a `BREAK_LOOP`. The old break
resolution mapped that break to the block before the SETUP_LOOP follow -- the back edge -- so it was
dragged into the loop body and the header mis-structured as a `while cond:` that dropped both the read
and the break (the garbage the guard rejected). Fix: lower a flat while-loop's break to a first-class
`Terminator::Break { follow, fallback }` -- it behaves exactly as `Jump(fallback)` for the graph and
the structurer everywhere except a new `structure_while_true_test`, which fires when a CondBranch loop
header carries statements and one arm is a direct break, emitting `while True:` with the header
statements and `if cond: break` (deep breaks in the same loop bind to the SETUP_LOOP follow too). It is
deliberately narrow -- flat loops only (no FOR_ITER, no nested loop), a single break, and it declines
on the do-while shape and on loops whose follow enters a with/finally cleanup -- so the for...else
machinery and every working loop are byte-unchanged. Recovers 32 read-loops correctly (xdrlib.unpack_list
byte-exact vs canonical, plus jpeg, getpass, the LWP/Mozilla cookie jars, cdplayer, mimify, ...);
binhex's two objects flip from `while <undefined>:` garbage to an honest failure. Tests
while_true_read_loop_with_test_header. FOUR prior surgical attempts (break_targets back-edge tweak,
loose/tight break->Break, natural_loop exclusion) all regressed working breaks; this one works because
`successors()` stays `[fallback]` (loop detection byte-identical) and the recovery is gated to the one
shape that needs it. The remaining read-loops -- multiple breaks, do-while, loop-in-`with` -- still
fall back to the prior behavior.

**Lost-body loop garbage REJECTED** (faithfulness, -40 nominal): a relinearized loop
(`while 1: x = read(); if x == '': break; ...`) could be mis-headered onto an inner test, drop its
body, and emit a semantically WRONG `while x == '': pass` (often with the surrounding block
duplicated) -- recompilable but not faithful. ~85 such loops existed in the nominal 97.8%, so part of
that number was garbage. Fix (structure.rs loop_body_lost): reject a loop whose recovered body is
empty yet whose body_set has a non-header block carrying real statements (content lost); a genuine
empty loop (`while c: pass`) has no such block and is unaffected. This converts ~38 confirmed
lost-body read/poll loops (cdplayer, xdrlib, mimify, pdb, getpass, ...) from garbage into honest
`# did not reduce` failures. The count drop is the honest cost of not presenting wrong source as
recovered -- per the goal's semantic-accuracy requirement, an honest failure beats silent wrong code.
The proper fix (correctly structuring the relinearized while-1-with-break read-loop, count-positive
AND correct) remains the next lever; the guard is the safety net until then. Test
while_with_genuinely_empty_body (guard must not over-fire on real busy-waits).

**Tuple-parameter lambdas** (`lambda (a, b): ...`, PackItemInfo.create's ifilter predicate, +16): a
Python 2 tuple parameter compiles to a synthetic `.0` arg the body unpacks; a lambda body must be a
single expression, so the leading unpack made it __unrecovered__. Render the tuple in the lambda's
parameter list (from the unpack's targets) and drop the unpack from the body; reject when the
deobfuscated names collide (`lambda (_, _): ...` is invalid). A `def` keeps the compiler's form (the
`.0` arg + unpack as a body statement -- already valid Python), so only the lambda path changed --
critically, sugaring defs would have introduced a `_` collision in inspect_fodder (caught by the
per-OBJECT check; the per-file check missed it because the whole module flipped to standalone dump).

**Missing constant types + extended-slice rendering** (+131): render_obj had no arm for Complex,
Bytes, Ellipsis, or StopIteration constants, so any object holding one (e.g. `return -0j`) emitted
`__unrecovered___const_Complex` and failed as Incomplete -- a pure RENDERING gap, not corruption.
Added: complex as a CPython-repr-matching literal (`-0j`, `(2+3j)`, `(1.5-2.5j)`) that round-trips,
Bytes as a str literal, Ellipsis/StopIteration as their builtin names. Exposed (and a prerequisite
commit fixed) a pre-existing extended-slice bug: BUILD_SLICE pushes explicit None constants for
absent bounds, so slices rendered `None:42` (SyntaxError) instead of `:42`, and tuple subscript
indices were wrongly parenthesised (`x[(a, b)]` -> `x[a, b]`, required for `x[:42, ..., :24]`).
LESSON: Incomplete/"partially recovered" failures are not all corruption -- some are leaf RENDERING
bugs (a const type, a precedence, a slice form) that fail an otherwise-recoverable object; these are
high-value (a one-line render arm recovered 131 objects).

**Trampolined for...else** (CamerasKeyHandler.update -- the canonical "irreducibility" example --
MissionsComponent.onVehicleDeath, lib2to3 parse): the relinearizer makes the SETUP_LOOP follow a
lone `JUMP_ABSOLUTE <conv>` trampoline rather than the after-loop code, with the else clause between
the FOR_ITER exit and that trampoline, ending in a jump PAST the raw follow. clean_else on the raw
follow rejects the for...else, the break is unrecognised, and region() walks out as a bare ForIter.
Fix (break_targets): thread the follow through lone-jump trampolines (cycle-guarded, only past the
FOR_ITER exit), and when the threaded else region holds a real statement, resolve break + the
for...else to it. The real-statement guard stops a nested loop's trivial exit cleanup (POP_BLOCK +
jumps) being mistaken for an else (sre_compile._optimize_charset). Additive (tried only after the
plain logic), so plain breaks are untouched. This dissolves the last of the "control-flow-flattening
irreducibility" frontier: update() was NOT irreducible, just a for...else with a trampolined follow.
A lambda used as an operator operand is also now parenthesised (`convert or (lambda g, n: n)`) --
MakeFunction reported prec::ATOM but a lambda is the lowest-precedence expression (lib2to3 parse).
VALIDATION UPGRADE: the per-file marker worse-check is BLIND to a file where one object regresses and
another improves (net-zero) -- caught sre_compile only via content-diff; now use a per-OBJECT
regression check (objects newly in the failure set) in addition.

**Break target split from the FOR_ITER exit** (WishesSystem.__getBestWishes, NavigationCommon,
tarfile._proc_sparse, smtplib.login, +95 files): a relinearized loop splits its cleanup so the
FOR_ITER exit is `POP_BLOCK; JUMP <conv>` and the SETUP_LOOP follow is a separate `JUMP <conv>`,
both converging past the follow. break_targets resolved BREAK_LOOP to `natural` (the instruction
before the SETUP_LOOP follow), which lands on the FOR_ITER exit's *trailing jump* -- a different
block than the loop's structural follow (the FOR_ITER exit block itself). The break edge was thus
unrecognised: region() walked out of the loop body and inlined the after-loop code into it
(recompilable but semantically WRONG -- duplicated, mis-nested), or failed as did-not-reduce. Fix
(break_targets): when the exit region carries no real statements (POP_BLOCK + unconditional jumps
only -- i.e. there is no else clause, just split cleanup), resolve break to the FOR_ITER exit so it
aligns with the follow. This not only recovered +24 objects but DE-DUPLICATED ~95 already-"recovered"
files that had been emitting wrong source -- the marker-count check is blind to recovered-but-wrong,
so this was caught only by content-diffing changed files and verifying against canonical stdlib
(tarfile._proc_sparse and smtplib.login match exactly; NavigationCommon shed a 113-line mis-inlined
duplicate, `descendPoint = unknown_17` going from 4 copies to 1). Test break_target_split_from_for_iter_exit.

**`if` whose both arms transfer control, inside a loop** (QuadTree.__createChildren,
textwrap.dedent, AirDefense, difflib, +52 files): region() resumed at a conditional's
immediate post-dominator unconditionally. For the common `for ..: if cond: ..; break`
shape the inner loop body is just that `if` -- both arms transfer control (then breaks,
the false edge jumps back to the FOR_ITER = continue) so nothing follows the `if`, yet its
post-dominator is the inner loop's *follow*, which flows into the outer loop header.
Resuming there walked out of the loop body and re-entered the outer FOR_ITER as a bare
block -> "control-flow graph did not reduce". Fix (structure.rs): when both (non-empty)
arms of the emitted `if` `terminate()` (end in break/continue/return/raise), set the cursor
to None instead of the post-dominator -- the post-dom is not reached through this `if`, so
the region ends. The biggest single did-not-reduce lever found; verified faithful against
canonical textwrap.dedent (the `for..else` + break recovers exactly). Test
nested_loop_inner_if_breaks.

**Reordered ternary with a dict-display or lambda arm** + **short-circuit-wrapped ternary**
(updateProperties in ClientSettingsProxy, updateDunkerque in FakeStatesController): the
obfuscator's relinearizer lays a branch's merge *before* one arm and makes that arm jump
*backward* to the merge -- the "control-flow-flattening-induced irreducibility" diagnosed as
the remaining frontier. region() actually handles this fine (it follows edges, not physical
layout); the real blocker for `unknown_66 = {} if c else {VERSION: ..}` was that
find_reordered_ternaries' `pure_expression` arm check rejected `STORE_MAP` (and
`MAKE_FUNCTION`/`MAKE_CLOSURE`) -- statement-shaped mnemonics that are actually value-only
(a dict display / a lambda or inlined comprehension). With the diamond left as control flow
the merge's STORE underflowed on the empty per-block stack (the reported underflow was thus a
red herring, not irreducibility). Whitelisting those ops (mirroring pure_ternary_arm) folds
the diamond to one expression. This newly recovered FakeStatesController.updateDunkerque,
which exposed a *separate* pre-existing unstacker bug: a short-circuit `a and (x if c else y)`
whose `and` opens before the ternary and jumps to the ternary's own merge was absorbed into
the then-arm by the JUMP_FORWARD fold, yielding the mis-parenthesised `(a and x) if c else y`
(a different program). Fixed by tracking the short-circuit stack depth at which each ternary
opens (`sc_depth`) and only folding/resolving a short-circuit ahead of the ternary when it
was opened inside the arm; the wrapping operator stays pending and combines with the resolved
ternary at the merge. This correctness fix also repaired already-recovered Avatar (×4) and
Building output that had been emitting wrong source (`x or Y if c else Z`).

**Chained comparison inside a ternary arm** (`x if c else (a if p <= q < r else b)`,
getCoreData): a chained comparison's `JUMP_IF_FALSE_OR_POP` short-circuits to its own cleanup
(`ROT_TWO; POP_TOP`), not the ternary merge, and the POP_TOP reads as a statement, so
pure_ternary_arm rejected any arm holding one. Fix: compute find_chained_comparisons before
find_ternaries and pass its interior (short-circuit jumps + cleanup) down; pure_ternary_arm
skips it like an inline list comp's interior. Rare (+1) but principled.

**Opaque predicate ending in an out-of-range branch** (AutoPickConstants etc.): the
obfuscator splices a dead predicate after real code -- unpack its marker tuple (5 ints
ending in 255) into temps, grind set/arithmetic, compare, and `POP_JUMP_IF_*` to a target
PAST the end of the code. That jump can never be taken (CPython would fault), so the whole
predicate is dead, but `strip_opaque_predicates` bailed (the trailing POP_JUMP is neither a
pure value op nor a safe consumer), and the unresolvable CondBranch then failed the strip
attempt -> fallback underflowed. `opaque_block_end` now recognizes that terminus: a
`POP_JUMP_IF_{TRUE,FALSE}` whose target >= code length, reached with the comparison on the
stack, pops it and ends the block; the depth returns to entry level so the block is provably
self-contained and is NOP'd whole (a distinct "leaves no junk" shape from the operand-burial
blocks, so it takes its own validation branch). +18, all class/module bodies (AutoPickConstants'
full PVPRules table, ShipConfig, ShipAcesComponent, ClientMissile, ...), 0 worse, all recompile.

**Nested ternary in a ternary's value region** (`d[k1 if c else k2] if outer else e`,
axisMove): the outer then-arm computes a subscript whose key is an inner ternary. Two
fixes -- (1) pure_ternary_arm now accepts a JUMP_FORWARD whose target is WITHIN the arm
(a nested sub-ternary's own merge), not only the shared outer merge; (2) the unstacker
distinguishes an `and`-chain from a nested ternary by ELSE TARGET (an `and`-chain shares
the pending ternary's else target; a nested ternary in the key region, also before the
outer `then` is set, branches elsewhere) instead of the old `then.is_none()` heuristic.

**`for ... else:` is recovered.** The else runs only on normal completion (it sits at the
`FOR_ITER` exit) and `break` skips past it to the real follow. The structurer treated only
the `FOR_ITER` exit as the loop follow, so `break` was unrecognised and underflowed
(resetControlParams: a chained comparison in a for...else search loop). Now `break_targets`
tracks each loop's `FOR_ITER` exit and detects a for...else when it is not adjacent to the
`SETUP_LOOP` follow (an else clause sits between); `structure_loop` binds `break` to the
real follow and structures the else region as a new `Stmt::ForElse`. CONSERVATIVE GATE
(refined against the per-file worse-check): only model it when the else region does not
branch PAST the follow (relinearizer can place the real convergence beyond the SETUP_LOOP
follow) and contains no loop machinery (BREAK/CONTINUE/nested SETUP_LOOP -- a nested loop's
break path, not an else). Without the gate it mis-structured relinearized layouts
(duplicated after-loop code, a module-scope `return` = invalid Python). It also exposed a
latent hang -- a bad loop follow can cycle the region walk -- so `region()` now rejects a
revisited block. +146 with 0 worse / 0 recompile failures across 109 changed files.

**Deob strips dead-store junk from class creations.** The obfuscator wedges dead
`unknown_N = <const/arith>` stores between `MAKE_FUNCTION 0` and `BUILD_CLASS` (on either
side of the class `CALL_FUNCTION 0`); their net stack effect leaves stray values under
`BUILD_CLASS`, which pops garbage instead of (name, bases, dict) so the class fails
(unsupported `BUILD_CLASS`). `strip_build_class_junk` walks back from each `BUILD_CLASS` to
the class body's `MAKE_FUNCTION 0` (requiring exactly one `CALL_FUNCTION 0` and only
pure-data junk otherwise) and removes the whole region except the call -- restoring a
balanced stack regardless of the junk's internal (im)balance. Conservative: every junk op
must be side-effect-free, and a name read outside the region keeps its store. Recovered SSE
Conditions (62->0 failures), EventRecorder, CommandMappingModKey, etc. `strip_import_name_junk`
does the same for junk wedged between `IMPORT_NAME` and `IMPORT_FROM` (the junk leaves stray
values on top of the module so `IMPORT_FROM` reads garbage); +4 more (ScenarioMissionParticipant,
TrainingRoomComponent, ...) and it also removes bogus `unknown_N = ..` lines from
already-recovering modules. The same junk also appears INTERLEAVED inside dict displays
(StrategyManager, `BUILD_MAP; BUILD_MAP; ..STORE_MAP..` with a `LOAD_CONST tuple;
UNPACK_SEQUENCE; STORE unknown_N` block wedged mid-key) -- the STORE_MAP-unsupported bucket (16)
and the residual IMPORT_FROM (8). A general "remove a stack-neutral, name-confined run whose
STORE_NAMEs target unusable-identifier (junk) names" pass was ATTEMPTED and found intractable
here: the obfuscator REUSES the same junk names across multiple interleaved junk blocks
(so no single block confines them) and feeds the junk computation's value into the real dict's
own keys/values via the stack (so it is not a separable dead region). Left for a future,
heavier dataflow approach. (Gate idea worth keeping: `deob::is_unusable_identifier` -- a name
the deob will rename to `unknown_N` -- is the safe junk-vs-real discriminator at deob time,
since real/exported names are always valid identifiers.)

**Deob folds opaque predicates inside exception handlers (never-taken only).** Partial
execution (the deob's condition folder) never follows exception edges -- entering an
except/finally handler would need the exception triple modeled -- so an opaque predicate
INSIDE a handler survives. The conditional-import shape `try: from X import * except
ImportError: from Y import *` guards its re-raise `END_FINALLY` behind
`LOAD_CONST 0; POP_JUMP_IF_TRUE <body>`; left in place, `recover_try` can't match the
handler dispatch and the whole module body fails. `remove_const_conditions` now also folds
self-contained `LOAD_CONST c; POP_JUMP_IF_{TRUE,FALSE}` blocks (the const IS the popped
condition) for the NEVER-TAKEN case -- drop the dead edge, convert to a forward
`JUMP_FORWARD`, remove the dead `LOAD_CONST`. Only never-taken: the always-taken case is a
flattening trampoline with a possibly-backward target the IR already folds post-build.

**STALE CORPUS -- regenerate before measuring.** The `*_stage4_deob.pyc` files in the
allscripts corpus are CACHED deob output and go stale when the deobfuscator improves.
A whole cluster (esp. `dhcomponents/*`) was failing on opaque predicates
(`LOAD_CONST 0; POP_JUMP_IF_TRUE <backward>` wedged between `IMPORT_NAME` and `IMPORT_FROM`
-> the IR underflows because the imported module value is cleared across the CondBranch
block split) that the CURRENT deob already removes. Always refresh first: build
`deob_archive` (release) and run `deob_archive <corpus>` -- it catches per-file panics
and skips on failure (no data loss; regenerable from `*_stage4.pyc`). This recovered +48
with no code change and took the dhcomponents subtree to 99.8%. Do not trust a failure
bucket until the corpus is fresh. The precise-provenance + cross-block dead-operand removal work (next two
paragraphs) took this from 93.3% (87186) to 93.9% (87700) and all but eliminated the
BUILD_CLASS, STORE_MAP, IMPORT_FROM and IMPORT_STAR buckets; recovering try/with/
finally regions the relinearizer splits across `JUMP_FORWARD 0` trampolines, then
emitting each recovered module at top level with clean names, then threading the
relative-import level (below) carried it to 94.8% (88580), then folding negated
list-comprehension filters to 94.9%, then structuring try/except whose arms continue
an enclosing loop (the `for x in xs: try: f(x) except E: pass` idiom) to 95.2% --
that one collapsed the END_FINALLY bucket 310 -> 57 -- then recovering try/except
whose body falls through to the merge (the deob drops the body's `JUMP merge` when
the merge is the next instruction, e.g. the function epilogue) to 95.3%, which took
SETUP_EXCEPT 225 -> 127, then excluding a handler's re-raise END_FINALLY that the
relinearizer places past the try merge (the best-effort-loop idiom `for x in xs:
try: f(x) except E: pass`) to 95.4%, then tolerating an orphan POP_BLOCK left when
the deob drops a loop's SETUP_LOOP but keeps its POP_BLOCK (a `for` loop ending a
try/with/finally body), which recover_try/with/finally now skip, then recovering
`with x as obj.attr:` (an attribute `as` target, lowered through the unstacker), then
folding multi-`for` inline list comprehensions (`[x for a in xs for b in a if c]`,
`Expr::ListComp` now carrying an ordered clause list) to 95.5%, then recovering
cross-block boolean returns (`return (a or b) and not c`, compiled to short-circuit
control flow that splits across blocks). The boolean recovery (`recover_returned_bool`)
translates each short-circuit jump to a conditional by construction, then **verifies
it against the original control flow by truth-table equivalence** (same result operand
and evaluation order for every leaf assignment) -- any mismatch rejects the fold, so a
wrong-but-compilable boolean is never emitted. This is the safe form of the
otherwise-regression-prone "boolean reconstruction" frontier. `recover_returned_bool`
then generalized from whole-body returns to a leading run of straight-line statements
followed by a boolean return (`x = f(); return x and x.copy() or {}`): it peels the
statement prefix off at the last empty-stack boundary before the first short-circuit
jump (lowering it normally) and reconstructs the returned-boolean suffix with the same
truth-table gate (89186 -> 89202; isolated old-vs-new whole-archive dump confirmed the
9 changed files each gained exactly one recovered object with none lost, all
recompile, and a module whose fallback dump that newly-recovered method unblocked was
re-emitted as its proper structured class), then folding ternary and short-circuit
ELEMENTS of inline list comprehensions (`[m if m else 0 for m in xs]`, `[a and b for
x in xs]`) to 95.6% (89262). The comprehension folder routes a `POP_JUMP` whose target
is not an enclosing loop top (so it is a branch inside the element, not a filter), and
`JUMP_FORWARD`/`JUMP_IF_*_OR_POP`, through the same `step`/`resolve_pending` ternary
machinery the block path uses, gated by a snapshot of the pending ternary/short-circuit
state at region entry: a comp that leaves a NEW unresolved operator at its `LIST_APPEND`
(e.g. a boolean *filter* `[x for x in xs if a or b]`, whose keep/skip control flow does
not converge to a value) is rejected rather than mis-folded. Isolated old-vs-new dump:
48 files changed, none lost a recovered object, all recompile. That boolean *filter*
was then taken on too (89262 -> 89275): `reconstruct_comp_filter` folds a pure short-
circuit filter (`[x for x in xs if a or b]`) whose every exit reaches the loop top
(skip, the boolean's `False` terminal) or the keep point where the element begins
(keep, the `True` terminal), translating each `POP_JUMP` to `and`/`or`/`not` and
verifying the result against the control flow by the same truth-table gate. It fires
only when the filter region (bounded at the keep point, NOT including the element that
follows) contains a forward keep jump and no `JUMP_FORWARD`/`JUMP_IF_*_OR_POP`; a
pure-`and` filter (left to the per-jump path, byte-identical) and a ternary/short-
circuit-VALUED filter `if (a in c if c else a)` (folded by the per-jump path as a
value) are both declined. Two regressions caught by the isolated dump and fixed before
commit drove that scoping: the keep-jump and decline-on-merge checks must look at the
filter region only, or a ternary ELEMENT after a pure-`and` filter (its cond is a
forward jump past the keep point) wrongly triggers the folder and breaks an
already-recovered comprehension. Final isolated dump: 8 files changed, none lost a
recovered object, all recompile. Finally, a mid-expression boolean -- a ternary/`and`/
`or` embedded as a sub-expression with unrelated values below it on the stack, e.g.
`return fmt % (x[0], join(x[1]) or '' if x[1][0] else '')` -- is recovered by a
straight-line FALLBACK (89275 -> 89279). The block structurer splits such a region at
its `POP_JUMP` and cannot rejoin it (the values below clear at the block boundary), and
the in-block `resolve_pending` machinery cannot model the shared-else short-circuit
shape (the ternary's else arm coincides with the `or`'s fall-through, so its `then` is
never recorded -- there is no `JUMP_FORWARD`). `recover_straightline_bools` runs ONLY
after the normal CFG path fails: it requires the function be straight-line modulo
forward short-circuit jumps (no loops/setup/back-edge/JUMP_FORWARD/mid-body return),
processes the stream linearly, and folds each boolean region into one value via the
same `eval_bool` + truth-table gate as the returned-boolean path (the first leaf is the
value already on the stack; the rest are lowered by stepping, each leaving the stack at
its pre-region depth so the values below are preserved). Because it runs only on
failure and emits only a gate-verified value, it can solely turn a failure into a
success -- the isolated dump confirmed exactly 3 files changed (imaplib, inspect,
pydoc), all additions, all recompile. The fallback then grew to fold multi-exit
booleans -- a short-circuit whose branches return directly, leaving interior
RETURN_VALUEs rather than converging to one merge (e.g. `unknown = getGP(id); return
unknown and (isMSkin(unknown) and not unknown.isTileflage or unknown.species == SKIN or
isPermo(unknown))`, which the deob lays out with two RETURNs): `fold_bool_region`
treats each interior RETURN as a result terminal, so the region reconstructs and
verifies as before (89279 -> 89280). Because this still only changes the post-failure
fallback methods, the CFG and fast paths stay byte-identical and it cannot regress.
(The diagnostic example `list_fails <dir> <error-substring>` lists the smallest
objects failing with a given error, for finding concrete instances of a residual
bucket.) The straight-line fallback only reaches functions that ARE straight-line; a
shared-else boolean embedded in a STATEMENT -- an `if` arm or a call argument, e.g.
`if self.proto >= 2: self.write(NEWTRUE if obj else NEWFALSE)` or `x = (a or b) if c
else b` followed by more control flow -- still failed, because the block path splits
the diamond at its POP_JUMP and cannot rejoin it (no JUMP_FORWARD records the then
operand). The final lever folds those in-block (89280 -> 89347, 95.7%): `find_bool_
regions` detects a self-contained pure short-circuit region (every jump forward within
`(start, merge]`, an interior `JUMP_IF_*_OR_POP`, no `JUMP_FORWARD`/statement), and a
post-failure rebuild `Cfg::build_bool_regions` keeps each region's interior inside one
block so the feed folds it with `fold_bool_region` (the same gate-verified
reconstruction) while the surrounding `if`/`else` structures normally. Safety rests on
two independent guarantees: the rebuild runs ONLY after the normal build fails (so the
normal path's output is byte-identical -- the build threads empty region maps
otherwise, and `Cfg::build_with` takes a `BuildMode` so the intent is explicit), and
each fold emits only a truth-table-verified value (so a misjudged region poisons its
block and the function stays failed rather than mis-emitting). Isolated old-vs-new
dump: 38 files changed, none lost a recovered object, all recompile. A follow-up
sharpened the region scanner (89347 -> 89350): a bare `POP_JUMP` (not a value-keeping
`JUMP_IF_*_OR_POP`) targeting the merge is a control-flow `if`, not a value short-
circuit, so such a region is rejected -- otherwise it greedily swallows an `if` whose
branches return booleans (`if alive: return a.f(p) or b.f(p) if a else b.f(p)`) and the
genuine value boolean nested in each branch never folds. Rejecting the outer region
lets the inner ones be found and folded per branch; isolated dump confirmed 1 file
changed, 0 regressions. Earlier module-emission
soundness fixes ride with these steps (fixing invalid output more recovery exposed):
a module's leading `__doc__ = <str>` is rendered as a bare docstring literal (so a
following `from __future__` stays legal); a class body whose implicit `return
locals()` the relinearizer hoisted into a branch is rejected rather than emitted as
invalid `return locals()`; and `import *` in the module-as-`def` fallback is rejected
(illegal inside a function whose nested functions close over the wrapped module's
bindings), the module dump falling back to a comment plus standalone nested leaves.
Each step was validated whole-archive by recompiling every changed file under Python
2.7 with zero recompile regressions (the try/except-continue step: 901 changed files,
0 regressions, 15 invalid -> valid). A note on counting: rejecting unsound renderings
(the `import *` def-wrap, the hoisted class return) trades a little raw `ok` count for
honest, recompilable output -- the goal is maximal *correct* recovery, and a residue
of genuinely corrupted deob output (truncated bytecode, over-removed stack values) is
correctly rejected rather than counted.

Written-output validity is tracked separately by recompiling every emitted `.py`:
the whole archive (5094 module files) now has just **5 that do not recompile** under
Python 2.7. Two recent fixes drove it down from 13: an integer literal used as an
attribute target is parenthesized (`(6).__index__()`, not `6.__index__()` which lexes
`6.` as a float), and the module fallback no longer renders class/module bodies as
`def` wrappers (a body is not a function; wrapping it makes a nested `exec`/`import *`
illegal and is redundant with the standalone method dumps). The 5 left are genuine
edge cases: two bare `exec` in a closure scope, a numeric-named decorator
(`@52(...)`, obfuscation residue), a docstring/structure case, and one input the
Python 2.7 compiler segfaults on.
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

A later pass through the try/except/with/finally family took the archive 89350 ->
89381 in three additive, separately-validated commits (each: isolated old-vs-new
whole-archive dump showing zero objects lost, every changed `.py` recompiled under
Python 2.7, a unit test per shape, zero panics). (1) `recover_try` located the
body's own POP_BLOCK by counting SETUP_ against POP_BLOCK, but a nested with/finally/
except whose body returns or raises emits no POP_BLOCK (the return unwinds through
WITH_CLEANUP/END_FINALLY at the region target), leaving the nested SETUP_ unbalanced
and consuming the try's own POP_BLOCK -- so the try was misclassified as merge-less
and rejected. It now tracks the runtime block stack (push each SETUP_'s target, pop
on POP_BLOCK or on reaching a still-open target), which also tolerates the
relinearizer placing a nested handler past an outer cleanup (targets do not nest by
offset). Recovers the `try: with open(p) as f: return f.read()` shape
(`__readAccountIdFromFile`). (2) The typed-except clause parser only accepted a
single STORE_ for the `as` target; it now parses an UNPACK_SEQUENCE of (possibly
nested) stores into an `LValue::Tuple`, and emit renders it in the comma form
`except socket.error, (errno, msg):` (the `as` form with a tuple is a SyntaxError in
2.7; a simple name keeps `as`, byte-identical). Recovers game-code handlers like
`DevConnection.sendData` and the distutils `os.error` idioms. (3) The merge-less
rejection (object contains any SETUP_FINALLY/SETUP_WITH) is relaxed to the precise
condition: admit the merge-less try when every handler provably terminates (reaches
RETURN_VALUE/RAISE_VARARGS through straight-line code before any branch), since a
terminating handler never falls through into the enclosing cleanup. The check is
conservative (a branchy handler is treated as possibly falling through), so it only
declines, never mis-accepts; the falling-through rejection is preserved. Recovers
the with-wrapped returning try (`import_module`), the with-in-try-then-handle
(`IOBinding.writefile`), and the inner try/except that raises inside a try/finally
(`test_argparse.stderr_to_parser_error`) -- each emits its cleanup exactly once
(verified by source inspection, since recompile alone does not catch a
double-execution mis-emit).

CFG structurer -- loop back-edge reached by fall-through (89381 -> 89616, 96.0%, the
single largest lever). Found by a near-miss analysis (`/g/tmp/near_miss.py` over the
`.new` module dumps): **520 module/class bodies were one or two failing leaves short
of full recovery**, and the dominant blocker was "control-flow graph did not reduce
to regions" (mostly game code: AccountFeatureSystem, AchievementSystem, ArmorConstants,
Behaviour, ...). `structure::region` only recovered a `continue` when a block's jump
terminator targeted the loop header; but control can reach the header by fall-through
via a post-dominator-driven cursor. When an `if` inside a loop has one arm that
returns, that `if`'s post-dominator is the function exit, so the rest of the loop body
is structured with `stop == Exit` instead of `stop == header`; a later `if` whose arms
both reach the header then leaves the cursor on the header with `stop != header`, the
`stop == header` break does not fire, and the header's FOR_ITER/while terminator was
emitted as a plain block and rejected (`getArmorType`, a triple-nested loop with an
early return). Fix: when the cursor lands on the innermost active loop's own header,
emit a `continue` and end the region. It fires only where the old path led to
Unstructurable or mis-structured a while header as an `if`, so it cannot change a
previously-correct output. Validated by the isolated dump: 128 files changed, all
recompile under Python 2.7, zero objects lost -- the only marker-set deltas are nested
generator expressions newly recovered (no standalone marker, e.g. ShipConfig and the
json encoder's `_iterencode_dict`) and lambdas inlined when a module flipped from a
partial dump to a full module body. Collapsed "cfg did not reduce" 521 -> 369 and
"construct only partially recovered" 2542 -> 2454 (the cascade into class/module
bodies). This near-miss + instrument-the-Unstructurable-sites loop is the method to
keep pushing: the remaining "cfg did not reduce" are now dominated by `while True:`/
`while 1:` unconditional-header loops (the `loop-header-not-cond-or-foriter` site,
which the structurer rejects -- a clean feature gap) and deob corruption (a FOR_ITER
with no STORE target because the loop body was stripped, e.g.
SysMessagesRendering._removeRenderedMsgsFromScene -- not recoverable).

Two more structurer/comp levers off the same near-miss loop (89616 -> 89655, 96.0%):
- Nested list comprehensions `[[..] for ..]` (89616 -> 89622). `recognize_list_comp`
  required exactly one LIST_APPEND, so a comp whose element is itself a comp (a second
  append) was left to fail; its FOR_ITER loops then fell through to the structurer as
  "cfg did not reduce". Fix: skip the spans of genuine nested comps before counting, so
  the outer is accepted when one append is its own, and fold the inner BUILD_LIST region
  recursively as the element. The nested-vs-`[]`-literal discriminator is that a real
  nested comp closes its loop straight into a LIST_APPEND (inner list appended to the
  enclosing accumulator) while a `[]` default arg in a later for-clause's iterable
  (`rewards.get(k, [])`) borrows the following FOR_ITER whose loop jumps back to an
  enclosing loop top -- the end-is-append check keeps multi-for comps byte-identical
  (regression caught in GrandStrategyPassSystem.getRewardsByTypes during validation).
  5 files changed, zero lost, all recompile; gains like CrewModifiers.__str__ and
  SSEClientUtils' `[[tuple(r) for r in g] for g in taskInfo['rewards']]`.
- Back-edge-less FOR_ITER as a `for` loop (89622 -> 89655, the single most common
  rejection -- a UT trace over the archive put it ~5x the next bucket). A for-loop whose
  body always returns/raises/breaks on the first iteration has no JUMP back to the
  FOR_ITER, so no back edge, so `detect_loops` never registered it and the header
  reached `region()` as a bare ForIter. Fix: `block_leaders` makes every FOR_ITER begin
  its own block even with no back edge (a no-op for ordinary loops, whose back edge
  already does this) so the iterator stays on the predecessor's stack_out where the loop
  structurer reads it; `detect_loops` then synthesizes the LoopInfo from the terminator
  (body successor = body, exit successor = follow, body set = forward reach short of the
  follow). 49 files changed, zero lost, all recompile, **six class/module bodies recover
  in full** (e.g. StatsPublisher flips from a flat per-object dump to a full class body).
  Collapsed "cfg did not reduce" 364 -> 302. The residual under that bucket is now
  dominated by a FOR_ITER with no STORE target (loop var dead-eliminated because the body
  returns at once, e.g. play_prompts, BattleDefinitions.find) -- recovering it needs a
  fabricated `for _ in ...` target (borderline vs no-fabrication) -- and `while True:`/
  `while 1:` unconditional-header loops (clean, needs a new Stmt variant), the next
  no-fabrication lever.
- `while True:` unconditional-header loops (89655 -> 89676), the second most common
  structurer rejection. A loop header with no condition test (only a back edge) is
  `while True:`, exited by break/return/raise inside; structure_loop rejected it. Added
  a Stmt::Loop variant (`while True:`) and structure it: the header is the first body
  block (not a separate branch), so its statements are emitted directly and the rest
  structured up to the back edge, with the follow recomputed as the one block a body
  block reaches outside the loop (the break target). Critical guard: an empty body
  (`while True: pass`) only arises when the real body and its break collapsed -- a
  BREAK_LOOP mis-resolved into the loop because break_targets points at instrs[idx-1]
  before the SETUP_LOOP follow and that block is not the POP_BLOCK exit (an optimized
  `while 1: break`, or urlparse's segment-removal loops whose POP_BLOCK exit the deob
  stripped). 29 such `while True: pass` appeared archive-wide (16 in urlparse) before
  the guard; rejecting them keeps the silent break-drop from shipping (recompile cannot
  catch it). Every surviving while True: is a genuine infinite loop exited by
  exception/return (heapq.merge over a heap exited by StopIteration, pickle.load's
  opcode dispatch exited by _Stop, telnetlib read loops, fpformat.test's input loop).
  14 files changed, zero lost, all recompile; test_ordered_dict flips its 8 class/module
  bodies from failed to fully recovered. NOTE the latent break_targets bug: do not
  "fix" it by requiring instrs[idx-1] to be a POP_BLOCK -- that regressed 331 objects
  whose working breaks legitimately have a non-POP_BLOCK instruction before the follow.

Methods the obfuscator renamed to a comprehension co_name (89676 -> 90481, 96.0% ->
96.9% -- the single largest class/module-body lever). The obfuscator rewrites a real
method's own code object co_name to `<dictcomp>`/`<genexpr>`/`<setcomp>`/`<listcomp>`
to mislead decompilers, while leaving the STORE_NAME at the method's real name (the
class needs it to dispatch). emit::function_def rejected any nested code object whose
co_name starts with `<` (a `def <dictcomp>(` is not valid source), so EVERY class/module
body holding such a method failed and fell back to a flat per-object dump. **1364 such
methods across 624 files.** Fix: distinguish by structure not name -- a genuine
comprehension/generator body takes the implicit `.0` argument (is_comprehension_body),
these renamed methods have a normal signature (self, args) -- and emit a `def` under the
store-target name (rename_def_header rewrites the `def <id>(` header; body untouched,
recursion reaches the method through self). ShipConfigContainer's `__init__` was
`<dictcomp>` (`self.__defaultConfigs = {}`, a `{}` BUILD_MAP with NO FOR_ITER/MAP_ADD --
not a comprehension at all); Account's was onGetRankDossier (6-arg event handler).
347 files changed, all recompile, **319 class/module bodies recover in full** (StateSystem
71 methods, XmppChat 126), zero regressions; collapsed `construct only partially
recovered` 2442 -> 1639. NOTE on non-ASCII docstrings: a Python 2 `str` docstring with
Cyrillic/other UTF-8 bytes renders as `\xNN` escapes (docstring_literal falls to
python_bytes_literal for any non-ASCII byte) -- faithful and byte-exact on recompile
without needing a `# coding:` header, just not human-readable. Correct, not a bug.

Non-ASCII string literals now render readable and byte-exact (rendering-only, coverage
unchanged at 90481/96.9%). A Py2 byte string holding UTF-8 text (e.g. ShipConfigContainer's
Cyrillic docstring) was fully `\xNN`-escaped; now valid-UTF-8 bytes emit as their
characters and `decompile_module` adds a `# -*- coding: utf-8 -*-` header on any module
with non-ASCII output (Py2 source defaults to ASCII). Round-trips byte-identical -- a Py2
str literal in a UTF-8 file is exactly those bytes. Two correctness rules in
docstring_literal/python_bytes_literal: (1) non-ASCII strings keep the single-quoted
`\n`/`\t`-escaped form, NOT triple quotes -- a triple-quoted literal's real newlines get
re-indented when the method nests in its class, corrupting the bytes (the single-quoted
form is one physical line, immune); (2) triple quotes are used only for backslash-free
ASCII text -- a backslash inside triple quotes is a string escape, so a doctest's literal
`\xe4` recompiled to byte 0xe4 (this fixed a PRE-EXISTING corruption in test_xml_etree).
Invalid UTF-8 (real binary) keeps `\xNN`. Verified by an archive-wide byte check
(`/g/tmp`: compile each recovered module, compare every non-ASCII str const to the
original) -- 284 files changed, all recompile, only residual is a pre-existing
test_multibytecodec codec artifact.

**Docstring re-indentation corruption (found by adversarial review, fixed).** A
function/method/class-body docstring is decompiled standalone then nested into its
class/module by re-emitting the source line by line with an added indent -- which
injects spaces into the continuation lines of a triple-quoted literal, corrupting the
bytes (getOrCreateDefaultShipConfig 316 -> 344). It hit ~half of all multi-line
docstrings: 706 across 158 files in a 1500-file sample. Fix: Emitter::docstring (the
re-indented path) emits the single-quoted one-line `\n`-escaped form (survives
re-indent byte-exact); Emitter::module_docstring (top level, never re-indented) keeps
the readable multi-line triple-quoted form. Verified 706 -> 0 by an archive-wide byte
check (every recovered multi-line string must exist verbatim in the original). When
touching string/docstring rendering, ALWAYS run that byte check -- recompile alone does
not catch a docstring whose bytes changed.

Two more clean recovery levers (90481 -> 90646, 96.9% -> 97.1%):
- For-loops with nested tuple targets `for a, (b, c) in xs:` (90481 -> 90613). The CFG
  for-target parser handled only a flat UNPACK_SEQUENCE; a slot that was itself an
  UNPACK_SEQUENCE hit store_target and failed the function. Replaced with a recursive
  parse_for_target (parity with the except-clause and assignment unpackers); the emit
  side already rendered nested LValue::Tuple. 26 class/module bodies recovered, e.g.
  CarrierStateSystem._stopVary and PlayerEvaluationInfoSystem.__parseConfig's
  doubly-nested `for (a,b,c),(d,e,f) in config.iteritems()`.
- Decorated classes `@register(x) class Foo(Base):` (90613 -> 90646). The decorator
  call wraps the BUILD_CLASS, so complete_store (which only turned a bare BuildClass into
  a ClassDef) left it as an assignment and the BuildClass reached emission as an
  __unrecovered__ expression. Extended try_decorated_def to bottom out at a BuildClass
  too (it already peeled decorator calls for functions), requiring the store target to
  match the class name. 36 class/module bodies recovered (AccountUnlocksParams' unlock
  classes). This was the largest distinct construct in the partially-recovered bucket
  (655 buildclass-expr hits) after the nested-def cascades.

**The "corruption" is largely DEOB OVER-REMOVAL -- fixable in the deob, not fabrication
(90646 -> 90731, 97.1% -> 97.2%).** First deob fix: remove_const_conditions folded a
JUMP_IF_TRUE_OR_POP / JUMP_IF_FALSE_OR_POP as a constant condition and removed its
value-producing load. But unlike POP_JUMP_IF_* (value discarded), the OR_POP variants
KEEP the tested value on the stack -- it is the short-circuit's result -- so removing the
load left the stack short ("symbolic stack underflow"). robotparser RuleLine.__str__
(`'Allow' if x else 'Disallow'`, obfuscated to `'Allow' or 'Disallow'`) lost its
`LOAD_CONST 'Allow'`. Fix: skip OR_POP conditions there, leaving them for the IR boolean
recovery. Validated by re-deobbing the whole archive at HEAD vs with the fix and
re-decompiling both (examples redeob_dump / deob_archive): 34/5093 deob outputs change,
rest byte-identical, +46 markers, ZERO lost, all recompile. **Validation recipe for any
deob change: redeob_dump <dir> redbase at HEAD, redeob_dump <dir> rednew with the change,
diff the marker-id sets -- net gain, zero lost -- then recompile the changed files.**
This means the symbolic-underflow / cfg-did-not-reduce buckets are NOT all unrecoverable:
chase each to whether the deob deleted a live instruction (the missing value's const
often still sits unused in co_consts; the FOR_ITER-with-no-STORE is the deob peepholing
`STORE x; LOAD x`) and fix the deob pass that removed it.

Second deob over-removal fix (90731 -> 90745): from_code, when a jump targets the middle
of the entry block, splits it into the entry portion (split_bb, starting at offset 0) and
the remainder -- but added split_bb without claiming root_node_id, so the root went to the
remainder. The reachability-based dead-node removal then dropped the entry block as
"unreachable". An opaque predicate that back-jumps into offset 3 (the second default-
argument load of the first MAKE_FUNCTION) triggers this: the entry's first default LOAD was
deleted, leaving MAKE_FUNCTION short (GenericTransformers' verify_keys lost exclude=None).
Fix: claim root for the first split_bb at both split sites. 15 class/module bodies recover,
zero regressions (validated by redeob_dump at the prior commit vs the fix).

**FIXED: the decoder dropped real flattened-loop bodies because of a pydis opcode-table bug.**
The dominant cfg-did-not-reduce pattern (FOR_ITER-with-no-STORE, e.g.
`Components/Factory/m21e112c4.updateDict` -> stub `for x in fromUpdate.iteritems(): return
None`) was NOT a deep symbolic-decoder flaw. Root cause: **pydis 0.4 had `STORE_DEREF = 138`;
CPython 2.7 STORE_DEREF is 137** (138 is unused). So byte 137 -- assigning to a closure cell,
extremely common -- decoded as an unknown opcode, and `const_jmp_instruction_walker` stopped
following that path, truncating every closure-using body to a stub the decompiler then
faithfully "recovered". (Also fixed: ROT_FOUR 6->5, and removed the py3-only DUP_TOP_TWO; full
byte-by-byte audit of pydis against CPython 2.7.18 `Lib/opcode.py` now reports zero
discrepancies.) The fix lives in the local `../pydis` (jj/git repo) and is wired in via
`[patch.crates-io] pydis = { path = "../pydis" }` in unfuck's Cargo.toml, mirroring the
existing py27-marshal patch. updateDict now recovers the real for/if/else with its nested
genexpr (2236-byte stub -> 5158-byte real body).

**Adversarial-review consequence (important):** isolating the fix by re-deobbing the whole
archive at the prior commit vs with it (redeob_dump) and diffing the decompile marker sets
gave +161 / -147 (not +161 / 0). The 147 "losses" are NOT regressions -- a decoder fix that
only makes byte 137 decodable cannot break a function that lacked it. They are functions whose
buggy-deob bytecode was a truncated stub (a faithful recovery of CORRUPT input) and whose
correct full body the IR cannot yet structure: cfg-did-not-reduce fell 213->149 (the stubs are
gone) while construct-only-partially-recovered rose 1508->1622 (the real closure-heavy bodies
now decode and cascade). So the prior 97.2% was inflated by corrupt stubs; 97.1% is the honest
rate, and the newly-exposed real bodies are the next IR lever (many are the cross-block-ternary
shape `self.x = ({..} if cond else {})`, see below).

Underflows that are NOT deob over-removal -- the deob output is intact and balanced -- are
IR cross-block ternary expressions: `self.x = ({k:v for ..} if cond else {})` lowers to a
CondBranch whose two arms each leave a value on the stack, consumed by a STORE after the
merge. **FIXED (cfg.rs `pure_ternary_arm`):** the in-block ternary folder rejected any arm
containing a statement opcode, and `is_statement_or_control` flags `MAKE_*`, so an arm holding
a comprehension/genexpr call (`{k:v for..}` = `(<code>)(iter)` => `MAKE_FUNCTION;GET_ITER;CALL`)
or a `key=lambda..` was rejected, structured as a plain `if`, and dropped the arm value ->
underflow -> the whole function (and its class/module body) failed. A `MAKE_FUNCTION` inside a
ternary arm is ALWAYS an expression -- a real `def` consumes the function with a STORE, which
keeps the arm impure on its own -- so `pure_ternary_arm` now allows `MAKE_FUNCTION`/`MAKE_CLOSURE`.
`AttentionMarkersComponents.resetState` recovers as
`self.__markers = {x.id: x for x in attentionMarkers} if attentionMarkers else {}`. Validated on
the allscripts corpus: 10 files changed, all strictly improved (7 to zero failures), all recompile
under Python 2.7; the marker diff's 4 "lost" ids are lambdas formerly orphaned as standalone
top-level defs when their parent failed, now correctly inlined (still recovered). Test:
`ternary_arm_with_make_function`. **The reordered/tail-duplicated variant is also FIXED**
(cfg.rs, `return_points` + `lower_block`'s Jump case): when the deob tail-duplicates the
else-return and reorders blocks, `return X if cond else Y` becomes a then-arm that computes X
and `JUMP_FORWARD`s to a lone `RETURN_VALUE` merge, with an orphan dead `LOAD_CONST None`
stranded between -- `find_reordered_ternaries` rejects it (merge is not right after the then
jump) so the merge lowers on an empty stack -> underflow. Since `Unstacker::start_block` clears
the symbolic stack between blocks and `RETURN_VALUE` returns TOS, any block jumping to a lone
`RETURN_VALUE` block must leave exactly the return value on the stack; lower that jump as
`Return(TOS)` directly. Semantically exact, ignores the orphan, and uniformly recovers
shared-return-via-jump shapes. `mb20e87a8.getRestrictions` recovers as `if cond: return X` /
`return None`; `AchievementSystem.makeMultipleIDS` recovers its multi-return body. Validated on
allscripts: ok 91242 -> 91248 (+6), zero panics, marker net +3 / lost 0, 3 files all strictly
improved and recompiling. Test: `jump_to_shared_return_with_orphan_dead_block`.

**Inline list comp inside a ternary arm is also FIXED** (cfg.rs `pure_ternary_arm`): an arm
like `str([x for x in xs]) if cond else ''` (Entity.toString) holds an inline list comp whose
loop body has `STORE_FAST` (the loop var), which `is_statement_or_control` flags, so the arm
read as impure and the diamond mis-structured as an `if` -> underflow. The comp folds to one
value, so its interior (loop STOREs / FOR_ITER / LIST_APPEND) is not arm statements:
`find_list_comps` already yields the comp-interior offset set, so it is computed before
`find_ternaries` and `pure_ternary_arm` skips any interior offset (the comp's own BUILD_LIST
and the trailing consumer are still checked). Validated on the freshly-deobbed allscripts: ok
91296 -> 91313 (+17), zero panics, marker net +6 / lost 0, 5 files all strictly improved to zero
failures (m150e895e 11->0, SSE_Common.Conditions 10->0), all recompile. Test:
`ternary_arm_with_inline_list_comp`.

**Chained ternaries `a if c1 else b if c2 else d` are FIXED** (cfg.rs + unstack.rs): a
chained ternary nests in the else arm and shares one merge; find_ternaries rejected it
(the outer else arm holds the inner ternary's POP_JUMP/JUMP_FORWARD, flagged by
is_statement_or_control) and the unstacker held only one pending ternary. Fix: (1)
pure_ternary_arm accepts nested ternary control flow converging on the merge (a forward
POP_JUMP within the arm, a JUMP_FORWARD to the merge); find_ternaries already recognises
each diamond independently so all get marked. (2) the unstacker's pending ternary becomes
a Vec stack -- a POP_JUMP whose top pending ternary already has its `then` pushes a new
nested ternary, and resolve_pending at the merge resolves them innermost-first (each takes
the freshly-built nested ternary as its otherwise). GUARD: a real ternary's then arm
produces a value; an empty then arm (JUMP_FORWARD right after the test) is an `if cond:
<empty>` or-chain (`a==x or a==y or ..`), not a ternary -- find_ternaries skips it, else it
underflows (Avatar.onActionFailed regressed without this). getClassification and
BattlePassBonusesHelper.value recover. Validated on fresh allscripts: ok 91313 -> 91384
(+71), now 97.3%, zero panics, marker net +23 / 0 regressions (5 "lost" are sub-exprs now
inlined into recovered chains), 40 files changed (25 improved, 15 same, 0 worse), all
recompile. Tests: `chained_ternary`, `or_chain_if_with_empty_body_is_not_a_ternary`.

The rest of the remaining failures are, by adversarial verification, dominated by genuine
deob corruption that cannot be recovered without fabrication: `symbolic stack underflow` (456)
is the deob having removed a LOAD that fed the stack (e.g. robotparser RuleLine.__str__ is
`('Allow' if self.allowance else 'Disallow') + ...` but the deob deleted the true-arm
`LOAD_CONST 'Allow'`, leaving the stack short -- the const sits unused in the table);
`cfg did not reduce` (213) is now dominated by FOR_ITER-with-no-STORE (the deob peepholed
away `STORE x; LOAD x` of `for x in seq: return x`, so the loop var must be fabricated);
`instruction operand out of range` (138) and `failed to decode` (31) are truncated/garbled
bytecode. The recoverable-without-fabrication remainder is mainly the try-family
(`control flow not yet structured`, ~235, mostly bundled-stdlib try/except/finally
*compositions* and the deob orphan-WITH_CLEANUP bug below) plus small opcode edge cases
(STORE_MAP 14, JUMP_IF_FALSE_OR_POP 30) -- high effort, high regression risk, low
game-code yield.

Top remaining try-family levers (not yet done):
- Falling-through-handler merge-less try (the ~20 the (3) guard still declines): a
  merge-less try whose handler falls through into an enclosing finally/with. To
  recover soundly, `recover_try` must bound the handler arm at the nearest enclosing
  finally/with cleanup target (so the structurer does not absorb the cleanup the
  finally/with structurer also emits) rather than reject. IR-side, additive.
- **Deob over-removal drops a SETUP_WITH (the orphan-WITH_CLEANUP bug):** 50 code
  objects across 34 files have more WITH_CLEANUP than SETUP_WITH in the deob output
  (e.g. tarfile `makefile`, filecmp `_do_cmp`, zipfile `_extract_member`), which is
  structurally invalid bytecode -- the deob dropped a `with`'s SETUP_WITH while
  keeping its WITH_CLEANUP/POP_BLOCK/STORE target. Real source is e.g. `try: with
  bltn_open(targetpath, 'wb') as target: copyfileobj(source, target) finally:
  source.close()`. It is NOT the cross-block dead-operand removal (that pass excludes
  SETUP_WITH -- only `pure_data` opcodes are deleted); the drop is in
  remove_const_conditions' own-block slice or a block-level removal/relinearization
  that discards a block containing the SETUP_WITH as opaque-predicate dead code.
  Scan: `/g/tmp/scan_with.py` over the deob output finds the 50. This is the largest
  single recoverable chunk found but is deob-side (highest risk, regresses all 5093
  files if wrong); diagnose by tracing the deob block removal on `makefile` (the raw
  stage4 is `<name>_stage4.pyc` in the sweep dir, but it is control-flow-flattened
  with junk so a linear opcode scan of the raw is unreliable -- trace the passes).

The biggest remaining buckets, in order: `construct only partially recovered` (a
parent fails when any nested object does, so it shrinks as leaf gaps close, ~2717 --
it also absorbs the module roots the `import *` def-wrap guard now rejects),
`cfg did not reduce to regions` (~554, mostly deob residue and irreducible CFGs) and
`symbolic stack underflow` (~430), the non-merge-less try/with/finally shape
variants (SETUP_EXCEPT ~225/SETUP_WITH ~83/SETUP_FINALLY ~72/END_FINALLY ~57, the
harder cases left after merge-less, the trampoline-split structuring, and the
loop-continue structuring),
`instruction operand out of range` (~134), and cross-block short-circuit
(JUMP_IF_FALSE_OR_POP as a block terminator, ~98). `sweep_stats` now reports the
smallest example per bucket (a minimal repro): the tiny `symbolic stack underflow`
and `failed to decode bytecode` cases are deob over-removal/truncation residue
(genuinely corrupted, correctly rejected), and `cfg did not reduce` includes
degenerate loops like `while 1: break`. The remaining `POP_JUMP_IF_TRUE` (~10) /
`POP_JUMP_IF_FALSE` (~24) cases are inline list comprehensions whose filter is a
short-circuit `or` or whose element is a ternary -- both cross blocks and are not
yet folded (the plain and negated single-condition filters now are). The
IMPORT_FROM/BUILD_CLASS/STORE_MAP cross-block-residue buckets, formerly ~202/188/130,
are now ~29/8/14 after the cross-block dead-operand removal (see below).

Relative imports are recovered by threading the `IMPORT_NAME` level operand through
the IR. The compiler pushes the level (a `LOAD_CONST` int: the leading-dot count for
an explicit relative import, `-1`/`0` for an absolute one) below the from-list, and
the IR discarded it -- so `from . import x` rendered as the invalid `from  import x`,
which emit rejected as `__unrecovered__`, poisoning the whole object. The level
(captured only when it is a plain `Const`) now rides `Expr::Import` -> `PendingFrom`
-> `Stmt::Import/FromImport`, and `import_dots` prepends that many dots at emit time
(bounded to a plausible nesting depth so a corrupt operand cannot drive an unbounded
allocation). Absolute imports prepend zero dots and stay byte-identical. This lifted
coverage 88534 -> 88580; validated by regenerating the whole archive and confirming
every written module is byte-identical to before (the gain is objects that previously
self-rejected on the relative import alone -- they still sit inside modules that fail
for other reasons, so the win is in the per-object metric, not yet in written output).

The unstacker clears the symbolic stack at every block boundary, so any value that
lives across a boundary fails. There were two such classes: the deob-residue cases (a
dict literal, import, or class whose building spans a deob-inserted boundary, or that an
earlier mishandled/dead stack push unbalanced) and the cross-block short-circuit (`a or
b and c` whose OR_POP jumps cross to the merge, often as a ternary then-arm like `X if c
else Y`). The residue class is now largely fixed deob-side by the cross-block dead-operand
removal (the "unsupported opcode STORE_MAP/IMPORT_FROM/BUILD_CLASS" errors were downstream
symptoms of an orphaned junk push burying the real value; removing the junk closure clears
them). The cross-block short-circuit remains the open frontier and needs real,
regression-prone work, not local hacks.

The flat short-circuit-as-ternary-then-arm case (`(a or b and c) if cond else d`) is
now handled (`pure_ternary_arm` accepts an OR_POP that targets the arm's merge, and
the JUMP_FORWARD handler folds the pending short-circuits into the arm value before
capturing `then`). A first attempt that did only the find_ternaries half MIS-EMITTED
(the then captured only the tail operand, swapping arms and folding the else into the
and-chain) -- the JUMP_FORWARD fold is the load-bearing other half. The remaining
short-circuit failures are other cross-block shapes (the OR_POP value crossing a real
block join, not in-block), which still need general cross-block stack propagation:
thread a block's `stack_out` into its successors' `stack_in`, with join handling for
the short-circuit/ternary merge. (The residue cases wanted deob-side dead-stack-
computation elimination so the regions come out clean; that is now the cross-block
dead-operand removal, see the BUILD_CLASS section.) These are load-bearing;
checkpoint-commit and re-sweep before and after, and validate semantically (recompile
is necessary but does NOT catch a mis-emit that still compiles -- compare disassembly
to source). Note also a class of genuinely corrupted residue the IR currently renders
as invalid source rather than rejecting (e.g. `'verbose'(**{unknown_2}=True)` from a
mangled `__main__`); a CALL whose keyword key is not a string constant should reject.

The IMPORT_FROM dead-store residue is now stripped deob-side
(`CodeGraph::strip_import_store_junk`, wired in `deob.rs` after `remove_const_conditions`
per the ordering caveat below). The obfuscator interleaves dead junk stores into a
`from m import a, b` (confirmed present in the raw stage-4, original obfuscation the
deob failed to strip): per import name, `IMPORT_FROM <n>` then a run of `LOAD_CONST <k>;
STORE_NAME <junk>` pairs (junk names are an illegal identifier `:` or a deob `unknown_N`
temp) and finally a value-shadowing `LOAD_CONST <k>` immediately before the real
`STORE_NAME <n>` -- so the store binds the junk const and the imported attribute is left
on the stack and POP_TOP'd. The pass strips everything strictly between an
`IMPORT_FROM <n>` and the matching `STORE_NAME <n>`, leaving `IMPORT_FROM n; STORE_NAME
n` so the store consumes the attribute. Conservative: it only fires when every
instruction between is a `LOAD_CONST` or `STORE_NAME`, and never drops a `STORE_NAME`
whose name index is loaded anywhere in the code object (use-checked). It runs after
`remove_const_conditions` because those junk stores can feed opaque predicates that the
fold consumes. Measured impact: it changed 15 files' deob output (the rest are
byte-identical, the pass being a no-op), all recompile clean, no panics, and recovers
~6 buried imports (e.g. `from AirPlanes import AirplaneUtils`). The headline coverage is
flat because letting those module bodies decompile further exposed a separate corrupted
construct (a mangled `warnings.warn` whose keyword key is a non-string const), which the
companion fix `kwarg_name -> UNRECOVERED` now rejects instead of emitting invalid
`f(**{2}=x)` source. Net: equal `ok` count, strictly more valid output. The buried-
import pattern is rarer than the ~202 IMPORT_FROM bucket suggests; most of that bucket is
downstream symptoms of other residue. Validate any deob change by regenerating the whole
archive (the deob output feeds both the IR and the written .pyc), diffing which
`*_stage4_deob.pyc` changed, and recompiling them; a deob soundness bug regresses all
5093 files. The remaining residue (dead stack pushes before BUILD_CLASS, dict values
spanning a deob-inserted boundary) wants the same treatment, generalized.

BUILD_CLASS / STORE_MAP / IMPORT_FROM cross-block residue -- RESOLVED by precise
provenance plus cross-block dead-operand removal (the two were one bug). Traced shape
(e.g. `class Scout(ConsumableSquadron, Squadron)` in ConsumableSquadrons): the obfuscator
wraps the construct in opaque predicates whose operands are junk arithmetic on `unknown_N`
temps, control-flow-flattened so a junk value is computed in one block but its `COMPARE`/
`POP_JUMP` lands in a LATER block (cross-block operand). The raw is balanced (every junk
value consumed by a predicate). `remove_const_conditions` folded the predicates but
removed only each condition's OWN-block slice, leaving the cross-block COMPARE that pushed
the bool -> the value orphaned on the stack -> the next real construct (`BUILD_TUPLE`
bases, a `STORE_MAP` dict, an `IMPORT_FROM`) captured junk and the IR rejected it.

The root cause was an imprecise access tracker: `InstructionTracker` shared its
`Vec<AccessTrackingInfo>` by `Arc` on clone, so a condition's instruction set picked up
unrelated live instructions (this is what stripped validateAndParseCmd in
processConsoleCommand) and the deob could only safely strip the own-block slice. Fixed in
two committed stages:

1. `fix(smallvm): precise per-value provenance` -- the tracker is now a value type (clone
   deep-copies, combining unions), and LOAD_FAST/LOAD_NAME no longer record the consuming
   load on the table entry. `path_instructions` is now exactly a folded condition's
   def-use closure. Net: 87177 -> 87186, three files changed (each a live operand the old
   tracker wrongly stripped, now kept).
2. `feat(deob): cross-block dead-operand removal` -- remove the whole closure's DATA
   instructions across all blocks (not just the own-block slice), guarded so it stays
   sound: only side-effect-free binds/reads/arith/compares/builds are deleted (a closure
   touching a call/attr-store/import is left to the own-block path); jumps in the closure
   are tolerated but never removed (they wire the flattened blocks); a store is deleted
   only if its name is read nowhere outside the closure set (liveness, so a bind feeding
   live code survives); and `deobfuscate_code` re-decodes the result and retries once with
   cross-block removal disabled if a jump lands mid-instruction (`bytecode_structurally_valid`).
   UNPACK_SEQUENCE is allowed (junk always binds all its outputs to temps); DUP_TOP/X are
   not. Net: 87186 -> 87700; BUILD_CLASS 188->8, STORE_MAP 130->14, IMPORT_FROM 199->29.

Validated by regenerating the whole archive, recompiling every changed `.py` under Python
2.7 (zero new failures), and source-diffing: of 5093 files 3541 have byte-identical
recovered source (the removal is transparent), the rest recover more, and two stdlib files
regress one method each to a graceful `symbolic stack underflow` comment. Remaining
BUILD_CLASS/STORE_MAP/IMPORT_FROM cases (8/14/29) are closures the guards conservatively
decline (a junk var that is also read by live code, or a closure with a non-pure opcode);
the next lever there is forward-consumer analysis so a partially-shared UNPACK or a
call-bearing closure can be removed exactly, or a CFG stack-depth validator to replace the
structural re-decode check with a semantic one.

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
