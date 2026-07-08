# Metrics and corpus notes

Coverage metrics, corpus locations, and measurement caveats extracted from the AGENTS.md changelog.

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
regenerate: `G:\deob\scripts.zip`. **Now 70718/71603 = 98.8% (per-object sweep)** after the merge-redirect,
narrowed merge-less-try, decorated-renamed-method, degenerate-predicate, empty-finally, nested-finally,
END_FINALLY-edge-remap, and `assert`-recovery fixes below.

**TWO metrics, and the per-object sweep is NOT the artifact-faithful one (2026-06-06).** `sweep_stats`
decompiles every code object standalone via `decompile_function`, which wraps it in a `def`. That
MISMEASURES the kinds the real `decompile_module` pipeline never wraps: a module ROOT holding `import *` or
`from __future__` (illegal in a `def` -> counted as a failure though it recovers perfectly as a module), and
class bodies (a `def`-wrapped class body can "succeed" as bogus source). The new `honest_stats` example
mirrors the real artifact: a file whose ROOT recovers as a module body has every nested object inlined
marker-free (else `decompile_module_body` would fail), so it counts them all; otherwise it falls back to the
per-object path. Honest number: **68887/71603 = 96.2%**, with **349 "fallback" modules** where the root fails
and the WHOLE module degrades to standalone per-object dumps -- losing every class/module body to a `#
... not recovered` marker (2680 bodies forfeited corpus-wide before the assert fix). THE LEVER: one failing
root poisons ~7 bodies on average, so rescuing a single root recovers a whole module. Fallback causes by
bodies forfeited: partially-recovered (nested class body fails) 192f/1298b, root underflow 94f/912b,
SETUP_EXCEPT 50f/322b, STORE_MAP, END_FINALLY (mailbox 29b), etc. Run `honest_stats G:/deob_guard/scripts`
for the live breakdown; it is the metric to optimize, not the sweep.

**The deob is DETERMINISTIC -- the "non-determinism" was a STALE-BINARY artifact (2026-06-05, RESOLVED).**
Earlier the count appeared to swing 70630..70670 across re-deobs. ROOT CAUSE: a `cargo build --example X`
rebuilds only X; after reverting a change I rebuilt `sweep_stats` but not `dump_dir` (or vice versa), so a
measurement ran a binary that still had the reverted change compiled in. Three full deob_archive+sweep
rounds with all-examples-rebuilt give 70630 every time; two re-deobs produce byte-identical output. The +40
"swing" was the loop+try structurer change (below) still in the binary. LESSON: ALWAYS `cargo build
--release --examples` (all) after a revert/change before measuring; never trust a single-example rebuild
when validating. The deob and IR are both deterministic on a fixed corpus.

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
