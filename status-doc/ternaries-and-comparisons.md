# Ternaries and chained comparisons

Recovery of ternary expressions and chained comparison operators.

**Chained comparisons feeding a relinearized branch recovered (unfuck "ir: recover chained comparisons that
feed a relinearized branch" commit, 2026-06-08).** `find_chained_comparisons` recognized only the contiguous
VALUE form of `a <= b <= c`: the final comparison's `JUMP_FORWARD <merge>` sits right before the
`ROT_TWO; POP_TOP` short-circuit cleanup. When the chained comparison is a branch CONDITION (`if a <= b <= c:`),
the relinearizer displaces that cleanup to AFTER the consuming `POP_JUMP_IF_*` and reaches it with
`JUMP_ABSOLUTE <consumer>` (the short-circuit-taken path), while the fall-through reaches the consumer directly.
The `JUMP_IF_FALSE_OR_POP` was then left unrecognized -> the unstacker rejected it ("unsupported opcode
JUMP_IF_FALSE_OR_POP", ~30 functions on the canonical corpus). FIX: also recognize that branch form -- a
`JUMP_IF_FALSE_OR_POP` whose target is `ROT_TWO; POP_TOP; JUMP_ABSOLUTE <consumer>` with `<consumer>` a
`POP_JUMP_IF_*` -- overriding the short-circuit merge to the consumer and excluding the displaced cleanup. ZERO
regressions across both corpora (canonical: 16 per-object wins; broader /g/tmp: 206, 1M+ objects), all verified
clean and recompiling under py2.7: `parse_starttag` (`s[:1] == "'" == s[-1:]`), `_DockProxyClient__receiveForced
PortsList` (`a <= getServerTime() <= b`), `_init_board` (`0 <= x+dx < w` in a list comp), the datetime aware-
comparison tests. NB canonical honest metric is FLAT (97.18%): the touched modules carry OTHER unrecovered
constructs (flattening, etc.), so a recovered chained comparison alone does not complete a whole module -- this
is an output-quality win (more methods recover within partially-recovered modules), not a headline-count move.
Test `chained_comparison_feeding_a_branch`. NB the tight `ROT_TWO; POP_TOP` cleanup signature (specific to a
chained comparison's short-circuit) keeps it from false-matching ordinary `and`/`or` short-circuits.

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

**Nested ternary in a ternary's value region** (`d[k1 if c else k2] if outer else e`,
axisMove): the outer then-arm computes a subscript whose key is an inner ternary. Two
fixes -- (1) pure_ternary_arm now accepts a JUMP_FORWARD whose target is WITHIN the arm
(a nested sub-ternary's own merge), not only the shared outer merge; (2) the unstacker
distinguishes an `and`-chain from a nested ternary by ELSE TARGET (an `and`-chain shares
the pending ternary's else target; a nested ternary in the key region, also before the
outer `then` is set, branches elsewhere) instead of the old `then.is_none()` heuristic.

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
