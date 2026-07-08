# Opaque predicate and marker-junk folding

Deob and IR work that folds control-flow-flattening opaque predicates and marker junk.

**CONTROL-FLOW-FLATTENING predicate direction IS PROVABLE -- dead never-taken predicates FOLDED (+50 honest
-> 69219/71603 = 96.67%, +10 modules; unfuck "fold dead constant-integer opaque predicates" commit,
2026-06-06).** The prior frontier note (and many memory dead-ends) assumed these predicates' direction was
unprovable. It is NOT: the marker block grinds its 5 integers through arithmetic into a COMPARE whose BOTH
operands are junk-derived constants (the `realval` it looks like it compares actually LEAKS -- the real value
is wedged-apart, consumed by a later op). So the comparison is a CONSTANT and the branch direction is
provable by evaluating the marker arithmetic. Sweep: of the marker->COMPARE->POP_JUMP predicates, 74 are
self-contained constant & NEVER-taken (across 63 files; essentially all integer-only), ~121 are constant &
always-taken (set-based, see below), 5 genuinely use a runtime value. FIX (`fold_dead_marker_predicates`,
cfg.rs, run in decode before strip_opaque_predicates): evaluate the marker arithmetic with Python-2 integer
semantics (floor div/mod); when the predicate is self-contained (stack returns to empty at the COMPARE,
touching only its own unpacked temps) AND provably not taken AND its temps are dead outside, NOP the whole
stack-neutral region -- restoring the statement it was wedged into and dropping the dead edge into the
flattening trampoline. Bails on ANY value it can't fully evaluate as a known integer, so direction is never
guessed (silent-wrong avoided by construction). VALIDATED: 0 per-object regressions, +10 modules, all
recompile, AccountUnlocksParams's `for unlockId,(name,_) in UNLOCKS.iteritems(): UNLOCK_NAMES_TO_IDS[name]=
unlockId` recovers exactly, SimpleHTTPServer/fileinput match canonical stdlib. Test
`dead_constant_integer_predicate_is_folded`. REMAINING in this family: the IMPORT_FROM incomplete-unpack import hijack (junk `STORE` absorbed by
`pending_unpack`) and STORE_MAP dict-interleaved junk still need a junk-vs-real-name discriminator.

**ALWAYS-TAKEN set predicates ALSO FOLDED -- as a pure NOP, no edge redirect (+42 honest -> 69261/71603 =
96.73%, +12 modules; unfuck "fold always-taken set opaque predicates" commit, 2026-06-08).** The second
flattening shape: the obfuscator grinds the marker integers into two junk SETS whose comparison is a constant
True, feeding a POP_JUMP that ALWAYS jumps over a dead fall-through to the real continuation (e.g. a junk
set-predicate wedged between `LOAD __name__; LOAD '__main__'` and the real `==` of `if __name__ ==
'__main__':`). KEY INSIGHT that made it safe (vs the feared edge-redirect): the always-taken jump lands at
`target` with the pre-marker stack intact, so NOPing the WHOLE `[marker, target)` span (predicate AND dead
fall-through) makes control fall through to `target` with that same stack -- a PURE NOP, no control-flow
change -- gated to a forward `target` that no instruction outside the span jumps into (so the NOP'd dead
fall-through is provably unreachable). `eval_marker_predicate` now models integer-sets (BUILD_SET, &|^ as
intersection/union/symmetric-difference, comparisons as Python-2 (proper) subset/superset/equality) via the
`CmpOp` enum. Direction stays provable by evaluation -> never guessed. VALIDATED: 99 ir_m1 tests, 0
per-object regressions, +12 modules, all 63 changed files recompile, base64 recovers `if __name__ ==
'__main__': test()` exactly (canonical), KeyTargetsConfig (game) full faithful module. The marker-predicate
control-flow-flattening family (both never-taken integer and always-taken set) is now folded; what remains is
the IMPORT_FROM/STORE_MAP junk-vs-real-name discriminator and genuinely-runtime predicates (~5).

**Dead predicates with un-packed (non-marker) junk ALSO folded (+277 honest -> 69538/71603 = 97.12%; unfuck
"fold dead constant predicates with un-packed junk setup" commit, 2026-06-08).** The obfuscator also loads
the junk integers INDIVIDUALLY (`LOAD_CONST <int>; STORE_NAME <temp>` repeated) instead of packing them into
a marker tuple + UNPACK -- the same self-contained constant predicate, no tuple signature.
`eval_marker_predicate` now accepts either start; the un-anchored form additionally requires >= 2 const-store
temps and real arithmetic (`MIN_PLAIN_STORES` / `saw_op`, so a plain `x = const` never matches), with the
all-temps-dead-outside check as the binding safeguard. The fold stays semantically correct by construction
(self-contained + provably-constant + dead temps), so direction is never guessed. 0 per-object regressions;
glob/base64 recover with every real `if` intact. Test `dead_predicate_without_marker_tuple_is_folded`.

**NESTED/interleaved marker predicates FOLDED (+43 honest -> 69581/71603 = 97.18%, +11 whole modules; unfuck
"fold nested/interleaved marker opaque predicates" commit, 2026-06-08).** The obfuscator nests marker
predicate blocks: a complete inner predicate's `UNPACK`/stores are wedged between two of an outer block's own
unpack stores (ConfigParser: outer `marker; UNPACK 5; STORE 28,29` ... inner full predicate ... `STORE
30,31,32` then the outer's own COMPARE/POP_JUMP). Folding the inner block to NOPs is stack-neutral but left
the outer unfoldable: `fold_dead_marker_predicates` made a single top-down pass (never revisiting the outer),
and `eval_marker_predicate` bailed at the NOPs the inner left between the outer's pushed values. Two safe-by-
construction fixes (eval is pure constant evaluation, never guesses direction): `eval_marker_predicate` skips
`NOP` in its scan, and `fold_dead_marker_predicates` iterates to a fixpoint (fold inner -> exposes outer ->
fold next pass). ConfigParser/FL/cookielib/tokenize/test_bisect/genericpath/sysconfig/... recover whole and
match canonical stdlib exactly. 0 per-object regressions, sweep 70813->70825, 0 panics, all 12 changed
recompile. Test `nested_marker_predicates_are_folded`. FRONTIER after this: the clean FORWARD constant-predicate
vein is now FULLY MINED OUT at 97.18%. The residual marker junk in failing roots is the documented-hard tail --
predicates whose COMPARE's POP_JUMP targets BACKWARD (control-flow-flattening trampolines: CDROM 794->171,
transformer 581->305), dict-interleaved junk left on the stack with no COMPARE (`STORE_MAP`, SlotDataProvider),
junk temps reused across blocks with cross-jumps into the span (AllOrNothing), and unbalanced multi-marker
predicates -- all needing flattening reversal or full dataflow taint (both high-risk, repeatedly reverted).
The hypothesized "incomplete-unpack-pure-residue (residue leaks)" form does NOT occur in the failing corpus.

**Value-junk strip un-blocked by a pydis sign fix + made sound with a stack-validity gate (unfuck "ir: gate
opaque-junk strip on stack validity" commit + pydis "Fix BUILD_TUPLE/LIST/SET stack adjustment sign" commit,
2026-06-08).** A survey of the "unsupported opcode" fallback buckets (STORE_MAP/BUILD_CLASS/IMPORT_FROM) traced
them to marker VALUE-junk -- a `LOAD_CONST <5-int marker>; UNPACK 5; STORE x5; <set/int arithmetic>` block whose
residue is left on the stack and buries a real operand (e.g. it displaces the value tuple inside a `{k: (a,b)}`
dict literal, so the following `STORE_MAP` sees a non-dict). `strip_opaque_predicates`/`opaque_block_end`
already targets this form via a depth simulation, but it was silently defeated: **pydis 0.5
`stack_adjustment_after` returned the wrong sign for `BUILD_{TUPLE,LIST,SET}` (`arg - 1` instead of the
collapsing `1 - arg`)**, so a `BUILD_SET` in the junk arithmetic inflated the simulated depth and the below-entry
consumer that bounds the block was never detected -> the junk survived. Fixed in pydis (now wired into unfuck via
`[patch.crates-io] pydis = { path = "../pydis" }`). Correcting the sign alone REGRESSED two module roots
(recovered -> underflow), so two safeguards were added to `opaque_block_end`: (1) stop the block before an empty
`BUILD_*` (arg 0) -- it consumes nothing, so it is a real empty-collection producer (`name = []`), never junk;
(2) a stack-validity gate -- a below-entry collection consumer is only stripped when the real stack depth below
the block entry (`straightline_entry_depth`, computed only when the prefix is provably straight-line, with
correct per-opcode effects) leaves it satisfiable, distinguishing junk that DISPLACED a real operand (safe) from
junk ADDED to a `BUILD_LIST n` bumped element count (would underflow). Result: ZERO per-object regressions on both
the canonical `deob_guard/scripts` corpus (byte-identical failure set, still 97.18%) and the broader game-script
corpus, where it recovers value-junk dict/tuple literals (+19 whole modules across the wider tree, e.g.
ModsShell `BattleResultUtils`' large `BATTLE_RESULT_EXTENSION_FIELDS` dict -- verified clean, recompiles under
py2.7). NB the canonical metric is FLAT: this pattern's failing files live in the game scripts, not the curated
guard set. Tests `strips_opaque_predicate_feeding_a_tuple`, `opaque_junk_feeding_empty_build_is_not_stripped`.
FRONTIER: the gate bails on ANY control flow in the prefix, so it loses wins whose module preamble has a
conditional import (`if not IS_CLIENT: from ... import ...`, e.g. HttpClientUtils STORE_MAP); recovering those
needs a sound cross-branch depth (a small pre-CFG depth pass that verifies join consistency), since a naive
linear pass over an unfolded opaque predicate in the prefix would silently accept a bad strip.

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

**Out-of-range dead predicates STRIPPED (+9, unfuck b3515409).** A scan of the deob output found 27 module
bodies (`unknown_0`) with a conditional jump landing on an INVALID offset (past end / mid-instruction) --
opaque predicates the deob's marker-tuple strip misses (e.g. cookielib `LOAD; LOAD; INPLACE_MULTIPLY;
DUP_TOP; POP_JUMP_IF_TRUE <past-end>`). The IR cannot resolve the CFG edge -> the whole module body fails.
Extended `strip_degenerate_predicates` (already handled jump-to-fall-through) to also strip a jump to an
invalid offset; reordered decode() so strip_opaque_predicates (marker-tuple form) runs FIRST, then the
generic out-of-range strip. +9 (stack-underflow 112->108), FiniteStateMachine recovers cleanly, 0 reg, 0 new
recompile failures. The other ~18 have a DUP-style predicate that leaves a buried value on the stack
(os2emxpath, wintypes -> still underflow) -- a separate buried-junk shape, fail gracefully. Scan tool:
`/g/tmp/scan_badjump.py` (jumps to non-instruction offsets). BURIED-JUNK explored + REJECTED: those
predicates build a set, do junk set ops, COMPARE, jump past-end, netting +1 (buried junk) with a STORE
interleaved -- not a self-contained run the backward-strip can isolate. A POP_TOP fallback (exact, since the
branch is never taken) recovered only +2 and left the obfuscator's junk (dead `{...}` comparisons, junk
stores) as recovered source = UNFAITHFUL; reverted (honest failure beats junk output). Proper fix = a
self-contained-block remover (backward stack-sim from the dead branch, remove only if provably balanced +
side-effect-free); risky, deferred.

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
