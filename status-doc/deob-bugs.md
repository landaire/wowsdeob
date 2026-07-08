# Deobfuscator bugs and root-causes

Root-caused deobfuscator defects (relinearizer, dangling jumps, decoder tables) and their fixes.

**The 142 stack-underflow bucket is CROSS-BLOCK/scramble, confirmed via instrumentation.** Probed
`pulldom.processingInstruction` (DBG_STEP env in unstack.rs step()): underflow at a `CALL_FUNCTION` entering
a block with stack_depth=0 -- a call expression split across an if-merge where the two predecessors reach the
merge with inconsistent stacks (one empty, one mid-expression). Same hard class as the email/ttk scrambles;
the per-block unstacker doesn't carry partial expressions across block boundaries. Not a cheap lever.

**DEOB dangling-jump bug FIXED (+59, 98.5% -> 98.6%, unfuck 53827bca).** The root cause below was fixed in
`ensure_terminal_returns` (code_graph.rs): a leaf block (no successor) can end in an unconditional jump whose
target was eliminated during deob (a shared return de-shared away), leaving the jump DANGLING. The pass
appended `LOAD None; RETURN_VALUE` AFTER it, producing `...; JUMP_FORWARD; LOAD None; RETURN` -- a jump that is
no longer the last instruction, so `update_branches` (which only retargets a block's last instr) left its STALE
operand, which after relayout pointed mid-expression. FIX: drop the dangling unconditional jump before
appending the return (a leaf has no successor, so `return None` is the correct terminal). VALIDATION (the
required full cycle for any deob change): re-deob the whole 4215-file/71603-object corpus (`deob_archive`),
dump IR before+after, compare in ISOLATION (snapshot old-deob IR, re-deob, diff) -- +59 recovered,
stack-underflow 142->112, 30 files changed, ZERO regressions, zero new recompile failures; encode_7or8bit and
ttk.destroy match canonical-equivalent. Remaining stack-underflow (112) are OTHER causes (genuine cross-block
value splits, py2_test_grammar testAssert). Repro/debug the deob: `UNFUCK_WRITE_GRAPHS=1
target/release/examples/full_deob.exe <in_stage4.pyc> <out>` writes per-phase DOTs; read the `offsets` (final)
phase. The original investigation that pinned it:

**The stack-underflow (142) + SETUP_EXCEPT (52) "scrambles" were a DEOB RELINEARIZER BUG, not obfuscation
(2026-06-05, root-caused -- ~194 objects, the single highest-value remaining lever).** These failures are a
forward jump landing in the MIDDLE of an expression (ttk `LabeledScale.destroy`: `except: pass` -> a bare
`CALL_FUNCTION`; email `encode_7or8bit`: except -> mid-else `STORE_SUBSCR`). PROOF it is the deob, not the
obfuscator: disasm the PRE-deob `*_stage4.pyc` (vs `*_stage4_deob.pyc`) -- in BOTH ttk and encode the
pre-deob except correctly jumps to the function's RETURN, skipping the else/cleanup. The deob's relayout
moves blocks but the except's jump ends up pointing at the wrong (mid-expression) node. EXACT MECHANISM PINNED via the `offsets`-phase DOT (`UNFUCK_WRITE_GRAPHS=1 full_deob email/encoders_stage4.pyc`,
code object 135936035911295): the except-handler node is `POP_TOP*3; msg['CTE']='8bit'; JUMP_FORWARD 11; LOAD
None; RETURN_VALUE` -- i.e. a `JUMP_FORWARD` that is NOT the block's last instruction (dead `LOAD None; RETURN`
trails it). `update_branches` (code_graph.rs ~1909-1916) only retargets a node's LAST instruction and bails
when it is not a jump (`RETURN_VALUE`), so the mid-block `JUMP_FORWARD` is NEVER retargeted and keeps its STALE
pre-deob arg (11 -> offset 95). TWO compounding defects: (1) a block has live code after an unconditional jump
(should end at the JUMP, or the dead trailing return removed); (2) the else and the function return are merged
into ONE node (`89 '7bit' store ... 99 LOAD None; RETURN`), so the except's true target (the shared return at
99) is not its own block -- in the pre-deob the except correctly jumps to the standalone return, and both the
else fall-through and the except converge there. So a one-line `update_branches` tweak is NOT enough (retarget
to the else node's start would make the except re-run the `7bit` store); the real fix is in block
construction/relayout: keep the shared return a separate leader and don't leave a stranded mid-block jump.
HIGH RISK: the deob output feeds ALL 71603 objects, so any fix needs a full-corpus re-deob + per-object
regression + recompile-all sweep before landing. Reframes ~194 objects from "unfixable obfuscation" to a deob
CFG fix -- by far the biggest remaining coverage lever, but a dedicated, carefully-validated effort.

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
