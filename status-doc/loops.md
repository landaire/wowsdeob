# Loop recovery

IR structuring for while/for loops, breaks, and for/while-else.

**Loop-containing-try/except (CFG-not-reduced) -- LANDED +40 (unfuck f2b063af, 75 -> 43).**
`infinite_loop_body_inner` (structure.rs) rejected a Try terminator at the loop header; now it structures
the try like region()'s Try arm with follow=Block(target(end)) (end = the loop header, so the protected
body falls back to the loop top). Recovers the common `while True: try: ... except E: continue/return`
idiom (multiprocessing.forking waitpid loop matches canonical). +40, 20 files changed, 0 reg, 0 recompile
failures (isolated re-dump validation). RESIDUAL: the break-INTO-loop-exit subset (test_bsddb `unknown_14`,
forking.wait) is a separate harder tangle -- the BREAK_LOOP in the handler resolves wrong (`break_targets`
cfg.rs ~2800 sets fallback = instr-before-SETUP_LOOP-follow, but that is a DEAD `JUMP_ABSOLUTE <header>`
block, not the real exit; the real exit isn't a leader; AND the END_FINALLY-edge-remap points the
unmatched-reraise at the same dead block) -> BadOperand. A 3-way tangle (break-resolution + leaders +
end_finally_remap); declined for now, still graceful. See push-to-100-percent memory for the full map.

**While-True loops whose header breaks** (+1): `while 1: <stmts>; break` whose loop header block ends
in `BREAK_LOOP` (optimized, no POP_BLOCK) was rejected -- the infinite-loop structurer only accepted a
Jump/Fallthrough header and could not find the loop exit (the break's edge is its fallback = the back
edge). Now handles a `Break`-terminated header and derives the follow from the break it carries, so
`while True: break` recovers with the after-loop code intact. Rare shape (the read-loop test-header
case is handled separately), but a clean correctness fix.

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
