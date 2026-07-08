# try / except / finally recovery

IR structuring work for exception handling and finally cleanup.

**`assert` statements RECOVERED (+149 honest objects, +16 whole modules; unfuck `assert`-recovery commit).**
`assert test[, msg]` (and the bytecode-IDENTICAL `if not test: raise AssertionError`) lowers to a branch
that jumps over a `raise AssertionError[, msg]` when the test holds. The structurer rendered it as `if test:
<rest> [else: raise]`, which (a) lost the construct and (b) trapped a class body's implicit `return locals()`
inside the `if` arm -- tripping `class_body_source`'s `contains_return` guard, so the class failed to recover
as a body and POISONED its whole module (e.g. AirplaneConstants forfeited all 24 bodies). Fix: a
post-structuring pass (`structure::recognize_asserts`) folds both renderings -- the else-arm form and the
sibling-raise form (where the taken arm leaves the block) -- back into a new `Stmt::Assert`, splicing the
taken arm inline. The message form is handled too: `assert test, msg` compiles to a `raise
AssertionError(msg)` CALL (`LOAD AssertionError; LOAD msg; CALL_FUNCTION 1; RAISE_VARARGS 1`), so the
recognizer matches both a bare `AssertionError` name and a single-positional-arg `AssertionError(...)` call.
Faithful (the `if not test: raise AssertionError` lowering is indistinguishable, so `assert` matches source);
548 corpus modules now emit `assert` and ALL recompile cleanly; httplib `assert self.chunked != _UNKNOWN` is
verbatim canonical. CAUTION found while validating: difflib `_plain_replace` recovers `assert alo < ahi`
where canonical has `assert alo < ahi and blo < bhi` -- the `and blo < bhi` was an obfuscator opaque
predicate that became a DEGENERATE test (both arms reach the same block) and `simplify()` folds it away
BEFORE structuring, so the `If` cond never had it. That loss is pre-existing (the old `if/raise` output
dropped it identically) and is a DEOB matter, NOT caused by the assert pass -- the pass takes the cond
verbatim. Three `asserts_*` snapshot fixtures lock the behavior.

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

**Merge-less-try rejection narrowed (+3, whichdb byte-exact).** `recover_try` rejected every merge-less
try whenever the object contained ANY SETUP_FINALLY/SETUP_WITH (to avoid double-emitting an enclosing
cleanup). Narrowed to an ACTUALLY-enclosing cleanup: one whose SETUP precedes the SETUP_EXCEPT and whose
protected range (its branch target) extends past it. Recovered whichdb byte-exact and urllib.retrieve
(previously `# control flow not yet structured (SETUP_EXCEPT)` stubs); retrieve's read loop is still
branch-duplicated (the residual above) but recompiles and is equivalent -- strictly better than the stub.
