# Readability and faithfulness fixes

Output-quality fixes: deduplication, docstrings, constant rendering, and junk-name handling.

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
