# Classes, decorators, and imports

Recovery of class bodies, class-base junk, decorated methods, and import idioms.

**From-import bound to a closure cell RECOVERED (+167 honest -> 69169/71603 = 96.60%, +14 modules; unfuck
"bind a from-import target stored to a closure cell" commit, 2026-06-06).** The conditional-import idiom
`try: from hashlib import md5 as _hash_new except ImportError: from md5 import new as _hash_new` binds via
`STORE_DEREF` when an inner function captures `_hash_new` (a closure cell). `emit::import_binding` only
resolved `STORE_NAME`/`STORE_FAST`/`STORE_GLOBAL` targets, so the deref target rendered as
`from hashlib import __unrecovered__`, failing the enclosing function and poisoning its module to per-object
fallback. Fix: resolve a `LValue::Deref` import target against `co_cellvars`/`co_freevars` (new
`raw_derefname` helper returning the unsanitized name, mirroring the other branches). Rescued the
hashlib/md5/sha fallback across Crypto.Hash (MD5/SHA1/...) and similar; MD5 recompiles and matches canonical
PyCrypto. 0 per-object regressions, +14 modules, test `from_import_bound_to_closure_cell`. NOTE: the build
also needed a one-line fix -- the deps bump left `[dev-dependencies] pydis = "0.4"` while `[dependencies]`
moved to `0.5`, so a clean build of examples/tests hit E0464 (two pydis rlibs); aligned the dev-dep to 0.5
(the local `[patch.crates-io]` for pydis/py27-marshal is now commented out -- the fixes were published to
crates.io 0.5/0.6, and honest_stats is byte-identical to the patched build, so no decoder regression).

**CLASS WRAPPERS preserved when a module only partially recovers (unfuck "preserve class wrappers" commit,
2026-06-08).** Previously, one unrecoverable nested object (e.g. a single failing method) made
`decompile_module` fall straight back to FLAT per-object dumps -- every `class name(bases):` wrapper lost to a
`# ...: class or module body, not recovered` comment, its methods spilled out as top-level functions. Added a
middle tier `decompile_module_body_lenient`: when the root still STRUCTURES, emit the whole-module form (real
structure, class wrappers, the methods that did recover), stubbing only the unrecoverable objects in place; the
flat dump is now only the last resort for a root that cannot be structured at all. A failed def/class stub is a
one-line `def <name>(): __unrecovered__` / `class <name>(bases): __unrecovered__` so it stays valid even right
after a decorator (a bare marker would dangle -> SyntaxError). The strict `decompile_module_body` (the
honest-coverage metric) is unchanged, so honest/sweep numbers are identical; this is an OUTPUT-QUALITY win:
~201 modules now keep their class structure (e.g. m21292a9a recovers `class Result(object)`/`class Ok(Result)`
/`class Err(Result)` with methods, one stub), 0 per-object regressions, 0 new recompile failures (cgi
exec-in-nested-func is pre-existing). Test `module_keeps_class_wrapper_when_a_method_fails`. NB the honest
metric counts these as still-"fallback" (they contain a marker); the gain is faithful class structure, not the
headline count. FOLLOW-UP ("annotate unrecovered stubs" commit): the stubs now carry the failure reason as a
trailing comment -- `def <name>(): __unrecovered__  # control flow not yet structured (SETUP_FINALLY)` -- so a
preserved class body documents why each method was lost (readers + future recovery work).

**Class-bases opaque junk: keep the `BUILD_TUPLE` (+34 honest, 8 whole modules; honest 68887->68921 = 96.25%,
sweep 70718->70725; unfuck `keep class-bases BUILD_TUPLE` commit, 2026-06-06).** The first lever from the
post-assert "partially-recovered" bucket. The obfuscator wedges an opaque-predicate junk block between a
class's base loads and its bases `BUILD_TUPLE`, with a trailing junk-temp load (or set/arith result)
displacing the real base as the tuple's operand: `LOAD_CONST 'C'; LOAD_NAME Base; <marker unpack + set/arith
grind over junk temps>; LOAD_NAME <junk>; BUILD_TUPLE 1; LOAD_CONST <code>; MAKE_FUNCTION 0; CALL_FUNCTION 0;
BUILD_CLASS`. `strip_opaque_predicates`' forward scan treated the `BUILD_TUPLE` (a `pure_value_pops` op) as
in-block and removed it along with the junk, leaving a bare-name base; `class_header` only accepts a `Tuple`
(or empty-tuple const) bases, so the class became `__unrecovered__` and poisoned the whole module to
per-object fallback. FIX (`opaque_block_end`, cfg.rs): end the junk run *before* a `BUILD_TUPLE` that is
immediately followed by the class-creation tail (`LOAD_CONST; MAKE_FUNCTION 0; CALL_FUNCTION 0; BUILD_CLASS`,
via `is_class_bases_tail`); the `BUILD_TUPLE` then survives to wrap the real bases left below the removed
junk -- correct for ANY base count (the obfuscator preserves the tuple's arg). Only fires inside an
already-recognized marker run (`saw_op && depth >= 1`), so a clean class is never touched. Validation: 0
per-object regressions, 8 modules rescued (Launchpad, ConsumableItemInfo, ArtilleryGun, euc_kr, test_anon,
m37c8858f, m1f87630f, result_screen), all recompile; eyeballed every rescued class header against the
bytecode bases. **euc_kr matches canonical CPython `encodings/euc_kr.py` EXACTLY** -- incl. multi-base
attr-chain bases `class StreamReader(Codec, mbc.MultibyteStreamReader, codecs.StreamReader):`. Test
`strips_opaque_predicate_wedged_in_class_bases`.

**Class junk wedged BEFORE the bases too (+81 honest -> 69002/71603 = 96.37%, +8 modules; unfuck "strip opaque
junk wedged before class bases" commit, 2026-06-06).** A companion shape: the obfuscator also wedges the
self-contained marker junk BEFORE a class's real base loads (shape B: `LOAD_CONST name; <marker; UNPACK 5;
only 2 STOREs -> 3 residue values>; LOAD_NAME Base; BUILD_TUPLE 1; tail`) or even before the name LOAD_CONST
(shape C: `<marker + set grind -> set5>; LOAD_CONST name; LOAD_NAME Base; BUILD_TUPLE 1; tail`). The forward
scan correctly ends the junk block at the real base load, but that boundary (LOAD_NAME/LOAD_GLOBAL/
LOAD_CONST) is not an `is_safe_consumer`, so `opaque_block_end` bailed and the junk stayed. FIX
(`followed_by_class_construct`, cfg.rs): accept such a boundary when the boundary op is a fresh load (pushes
without consuming the junk residue -- a `LOAD_ATTR`, which pops, is rejected as a boundary though it may
appear later as `mod.Base`) leading through only base-load ops into a class-bases `BUILD_TUPLE` + creation
tail. KEY CORRECTNESS: removing a self-contained block (depth never below entry, temps dead) that sits
before an INTACT class construct is always stack-safe regardless of the residue count -- it leaves the real
name+bases below for a balanced BUILD_CLASS; the existing trailing-LOAD_CONST trim preserves the class-name
const for shape C. Validated: 0 per-object regressions, +8 modules (BattleLogicComponentsConstants's
`class ModifierSource(object):`, ShipAcesCellHistory(SynchronizedComponent), GOGContext(IContext), Rewards,
ConsumableUsage, StartManeuver, ...), all recompile, eyeballed headers vs bytecode bases. Test
`strips_opaque_predicate_before_class_bases`. Session total for class-junk: 68887 -> 69002 (+115 honest, 16
modules). RESIDUAL same-bucket: a junk run whose displacing op before `BUILD_TUPLE` is a real `LOAD_ATTR` of
a junk temp (shape-A variant, scan stops at the popping LOAD_ATTR), plus the import/store/dict-interleaved
junk -- still open.

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
