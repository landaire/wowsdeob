# wowsdeob decompiler issues (found during WoWS aim-bug investigation)

Each entry: a case where the decompiled `.py` does NOT match the stage4 bytecode.
Verify with: `/c/python27/python2` + stdlib `marshal`/`dis` on `*_stage4_deob.pyc`
(skip 8-byte pyc header). The game is Python 2.7 (magic `f303`).

---

## RESOLVED 2026-06-23 — Issues 1 and 2 (float consts rendered as 0.0)

Root cause was NOT a const-index/off-by-one bug (that hypothesis below was a red
herring). It was the float renderer: unfuck `emit.rs::render_float` ran every
NON-integer float through a `to_i64` truncation, so 0.5 / 0.1 / 0.0001 all became 0
and emitted "0.0". A genuine 0.0 const in the same `co_consts` (e.g. a `>= 0.0`
operand) is whole-valued, so it took the correct `fract()==0.0` branch and rendered
fine -- the two printing "0.0" for different reasons looked like a wrong-slot lookup.

Fixed in unfuck (commit `ir: emit -- render non-integer float consts with their exact
value`); non-integer floats now use Rust shortest-round-trip formatting. The
`wowsdeob.exe` that produced the reports below was built 2026-06-21, BEFORE that fix
landed -- so the bug was a STALE BINARY. Rebuilding `wowsdeob` against current unfuck
resolves all three reported cases; re-running `--final-only` on the live zip now emits:
- `Vehicle.calcServerSpeed`: `self.serverSpeedRaw * 0.5 * self.speedSignDir`
- `Vehicle.calcMaxServerSpeed`: `self.maxServerSpeedRaw * 0.0001 * ConstantsShip.SHIP_TIME_SCALE_INV`
  (the "spurious 0.0" was a real 0.0001 coefficient truncated by the old renderer)
- fovRemapping module: `1.0 - cameraHeightMultiplier * 0.1` and `0.5 * max(..., 0) ** 2`

Regression test: `fractional_float_adjacent_to_zero_in_multiply_renders_exact_value`
in unfuck `tests/ir_m1.rs` (asserts `v * 0.5 * 0.1 * 0.0001`; reproduces the exact
`v * 0.0 * 0.0 * 0.0` corruption under the old renderer).

---

## Issue 1 — float constant in BINARY_MULTIPLY rendered as wrong value (0.5 -> 0.0)

- **Module/function:** `Vehicle.calcServerSpeed`
- **Stage4 bytecode (correct):**
  ```
  LOAD_FAST  self
  LOAD_ATTR  serverSpeedRaw
  LOAD_CONST 1 (0.5)        <-- co_consts = (None, 0.5, 0.0)
  BINARY_MULTIPLY
  LOAD_ATTR  speedSignDir
  BINARY_MULTIPLY
  STORE_ATTR serverSpeed
  ...
  LOAD_CONST 2 (0.0)        <-- this one is the >= comparison operand
  COMPARE_OP >=
  ```
- **Decompiled (wrong):** `self.serverSpeed = self.serverSpeedRaw * 0.0 * self.speedSignDir`
- **Should be:** `self.serverSpeed = self.serverSpeedRaw * 0.5 * self.speedSignDir`
- **Symptom:** the `LOAD_CONST (0.5)` operand was emitted as `0.0`. `co_consts` contains both `0.5` and `0.0`; the decompiler appears to have used the wrong const-pool index (picked `0.0` at index 2 instead of `0.5` at index 1) for the multiply operand, while the later `>= 0.0` comparison rendered correctly.
- **Impact:** makes correct game code look like a multiply-by-zero bug. Constant/const-index resolution in the expression emitter needs checking.

---

## Issue 2 — same `-> 0.0` constant bug (0.001 rendered as 0.0)

- **Module/function:** `mb5c7a3d8.getAimPointFast` (build 12506899; the aim-point helper)
- **Stage4 bytecode (correct):** `co_consts = (docstring, 0.001, 0.0)`
  ```
  LOAD_FAST  unknown_1
  LOAD_CONST 1 (0.001)
  COMPARE_OP < (0)
  POP_JUMP_IF_FALSE ...
  ```
- **Decompiled (wrong, incl. raw `*_stage4_deob.py`):** `if unknown_1 < 0.0:`
- **Should be:** `if unknown_1 < 0.001:` (a near-zero flat-distance guard)
- **Symptom:** identical to Issue 1. `co_consts` index 1 is the real value (`0.001`), index 2 is `0.0`; the `LOAD_CONST 1` operand is emitted with the value of const index 2 (`0.0`).

## Pattern (Issues 1 + 2)
Both functions have `co_consts` where index 1 = a small nonzero float (0.5 / 0.001) and index 2 = `0.0`. In each, a `LOAD_CONST 1` is decompiled as `0.0`. Strongly suggests an **off-by-one or wrong-slot lookup when resolving `LOAD_CONST` operands to values** (emits `co_consts[i+1]` or always grabs the trailing `0.0`), specifically when adjacent float constants are present. Reproduce: decompile any function whose `co_consts` is `(..., <small float>, 0.0)` and check the `LOAD_CONST <idx of small float>` rendering.
