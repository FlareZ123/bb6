# Agent 31: Cryptid D-start symbolic research continuity

**Original lease:** `agents/agent31/.lease.json`, claimed `2026-11-02T05:48:00Z`, run_id `agent31-bb6-20261102T054800Z-v6`. Do not refresh. At each persistence checkpoint compare real UTC clock. If at least 70 minutes elapsed (06:58 UTC on this run), finish minimal cleanup, commit/push all work, then delete lease as final mutation.

## Main contribution, 2026-11-02

Target open six-state D-start cryptid `1RB0RE_1LC0RA_1LA1LD_1LC1LF_0LC0LB_1LE---`. Agent 2 had an unrelated synthetic halting family. I built a fully explicit raw-machine Lean 4.36.0-rc2 symbolic proof under `im-results/agent31-cryptid-boundary/`. Base source is xz+base64 encoded, `Boundary.lean.xz.b64`; `unpack.py` verifies SHA-256 and reconstructs atomically. **Current source hash** `0d9f160644d919adf7239b49857fa6cd62ee6cdecadfe0a75ec312a612194883`, Git blob `0e5a4e9799c9491b5e7c4a9c88c5a05b257ff3a5` (manual source artifact exact); README documents semantics. Current source was compiled locally with no errors and `#print axioms full_B` = `[propext, Quot.sound]`, no `sorryAx`.

Major exact raw-step theorems:
- For every `m` and tape suffix `ys`, `pump_generic : run (6m+27) (midM m ([1,1,1]++ys)) = midM (m+4) ys`.
- Three arbitrary-suffix initial first-zero-delimiter prefix formulas for `n≡2,0,1 mod3` with exact times `12k²+41k+(31,32,33)`.
- `full_B`: for all `k,ys`, `I_(3k+2)(0ys) -> I_(8k+9)(ys)` in exactly `12k²+49k+40` steps, whole F-return. This is a universal primitive-step identity, not just a finite scan.
- Actual blank bridge `blank36`: `run 36 blank = I_9(empty)` (pure kernel `by decide` with *no axioms*). `blank198` is exact raw configuration on genuine blank orbit after 198 steps. 
- `BoundaryExtra.lean` contains the further locally-verified appended-module `full_A_00`: `I_(3k+3)(00ys) -> I_(8k+11)(ys)` in `12k²+49k+44` steps, plus `full_A_nil` and `full_B_nil` for exact blank-right suffix. Those formulas compiled in the same Lean source before a local container reset, but a separate import-based compile is **pending CI**, do not claim imported module passed until run success.

A manual-only workflow `.github/workflows/agent31-cryptid-lean.yml` was dispatched at 06:38:57 UTC, [run 41401237796](https://github.com/FlareZ123/bb6/actions/runs/41401237796), exact commit `7ff8e8e05e5627cbc8ee85176f361e2c10361c19`. It restores source using checksum, compiles `Boundary.olean`, then imports it into `BoundaryExtra.lean`, checking all axioms. Inspect job logs if failed and fix.

Sent detailed specialist message to `communications/agent2/2026-11-02T0638Z_agent31-cryptid-macro-and-blank-bridge.md`. Updated README under intermediate results. No exact BB(6), no decided holdout, and no publishable new bound. The machine is presumed extremely hard, so maintain proper scope.

## Empirical conjecture, explicitly unproved

Raw Python simulator checked 229,376 pairs of macro(n,suffix) versus macro(n+3,suffix) for n=5..11 and all canonical suffixes up to 16 bits (plus empties), 0 discrepancies for predicted output unary length +8 and identical suffix when both return, and joint halting when both halt. A random much longer-suffix scan also suggested this, but no universal proof. Agent 2 found counterexamples to a superficially related unrestricted `n+3^k` branch heuristic for n=4, suffix `011`. Do not promote any finite scan to proof or assume our conjecture holds on all tapes.

## Next high-value work

1. Check current manual CI run for imported `BoundaryExtra.lean`; ensure no unbound imports, fix and re-run if needed. Pin source SHA, runtime version, job log.
2. Compose `blank36`, `full_A_nil 2`, `full_A_nil 8`, `full_A_nil 24`, `full_B_nil 67` into a kernel-checked blank-orbit macro trace: F-state unary lengths 9 at step36, 27 at step226, 75 at1430, 203 at9562, and 545 at66753 (time arithmetic independently checked). This is finite evidence only.
3. Prove a complete 1 mod3 return branch in the presence of suffix, potentially as a transducer. Check whether the two existing full branches help prove a qualified `n+3` single-macro conjugacy. Focus on a forward *actual blank orbit* invariant rather than synthetic tape families.
4. Check literature novelty, particularly @-d's first-delimiter formulas on wiki, before promoting anything to `results/`.
5. Keep src and recovery in `im-results/` until a publishable frontier result, rather than filling `results/` with finite evidence.

Local environment caveat: the uploaded two-part Lean ZIP contains a second `.tar.zst` layer. Need concatenate, unzip, then `tar --zstd -xf` inner payload. Local container reset occurred at ~06:34 UTC, wiping all `/tmp` artifacts; the committed base source is safely recoverable from the repo using `unpack.py`.
