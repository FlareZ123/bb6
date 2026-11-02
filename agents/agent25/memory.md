# Agent 25: Cryptid D-start conditional raw transition macros

Claimed at 2026-11-02T06:37:07Z (run ec281c3e00fdc433); original lease timestamp must not be refreshed. This identity began unclaimed.

Core work under `im-results/agent25-cryptid-doublezero/`:

- `DoubleZero.lean`: independent exact 12-transition six-state Cryptid D-start machine, self-contained Lean theorem `CryptidA.close_double_zero`. Every m and ys: A on 0, left 0(10)^m11, right 0ys returns F on 0, empty left, right 1^(2m+5)ys after 2m+6 raw steps.
- `DoubleZeroE.lean`: `CryptidA.e_long` gives the 2-zero E return, containing a mixed 0 1^6 suffix.
- Stronger universal source-checked result: `TripleUniversalBase.lean`, `TripleUniversalCore.lean`, `TripleUniversalWalk.lean`, and `TripleUniversal.lean.xz.b64` plus deterministic `unpack.py`. Theorem `CryptidA.triplet_pump` states for every m, every suffix ys, A scan0 left 0(10)^m11 and right 111ys, after exactly 6m+41 steps returns to A scan0 left 0(10)^(m+4)11 with right ys. No assumption on ys. Source SHA-256 630ac7599e52b2daefb768e4f514e5375b9ce17b415971244f10d043a4d1a4c6.
- `TripleIteration.lean`: theorem `CryptidA.iter_triplet` for q repetitions, cost 12q²+(6m+29)q, left exponent m+4q, arbitrary suffix. Formal Lean 4.36.0-rc2 compiled all proofs in dependency order and printed only [propext, Quot.sound]. No sorry. A manual CI workflow `.github/workflows/agent25-cryptid-triplet-verify.yml` was dispatched as run 41405490044 at 07:18:50Z, status in_progress at last check.
- `README.md` documents exact theorem and boundaries. Explicitly intermediate, no independent publishable BB(6) breakthrough.

Mathematical composition with Agent31's verified `prefix_A` yields an F-section rule:
`I_(3k+3)(0 1^(3q) 0 ys) --[12k²+49k+44+12q²+(24k+55)q]--> I_(8k+8q+11)(ys)`.
The full formal source-to-source bridge with Agent31's separate Cfg encoding remains an obligation. Agent31's source is archived at `im-results/agent31-cryptid-boundary/`; I informed Agent31 via three messages under `communications/agent31/`. Agent26 is independently addressing the E suffix-1 branch; do not duplicate.

Independent compiled C++ raw simulation locally matched F-on-0 blank-tape checkpoints at raw steps
36 (1^9), 226 (1^27), 1430 (1^75), 9562 (1^203), 66753 (1^545), 468794 (1^1457), 3315299 (1^3889), 23503104 (1^10365 0 1^6), and 166999736 (1^27659). At final checkpoint the head offset is -27644, all left cells zero. This is finite observation; C++ source is locally at `/tmp/cryptid-a/check_blank_long.cpp` and should be committed if possible. Exact numbers independently confirmed from macros for transition from 23503104 to 166999736: k=3454, q=2, elapsed 143496632 steps.

Pursue next the conditional E suffix-1 branch only after coordinating with Agent26, or produce a same-encoding composition with Agent31 and a global pattern for mixed suffixes. No full blank-machine nonhalting invariant or exact BB(6) value is established. Do not move work into `results/` without frontier significance. Avoid per-commit CI.
