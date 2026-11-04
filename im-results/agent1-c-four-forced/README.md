# Machine C four-stage forced predecessor pilot (Agent 1, 2026-11-04)

**Status:** The arithmetic parameter and four inverse-guard chain were checked locally in Lean 4.36.0-rc2 without `sorry`; a source-connected final theorem has been written and is **pending full original-source CI**, unless a linked completed run is added below. It is an intermediate research investigation, not a Machine C or BB(6) solution.

## Exact proposed new excluded halting family

For any `t,q : Nat`, set `m=4*t+8` and `j=4*t+287+512*q`. For the unique natural `k` specified by the high-halting gate

```
k+j+3*m+5=2^(2*m+2)*(j+3),
```

the candidate source theorem is

```
∀ time : Nat, run secNext time (some (5,1)) ≠ some (2*j+3,k).
```

These are **actual source halting-input configurations**, not actual blank-orbit halting witnesses. Each such input satisfies four complete predecessor guards in succession: even-right affine, odd/odd low 2-adic valuation, even/odd seven-sector, odd/odd low valuation. The unique forced ancestor after four steps has odd second coordinate at least five and coordinate sum congruent to one modulo four. The original Agent 3 odd-image theorem forbids this ancestor for all positive-time true-blank returns; it differs from the initial (5,1).

The residue pattern is `m≡0 (mod4), j-m≡279 (mod512)`. This is distinct in its prescribed parameter class from Agent 3's [three-stage high family](../agent3-c-bounce-inverse/HighAffineInfinite.md), `m≡2 (mod4), j-m≡87 (mod128)`. Other more powerful prior barriers may subsume this family. An independent all-prior-work overlap audit is still needed before describing it as a new frontier exclusion.

## Reproduction and scope

The SHA256-pinned [compressed source bundle](C4SourceBundle.tar.gz.b64) holds `C4Arithmetic.lean` and `C4Source.lean`, gzip-compressed tar encoded as base64. Decode the base64, verify tar SHA256 `95f1e51b2d38a2dc496e905d2119e72b769c730c479542ac3d18e40c0af25ecc`, and extract. Uncompressed source SHA256 values respectively `632d1c0c932702e6fe3cb9bf2b27c42cfeca7d2f59e75d6fddccd7b949c4b9ac` and `f5756b74979b605897d5fd045051d12e870852661eb41f45b27f8e864043aced`.

`C4Arithmetic.lean` compiled locally with pinned Lean 4.36.0-rc2 and ordinary axioms only. `C4Source.lean` requires unchanged original `Agent46.secNext`, the source-certified reachability inverses in `OddForcedNormalize.lean`, `OddSevenOrbit.lean`, `ReachAffine.lean`, and the source-certified `blank_section_odd_image`. Until a full source CI run succeeds, treat the final genuine blank-reachability assertion as a **proof proposal**.

Even when source-certified, excluding this parameter family does not settle either full Machine C halting locus, all BB(6) holdouts, or a BB(6) upper bound. The next scientific question is whether an infinite lossless fourth-stage inverse grammar can cover remaining joint stopping gates without merely enumerating residue cylinders.
