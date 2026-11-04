# Machine C four-stage forced predecessor pilot (Agent 1, 2026-11-04)

**Status (corrected after prior-art audit):** This entire four-step stopping family is **already source-certified by Agent 3's `high_halt_affine_oeo_512_unreachable`** in [`HighAffineOddEvenOddHalt.lean`](../agent3-c-bounce-inverse/HighAffineOddEvenOddHalt.lean). It assumes `m≥4`, `m%4=0`, `(j+511*m)%512=279` and the identical halting equation, and therefore **strictly subsumes** the current parameters `m=4t+8`, `j=m+279+512q`. The arithmetic proof below independently compiles locally but contributes **no new excluded gate**. The proposed redundant original-source CI [41870197075](https://github.com/FlareZ123/bb6/actions/runs/41870197075) was cancelled immediately after detecting the subsumption; do not rerun merely for this duplication. This is archival/reproducibility material only.

## Duplicated excluded halting family (historical local reconstruction)

For any `t,q : Nat`, set `m=4*t+8` and `j=4*t+287+512*q`. For the unique natural `k` specified by the high-halting gate

```
k+j+3*m+5=2^(2*m+2)*(j+3),
```

the candidate source theorem is

```
∀ time : Nat, run secNext time (some (5,1)) ≠ some (2*j+3,k).
```

These are **actual source halting-input configurations** already excluded by the more general original-source theorem of Agent 3, and are not actual blank-orbit halting witnesses. Each such input satisfies four complete predecessor guards in succession: even-right affine, odd/odd low 2-adic valuation, even/odd seven-sector, odd/odd low valuation. The unique forced ancestor after four steps has odd second coordinate at least five and coordinate sum congruent to one modulo four. The original Agent 3 odd-image theorem forbids this ancestor for all positive-time true-blank returns; it differs from the initial (5,1).

The residue pattern is `m≡0 (mod4), j-m≡279 (mod512)`. It is already covered by Agent 3's four-stage [`affine_odd_even_odd_cone_unreachable`](../agent3-c-bounce-inverse/AffineOddEvenOddCone.lean) and high-halt theorem. It is distinct in its prescribed parameter class from Agent 3's [three-stage high family](../agent3-c-bounce-inverse/HighAffineInfinite.md), `m≡2 (mod4), j-m≡87 (mod128)`. The complete overlap is established by direct comparison with the previously published exact Lean theorem. Any independent-source test of this bundle should be identified strictly as replication.

## Reproduction and scope

The SHA256-pinned [compressed source bundle](C4SourceBundle.tar.gz.b64) holds `C4Arithmetic.lean` and `C4Source.lean`, gzip-compressed tar encoded as base64. Decode the base64, verify tar SHA256 `95f1e51b2d38a2dc496e905d2119e72b769c730c479542ac3d18e40c0af25ecc`, and extract. Uncompressed source SHA256 values respectively `632d1c0c932702e6fe3cb9bf2b27c42cfeca7d2f59e75d6fddccd7b949c4b9ac` and `f5756b74979b605897d5fd045051d12e870852661eb41f45b27f8e864043aced`.

`C4Arithmetic.lean` compiled locally with pinned Lean 4.36.0-rc2 and ordinary axioms only. `C4Source.lean` requires unchanged original `Agent46.secNext`, the source-certified reachability inverses in `OddForcedNormalize.lean`, `OddSevenOrbit.lean`, `ReachAffine.lean`, and the source-certified `blank_section_odd_image`. The final genuine blank-reachability assertion is already **source-certified through Agent 3's stronger theorem**; this independently written C4Source proof itself remains locally uncompiled against the untouched source, and no need exists to spend CI on it.

Even when source-certified, excluding this parameter family does not settle either full Machine C halting locus, all BB(6) holdouts, or a BB(6) upper bound. The next scientific question is whether an infinite lossless fourth-stage inverse grammar can cover remaining joint stopping gates without merely enumerating residue cylinders.

## Correction record

The duplication was recognized by reading the actual file `im-results/agent3-c-bounce-inverse/HighAffineOddEvenOddHalt.lean`, not merely comparing board summaries. The exact parameter relation is `j−m=279+512q`, and `(j+511m)%512=279` follows. Source duplication was caught before promoting any new mathematical novelty or running the full job. The original source bundle is retained to make the negative search auditable.
