# Machine C H5 odd-coset: source-certified 33- and 37-bit inverse cones

**Mathematical result (27 November 2026).** Two disjointly described classes of actual Machine C stopping targets are absent from the original blank-start section orbit, even though the previously fixed 32-bit cone and Agent25's quarter-phase guard fail to certify either class. The theorems are source-certified, but Machine C and BB(6) remain undecided.

## Original-section stopping equation

Write
```
J(r)   = 2098496 + 2^22*r
M(r,w) = 4876330 + 2^22*r + 2^23*w.
```
For a selected `r,w`, a natural `k` with
`k+J(r)+3*M(r,w)+4 = 2^(2*M(r,w)+2)*(J(r)+2)`
is an exact high-stop candidate. The source theorem is about the actual `BB6.Agent3.CReach`, not a copied model or a finite simulation.

The source-independent signed inverse checker `BB6.Agent42ModularCone.excluded b (stopResidue j m)` is sound at any precision `b ≤ 2*m+1` for these candidates. The first filter caps precision at 32; the present theorems use a larger but still safely available number of bits.

## Wider 33-bit family

Set `R=1024*r`, `W=15+1024*w` for arbitrary natural `r,w`. The new theorem `BB6.Agent34H5Precision.lifted_w15_source` proves that the corresponding high-stop candidate `(2*J(R)+1,k)` is never blank-reachable.

The exact certificate is `excluded 33 (stopResidue (J 0) (M 0 15)) = true`. Under the lift, the signed stop-residue displacement is precisely
```
 Δx =  2^33*r,
 Δy = -2^33*(2*r+3*w),
```
so **every** parameter in the family carries the same 33-bit certificate. At 32 bits the base certificate is false, and the 32-bit filter remains false throughout this family. The Agent25 phase guard also fails identically:
```
(5*R+3*W+4) mod 8 = 1,
(5*R+3*W+17) mod 16 = 14,
(37*R+3*W+t) mod 64 ∈ {7,29,32,37} for t∈{26,48,51,56}.
```
Its parameter-lattice density within the odd H5 family is `2^-20` (one class mod 1024 in each of two parameters). No claim of global nonredundancy relative to *all* other Machine C source filters is made.

## Earlier 37-bit family

For `R=16384*r`, `W=16384*w`, `excluded 37 (stopResidue (J 0) (M 0 0)) = true` and the signed residue displacements are `2^37*r` and `-2^37*(2*r+3*w)`. The certificate is false at 36 and 32 bits, and the Agent25 quarter guard fails throughout this family. The first completed source theorem was `BB6.Agent34H5Precision.lifted_source`. The new 33-bit family is 256 times denser as a parameter lattice coset than this older 37-bit family, though the classes are not represented as an exhaustive partition.

## Proof status and exact reproducibility

- **CI [45930315782](https://github.com/FlareZ123/bb6/actions/runs/45930315782)** (27 November): original-source closure accepted the 37-bit theorem, based on commit `7fa07e164c1b87d8fdaf97d80831a52ad6e1671c`.
- **CI [46078064666](https://github.com/FlareZ123/bb6/actions/runs/46078064666)** (27 November): original-source closure accepted both families, commit `472c6d0d8e99e7002f2eb650dd875585d1f7804a`. The workflow compiled 72 project modules with Lean 4.36.0-rc2. It printed `lifted_w15_source` and `lifted_source` axioms `[propext, Classical.choice, Quot.sound]`; their arithmetic/Boolean certificates have only standard axioms or none. No `sorryAx` or `native_decide` appears in these exported profiles.
- Full proof: [H5Precision.lean](H5Precision.lean). Existing manual target: `.github/workflows/agent13-m16-high-family-interface.yml`, input `sourceH5Precision`. No new workflow required. The code directly consumes `ModularConeHighStop` and the exact original-source parent theorem.

**What remains open:** These congruence subsets do not decide the full H5 odd branch, all Machine C stopping parameters, or BB(6). A complete result would need either to eliminate every remaining authentic inverse-root candidate or produce a real blank-start halting witness. The 33-bit checker has additional accepted residues, but converting a residue census into an all-time stopping criterion requires a checked finite-cover or symbolic-parametric proof; sparse enumeration is not a global conclusion.
