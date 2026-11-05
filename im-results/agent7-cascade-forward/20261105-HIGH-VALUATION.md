# #746 first-reset inverse: valuation gaps through exponent five

Agent 7, 2026-11-05. This note records **intermediate** quantified mathematics. It does not decide halting of the six-state machine or BB(6), and is not presented as independently publishable novelty.

## Reusable near-top theorem

Let `u + A = 4·2^n` for natural `n>=5`, `A>=3`, with the tight inequality `64A+164 <= 13·2^n`. Let `ResetParent h u` denote the **complete genuine first-return reset relation**, as source-proved by Agent 10 in `im-results/agent10-cascade/FirstInverseComplete.lean`. An odd parent with valuation `t` requires an odd integer `d` and scale `k` satisfying

`2u+5=3^(t+1)·d`, `6·2^k+1 <= 2^t·d <= 8·2^k-1`,

plus the exact affine parent-height equation. The even parent's dyadic band also has a unique scale, and the exact parent height is `E(n,A)=4·2^n-2A-n+1`.

Under this near-top bound:

* Odd `t=0` falls in a forbidden band gap between dyadic scales (prior `FirstForkExactTwo.lean`).
* Odd `t=1` has the unique exact parent `O1(n,u)=4*((2u+5)/9)-8·2^(n-2)-(n-2)-5`, whenever `9|(2u+5)`.
* Odd `t=2` falls in a universal dyadic gap (`FirstForkOddT2.lean`).
* Odd `t=3` has the unique exact parent `O3(n,u)=16*((2u+5)/81)-8·2^(n-3)-(n-3)-5`, whenever `81|(2u+5)`.
* Odd `t=4` and `t=5` fall into **two further uniform dyadic gaps** (`FirstForkOddT45.lean`).
* Any further odd `t>=6` forces `2187 | (2u+5)`, since `2187=3^7`.

The single theorem `near_top_odd_only_one_three` in [FirstForkOddValuation.lean](FirstForkOddValuation.lean) composes all four forbidden valuation cases and proves that when `(2u+5)%2187 != 0`, every odd first-reset parent has `t=1` or `t=3`. The proof uses only `[propext,Quot.sound]` in the local Lean check, no source stub axioms.

[FirstForkExactThree.lean](FirstForkExactThree.lean) then proves a **complete three-parent iff**, not merely existence:

`ResetParent q u ↔ q=O3(n,u) ∨ q=O1(n,u) ∨ q=E(n,A)`,

whenever `81|(2u+5)` and `2187∤(2u+5)`. All three parents are pairwise distinct by [FirstForkThree.lean](FirstForkThree.lean). [FirstForkRootThree.lean](FirstForkRootThree.lean) transfers the full classification to an exact **genuine blank-root reachability iff** for every such `u≠2`, using the previously source-proved rooted first-reset chain theorem.

These symbolic results build upon the complementary mod54 and mod162 first-fork families documented in [EXACT-FORK-20261105.md](EXACT-FORK-20261105.md). In particular, for the exceptional fatal n%162 in `{5,130}`, or second-ancestor n%162 in `{83,124}`, an odd t=3 branch always exists. The exact three-parent theorem applies to those members additionally satisfying nondivisibility by 2187. Larger 3-adic valuation may admit further branches; no finite universal parent-count claim is made for them.

## Source status and limitations

All new Lean modules were checked locally with Lean **4.36.0-rc2**, ordinary kernel computation, no `sorry` or `native_decide`, against a **source-shaped minimal stub** which axiomatizes previously independently proved source lemmas (`root_reset_chain_iff`, `reset_chain_last`, `even_band_scale_unique`, `n_plus_three_le_pow` and friends). The local axiom audit of the new dyadic-gap and valuation-restriction theorems contains only standard foundational axioms, but source-dependent results show these stub interface axioms by design. Thus do not call the entire new chain source-verified or physical-Turing-machine-verified without an unchanged checked-in-source compilation.

The existing manual workflow `.github/workflows/agent7-746-uniform-fatal-parent.yml` compiled the first six new modules in the initial one-shot issue-triggered run [41966512900](https://github.com/FlareZ123/bb6/actions/runs/41966512900), if that run eventually succeeds. **At writing, the run is queued; no success is claimed.** It is pinned at an earlier commit and does **not** cover the later `FirstForkT3`, `FirstForkThree`, `FirstForkOddT45`, `FirstForkOddValuation`, `FirstForkExactThree`, or `FirstForkRootThree` additions. A subsequent manual source-check of those files is needed.

Most valuable next research is an invariant distinguishing the genuine blank-derived reset root from every member of the remaining infinite fatal family. Exact local parent grammar alone is an intermediate algebraic reduction.


## Direct exact-inverse numerical cross-check

An independent integer-arithmetic enumeration of all dyadic even and odd inverse bands at each finite target (not a Lean theorem) confirms that the nondivisibility-by-2187 condition is meaningful. The exceptional second-predecessor index `n=83` has **four** distinct candidate source reset parents (one even, odd valuation exponents `t=1,3,6`). The exceptional immediate fatal index `n=491` likewise has four candidates with odd valuations `1,3,6`. By contrast `n=124` at the exceptional second target and `n=130` at the exceptional immediate fatal target each have three (even plus odd `1,3`). This finite numerical evidence guards against the incorrect unconditional claim of exactly three parents in every exceptional residue class. The abstract `near_top_exact_three` theorem correctly requires `(2u+5)%2187 != 0`.

Two additional locally checked specializations are in [FirstForkFatalThree.lean](FirstForkFatalThree.lean): complete true blank-reset-root iff statements for fatal n%162 in `{5,130}` and for second-ancestor fatal n%162 in `{83,124}`, both conditional on nondivisibility by2187. These also remain pending untouched-source CI.


A second independent finite integer check over the first 118 surviving fatal candidate indices `2049<=n<=2399, n%6∈{4,5}` found 78 targets with no odd first-return parent, 35 with only `t=1`, and five with both `t=1,3`; every target also has its unique even first-return parent. This concerns only **immediate synthetic reset parents** and cannot establish whether the blank-root orbit reaches any target. The fixed interval sample is computational evidence, with no all-index extrapolation.
