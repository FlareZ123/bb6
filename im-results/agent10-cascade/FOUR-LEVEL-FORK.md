# Four forced #746 inverse reset levels, followed by a genuine fork

**Agent 10, 2026-11-05.** This is an intermediate holdout-specific result. The exact Busy Beaver value and the original #746 halting verdict remain open.

## Source and existing proof

The original six-state machine is `1RB0LF_1LC1RA_0RE0RD_---1LE_1LF1RC_1LC1LA`. Agent 10's exact `CascadeResetInverse.ResetParent` is a complete first-reset inverse relation, proven equivalent to source-indexed `CascadeSource.Cstep`. The genuine blank root in this acceleration is `C(2,0)`. Agent 7's `SecondEven.lean` already source-proved two forced even inverse levels for `n%18∈{10,11,16,17}`, using `ResetChain` and the genuine-root bridge; see [Agent 7's dossier](../agent7-cascade-forward/README.md) and source CI 41900314347 for its preceding one-level theorem.

## Candidate new universal result

For every `n≥10` with `n%18=10` or `n%18=17`, write `P=2^n` and define five exact reset heights:

| height | formula |
|---|---|
| `u0` | `4P-n-4` (fatal reset) |
| `u1` | `4P-3n-7` |
| `u2` | `4P-7n-13` |
| `u3` | `4P-15n-25` |
| `u4` | `4P-31n-49` |

The two new source-level statements in [FourEven.lean](FourEven.lean) assert:

1. Each `u_j` for `j=0,1,2,3` has exactly one `ResetParent`, namely `u_(j+1)` (the first two levels reuse Agent 7's proven interface).
2. Consequently `ReachC (2,0) (u0,0) ↔ ReachC (2,0) (u4,0)` for every such index, without a finite-index cutoff.

The key reusable lemma `any_parent_near_top` says: if `3*2^n≤u≤4*2^n`, `n≥4`, `(2u+5)%9≠0`, and there is a valid even-band parent at dyadic scale `k`, then it is the **unique** first-reset parent. For the odd inverse branch, valuation `t≥1` requires `9∣(2u+5)`, while valuation `t=0` would place its dyadic input strictly in the forbidden gap `(2*2^n,3*2^n)`. In the two stated index classes, direct modular calculation excludes divisibility by 9 at `u2` and `u3`. Agent 7's earlier proofs handle `u0,u1`.

## The obstruction is sharp

[FourthBranch.lean](FourthBranch.lean) constructs **two different genuine exact first-reset parents of `u4`** for all the same indices:

- The even parent `u5=4P-63n-97`.
- The odd parent `v=(14P-257n-399)/9`, equivalently `4*((2u4+5)/9)-8*2^(n-2)-(n-2)-5`.

Here `9∣(2u4+5)` in both classes. The odd witness has `k=n-2, t=1, d=(2u4+5)/9`, satisfying the **full** inverse grammar's dyadic band, parity and output equations. The even witness has `k=n-1`. The proof separates their heights by `v<2P<3P≤u5`. This explicit fork prevents a claimed fifth uniquely forced even inverse return in these classes.

## Validation and precise limits

The complete Lean files `FourEven.lean` and `FourthBranch.lean` have been compiled locally with **Lean 4.36.0-rc2**, with no `sorry` or `native_decide`, against a lightweight local `SecondEven` signature stub. Its `ResetParent` was copied verbatim from the repository's `FirstInverseComplete.lean`. The local kernel audits show no `sorryAx`; the final root theorem necessarily references the stubbed prior bridge, parent-scale uniqueness and second-even theorem. A local interface match **does not authenticate an unchanged-source theorem**. The checked-in [manual source workflow](../../.github/workflows/agent7-746-uniform-fatal-parent.yml) has been extended to compile the real `SecondEven.olean`, `FourEven.olean`, and `FourthBranch.lean` in that order. **A successful manual workflow run is still required** before reporting these two new files as verified against the unchanged repository source.

Local source SHA256 values:
- `FourEven.lean`: `d7bafa72dca46b580c0ae8e0a0a3e6502470b7012dd1e101b1e5646056c5ce97`
- `FourthBranch.lean`: `e0589f55b7deed68b8276743d2a42aea51f6aeb217a37d94e8ddcc1dee8e0776`

The exact-content GitHub files were entered through the repository connector; their hash should be compared to these local values before regarding the local check as a source-file reproduction.

**Why it matters:** This refines an infinite family of the *genuine* #746 reset-root problem and identifies the earliest provably necessary branching node of two surviving arithmetic sectors. It is a structural simplification, not an all-index obstruction. Existing finite forward proof excludes all fatal indices up to 2048, so no new finite halting exclusions or BB(6) upper bound follow. External academic novelty remains unassessed. The next consequential mathematical task is to constrain the two authentic `u4` parent branches uniformly in the blank-root inverse graph; further forced-even lifting cannot alone finish these sectors.


## Further refinement: complete two-branch grammar in four modulo-54 classes

The new [FourthExactTwo.lean](FourthExactTwo.lean) locally proves two stronger uniform statements for every (n\ge10) with (n\bmod54\in\{17,28,35,46\}):

1. `fourth_not_div27`: (27\nmid(2u_4+5)), via the exact multiplicative period 18 of (2^n\pmod{27}). The older result already gives divisibility by 9, so the 3-adic valuation is exactly 2.
2. `fourth_parents_exactly_two`: for **every** (q\in\mathbb N), `ResetParent q u4 ↔ q=oddPre n ∨ q=evenPre n`. Completeness uses the full two-arm source inverse. Even-band exponent uniqueness forces (k=n-1). Odd (t=0) is excluded by the dyadic gap; (t\ge2) would imply divisibility by 27; (t=1) forces the unique dyadic scale (k=n-2), quotient and parent height.

The derived `genuine_fatal_iff_two_parent_roots` composes this with the actual-root source `ResetChain` bridge: **genuine blank-derived reachability** of fatal(n) is equivalent to reachability of at least one of the two explicit parent heights. This is a complete iff of the two-branch interface, still conditional on unchanged-source checking.

The new file compiled locally under Lean 4.36.0-rc2 with the same explicitly stubbed prior source interface. The modulo27 arithmetic theorem's kernel axiom list is only `[propext, Quot.sound]`. The final exact-parent iff also lists `even_band_scale_unique`, which is a stub of Agent 7's existing proved theorem, plus standard Lean axioms. The final rooted iff additionally lists stubbed `root_reset_chain_iff`, `genuine_fatal_iff_second_even` and `reset_chain_last`. **These stub dependency names explicitly prevent describing the local run as complete unmodified-source verification.** Updated existing manual-only workflow now compiles the actual full source chain and all three new files; source check remains to be run.

Local newest source sha256: `FourthExactTwo.lean` `6b38661bc5abbbbda1c1b2af918b03446761b0f089bcb2b4e6c2571285fb0d58` before appending its rooted theorem; this digest is historical and should be recalculated for the final local proof. 
