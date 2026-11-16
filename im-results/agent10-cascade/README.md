# Cryptids #746: exact reset inverse grammar and infinite fatal-gate problem

**Research state (16 November 2026): the original-source inverse grammar and fixed-target nonreachability theorems remain the strongest root-facing results. A new adjacent-even fatality reduction limits its odd-reset valuation to t=0 or t=1, with exact root-source odd-part tests for both cases and no matches in the 100,000-transition prefix. The new Lean source theorem and the t=1 source-connected bridge are on PR #106 pending local compile; the genuine blank-start halt/nonhalt question remains open.** All closed forms, certificates, experiments and earlier verification entries are retained in [FULL_RESEARCH_LOG.md](FULL_RESEARCH_LOG.md).

## 16 November 2026: adjacent-even fatal valuation cutoff and root odd-part tests

The [adjacent-even fatal odd-part reduction](ADJACENT-EVEN-FATAL-ODDPART.md) derives the exact all-t fatal equation and proves that the odd-reset valuation must satisfy t≤1 whenever the child is at level K+1, undergoes same-level even resets, and exits to F_(K+2). The remaining t=0 and t=1 cases reduce to the two exact source-height equations B0=(2K+7)·2^(r+3) and B1=(2K+7)·2^(r+5), respectively, with r odd. The t=0 source-band interval has multiplicative width below 2, so each K admits at most one t=0 fatal depth and source-height candidate. The t=1 equation is the Q-depth bridge already developed in the preceding work; t=0 is the newly explicit companion branch.

The extended [root forward audit](root_forward_3adic.py) now checks both odd-part equations at every actual t=0 or t=1 source transition. In a deterministic 100,000-transition BigInt reproduction, neither equation matched the blank-root prefix. This is finite evidence only. Direct odd-output fatality remains a separate all-t branch, and neither surviving adjacent-even case has been excluded for all root times. The Lean proof of the t≤1 cutoff and the t=1 source bridge are still awaiting local preflight on PR #106.

## 14-16 November 2026: 100,000-step blank-root forward orbit and 3-adic coverage

The reproducible [root forward audit](root_forward_3adic.py) ran 100,000 exact reset transitions from height 2 in [CI 43638425432](https://github.com/FlareZ123/bb6/actions/runs/43638425432). It reached level K=77,220 (height bit length 77,223) without halting. The 49,717 level-entry heights cover every residue congruent to 2 modulo 3 modulo 3^7, and 2,186/2,187 such residues modulo 3^8. The prefix also contains same-index fatal congruence matches at every precision 3^a for 2≤a≤8, so fixed-modulus height-versus-fatal residue exclusions through 3^7 do not separate this root prefix.

The [full report](ROOT-3ADIC-COVERAGE-100K.md) includes the exact recurrence, coverage table, terminal-residual statistics, and a counterexample showing that the observed all-odd-exit tail is not implied by the simple condition D_K odd and D_K>4K+10. These are finite computational observations, not a proof of infinite 3-adic density or nonhalting.

## 12 November 2026: dual index/depth and nested-parent Hensel selectors (CI pending)

The [index/depth Hensel analysis](RAY-INDEX-DEPTH-HENSEL.md) complements the existing depth-coordinate selector. For every even canonical-ray depth j and sector s=4 or 5, exactly one fatal-index class h modulo 3^k makes Z_j(s+6h) divisible by 3^(k+1). Theorems depth_index_duality and indexResidue_bijective show that the depth and index selectors are inverse coordinates and form a finite bijection in each precision block.

The same Lean module now handles nested odd parents at every even depth. With W_(j,t)(n)=2^(t+1)*Z_j(n)+5*3^(t+1), it proves a unique next ternary lift and the full recursively named selector nestedOddIndexResidue, with nestedOddIndexResidue_iff giving the exact residue class modulo 3^k at every precision.

For the t=3 high-q gate, the local next index-shift digit from the actual index n is e modulo 3, where e=W_(j,3)(n)/3^8. The source equation for the second t=3 parent's target index R gives R=e+1 modulo 3. Thus the excluded R=0 case is local digit 2, while the remaining R=1,2 cases are local digits 0,1. This local shift digit is distinct from the canonical digit used recursively in nestedOddIndexResidue. See tThreeHighGate_digit_eq_quotient_mod_three and tThreeSecondParent_index_relation.

Lean source: RayIndexHensel.lean. The existing manual Agent 10 ray/odd-strip workflow now includes this module after RayDepthHensel and RayDepthResidue. No successful CI result exists for this revision yet. These are arithmetic selector results, not proofs of the dyadic source band, blank-root reachability, or nonreachability of the even fatal predecessor. They remain in im-results pending source CI and adversarial review.

## 9 November 2026: uniform odd-entry fatal-depth sieve

New [source-level modular fatal-depth research](SWEEP-ODD-FATAL-DEPTH.md) proves, for an odd first-return entry to level k followed by m same-level returns and an adjacent even exit to a fatal target, that m is odd and the level itself must satisfy k%6∈{3,4}. If entry≥6·2^k, an exact mod-9 gate forces a unique m%6 class for each eligible k%18. For two distinct source histories with the same fatal level, every nonmaximal depth automatically lies in that high-entry range; **at most one maximal depth is exempt**.

[Four linked Lean modules](SWEEP-ODD-FATAL-DEPTH.md#proof-and-ci-status) were confirmed by [full original-source Lean CI 42580632479](https://github.com/FlareZ123/bb6/actions/runs/42580632479). The subsequently strengthened sector-free corollary also passed [full-source CI 42581502772](https://github.com/FlareZ123/bb6/actions/runs/42581502772). The restrictions apply to synthetic source histories and are not a blank-root nonhalting proof. See the full dossier for the strict hypotheses, complete mod-18 table, arithmetic proof and concrete low-entry exception.

## Source-verified results

The first-reset inverse equations provide a complete original section parent grammar. [ReachDecide.lean](ReachDecide.lean) proves a correct terminating genuine-root reachability Boolean for **each fixed target**. [Manual source CI 41887144371](https://github.com/FlareZ123/bb6/actions/runs/41887144371) succeeded.

The stronger original raw-machine bridge, [OriginalGate268.lean](OriginalGate268.lean), **passed upstream original-source CI 41893704612**. Halting reduces to the existence of an authentic blank-reset-root path to some fatal target with `n≥268` and `n%6∈{4,5}`. This is a still-infinite condition. The earlier `n≥257` threshold is an older, weaker criterion.

[Source-generated reverse-cone certificates](../../.github/workflows/agent10-746-exit-source.yml) passed [CI 41892190566](https://github.com/FlareZ123/bb6/actions/runs/41892190566) for `n=257,262,263`. Those proofs exclude each particular fatal target at **all** source times. Other sampled reverse cones through index 2048 are numerical investigations unless separately kernel-certified.

## Remaining question

Prove that **every** fatal target in the surviving infinite sectors is inaccessible from the genuine blank root, or construct a true reaching path. The exact parent grammar permits synthetic ancestors and deep odd-parent chains. Fixed-target termination and arbitrarily large finite cutoffs do not establish a machine-wide decision.

Consult the [full research log](FULL_RESEARCH_LOG.md) for exact formulas, exceptional cases, generated Lean certificates, tree sizes, and historical status text. Old “pending upstream CI” assertions there are superseded by the successful run cited above.
