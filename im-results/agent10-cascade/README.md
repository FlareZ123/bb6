# Cryptids #746: exact reset inverse grammar and infinite fatal-gate problem

**Research state (12 November 2026): original-source inverse and fixed-target nonreachability theorems remain the strongest root-facing results; a dual index/depth 3-adic selector is now drafted, but its new Lean source check is pending. The genuine blank-start halt/nonhalt question remains open.** All closed forms, certificates, experiments and earlier verification entries are retained in [FULL_RESEARCH_LOG.md](FULL_RESEARCH_LOG.md).

## 12 November 2026: dual index/depth and nested-parent Hensel selectors (CI pending)

The [index/depth Hensel analysis](RAY-INDEX-DEPTH-HENSEL.md) complements the existing depth-coordinate selector. For every even canonical-ray depth j and sector s=4 or 5, exactly one fatal-index class h modulo 3^k makes Z_j(s+6h) divisible by 3^(k+1). Theorems depth_index_duality and indexResidue_bijective show that the depth and index selectors are inverse coordinates and form a finite bijection in each precision block.

The same Lean module now handles nested odd parents at every even depth. With W_(j,t)(n)=2^(t+1)*Z_j(n)+5*3^(t+1), it proves a unique next ternary lift and the full recursively named selector nestedOddIndexResidue, with nestedOddIndexResidue_iff giving the exact residue class modulo 3^k at every precision.

For the t=3 high-q gate, the next index digit is e modulo 3, where e=W_(j,3)(n)/3^8. The source equation for the second t=3 parent's target index gives r=e+1 modulo 3. Thus the excluded r=0 case is digit 2, while the remaining r=1,2 cases are digits 0,1. See the bridge theorems tThreeHighGate_digit_eq_quotient_mod_three and tThreeSecondParent_index_relation.

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
