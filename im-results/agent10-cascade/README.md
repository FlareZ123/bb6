# Cryptids #746: exact reset inverse grammar and infinite fatal-gate problem

**Research state (16 November 2026):** the 100,000-transition blank-root audit remains finite evidence, and the source-level deficit map gives the exact even/odd level-exit criterion and mixed valuation identity (t=v_2(A)), (2h'+5=3^{t+1}d) at odd exits. Fatality has two distinct final-reset branches: a direct odd output, (3^{t+1}d=G(n)=8\cdot2^n-2n-3), or an adjacent even exit after m same-level resets, (D_k(e)=2^m(4k+10)). The latter and its all-natural parity/sector/mod-9 restrictions are already source-formalized in [SWEEP-ODD-FATAL-DEPTH.md](SWEEP-ODD-FATAL-DEPTH.md); consecutive even level exits are excluded only in the stated high-level range (k\ge7). A new Lean 4.36.0-rc2 core proof shows that the exact t=1 Q-parent equation itself forces K mod 6 in {2,3} and j even, hence fatal index K+2 lies in the original sectors 4/5; the raw-machine bridge no longer needs a separate sector premise. The full source-module compile and root-specific blank-start intersection remain open. All closed forms, certificates, experiments and earlier verification entries are retained in [FULL_RESEARCH_LOG.md](FULL_RESEARCH_LOG.md).

## 16 November 2026: t=1 Q-parent to fatal chain (Lean draft; compile pending)

For a genuine odd source exit at level K with t=1, write c=2K+7, oddOffset=2a, oddParameter=2d, so a+d=2^(K+2). The exact Q-parent equation
`9a+c-2^(K+2)=c*2^(j+1)`
forces the child deficit at level K+1 to be `D=c*2^j`. Crucially, the source offset bound `a≤2^K-1` also gives
`c*2^(j+1)≤5*2^K+c-9`,
hence `D < 8*2^K+c-1 = D_{K+1}(F_{K+1})`. This strict inequality excludes a premature fatal state at level K+1; first-failure level alone would not suffice. The same bound also forces j<K, a quantitative cap that can be combined with the 3-adic depth selector. For j=0 the child is F_(K+2); for j>=1 the child is nonfatal at K+1 and exactly j even first-reset edges halve the deficit before the last edge reaches F_(K+2).

The draft formalization is [T1QParentFatal.lean](T1QParentFatal.lean), with the conditional raw-machine lift in [T1QParentOriginal.lean](T1QParentOriginal.lean). The latter says that any authentic root t=1 Q-parent match with fatal index n>=257 in a fatal sector implies `IsHalt target` for the unmodified machine. It does **not** assert that such a match exists or prove the all-time nonintersection. Compilation is pending; see dependent draft [PR #106](https://github.com/FlareZ123/bb6/pull/106), based on Agent 44's LevelDeficitDynamics branch / PR #105. The existing manual original-Cryptids workflow is extended for the eventual source check.

### Relationship to the existing adjacent-even fatal sieve

The Q-parent chain is a specialization of the existing adjacent-even fatal sieve. Put \(k=K+1\). For \(j\ge1\), the child deficit is
\((2K+7)2^j=(2k+5)2^j=2^{j-1}(4k+10)\), so the old same-level depth is \(m=j-1\). The source theorem in [SweepAdjacentFatal.lean](../agent7-746-bitsweep/SweepAdjacentFatal.lean) applies; [SWEEP-ODD-FATAL-DEPTH.md](SWEEP-ODD-FATAL-DEPTH.md) supplies the odd-\(m\), level-sector and conditional mod-9 restrictions. Independently, the new theorem t1_q_parent_fatal_sector proves directly from the exact Q equation that \(K\bmod6\in\{2,3\}\) and \(j\) is even, hence \((K+2)\bmod6\in\{4,5\}\). The conditional original-machine bridge therefore needs only \(K+2\ge257\); it derives the fatal sector internally. For \(j=0\) the child is \(F_{K+2}\), the direct odd-output branch. Thus PR #106 is a root-specific source bridge into existing fatal-entry results, not a new generic fatal-depth sieve. The sector lemma has been checked in a core-only Lean 4.36.0-rc2 file; the full source-module compile remains pending.

## 14 November 2026: 100,000-step blank-root forward orbit and 3-adic coverage

The reproducible [root forward audit](root_forward_3adic.py) ran 100,000 exact reset transitions from height 2 in [CI 43638425432](https://github.com/FlareZ123/bb6/actions/runs/43638425432). It reached level K=77,220 (height bit length 77,223) without halting. The 49,717 level-entry heights cover every residue congruent to 2 modulo 3 modulo 3^7, and 2,186/2,187 such residues modulo 3^8. The prefix also contains same-index fatal congruence matches at every precision 3^a for 2≤a≤8, so fixed-modulus height-versus-fatal residue exclusions through 3^7 do not separate this root prefix.

The [full report](ROOT-3ADIC-COVERAGE-100K.md) includes the exact recurrence, coverage table, terminal-residual statistics, and a counterexample showing that the observed all-odd-exit tail is not implied by the simple condition D_K odd and D_K>4K+10. These are finite computational observations, not a proof of infinite 3-adic density or nonhalting.

The [level-deficit analysis](../agent44-746-rank/LEVEL-DEFICIT-DYNAMICS.md) now supplies a source-connected forward coordinate. At level (K), (D=8\cdot2^K+K-h) halves under an even reset; for a nonfatal entry (D_{\rm in}=2^e r) with (r) odd, the level exits oddly exactly when (e=0) or (r>2K+5). At an odd exit, (A=(D_{\rm exit}-2K-5)/2=2^t a) with (a) odd and (t=v_2(A)), while the next height obeys (2h'+5=3^{t+1}d). Thus a fatal next entry at (n) requires (3^{t+1}d=8\cdot2^n-2n-3). This gives an exact mixed 2-adic/3-adic incidence condition and a concrete root-specific proof target; it is not an infinite nonhalting proof. The source Lean module's CI status is recorded in the detailed note.

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
