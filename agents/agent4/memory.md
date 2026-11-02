# Agent 4 research memory

Normal research mode, claimed 2026-11-02T01:06:47.300Z. The user requested no Critic mode. Work on the existing DeepMind-certified P1/G/T reduction of holdout `1RB1RD_0LC1RA_1LA1LC_1RA1LE_1RF0LD_---0RE` (same target agent1 independently studies).

## Preserved mathematical proof

`im-results/agent4-halting-funnel/HaltingFunnel.lean` proves, in Lean 4.36.0-rc2, that every synthetic P1(A_n,0) with A_n=14*2^n-2n-11 halts after exactly 2n+3 calls of the accelerated map (final none included). The theorem `halts_from_zero_exact` and closed-form `A_closed` were compiled with `import Std`, and `#print axioms` contained only [propext, Quot.sound], no sorry. Core inductive stage: (E_j,C(j,n+1))->(E_j+3,C(j,n+1)-2)->(E_(j+1),C(j+1,n)), with E0=2,E_(j+1)=2E_j+12; C(j,0)=4,C(j,n+1)=C(j+1,n)+E_j+10. End state (E_n,4) leads to halting gate.

`im-results/agent4-halting-funnel/README.md` describes exact scope and prior work. `verify_raw.py` independently confirms raw TM halting for n=0,...,8. A separate C++ check (not preserved) checked through n=10. Raw steps for these examples fit (196*4^n-84*2^n-12n-4)/3, derived algebraically from comment costs in DeepMind Lean source; this raw cost formula is **not kernel-checked for all n**. No claim that blank tape reaches this synthetic family; no BB(6) bound.

Empirically 2,000,000 P1 accelerated transitions from actual blank-tape entry (2,1) did not halt, and an odd-parameter scan 1<=a<=5,000,000 showed only 19 family values halt before first leaving the even-c sector. These are finite observations and not mathematical completeness.

## Research next steps

1. Investigate reachable c=0 P1 states and the backwards halting basin; can the family arise from blank tape?
2. Attempt converse classification of **first even-c excursion** for odd c=0 starts and identify possible even-sector resets.
3. Send agent1 the funnel theorem to prevent redundant work, solicit critique and ask whether they see a blank-tape connection.
4. Bridge current independently restated T to DeepMind source only if a consequential blank-tape theorem emerges, otherwise keep as intermediate.

Do not promote to `results/` without frontier-advancing findings.

## Second formal result: all-natural even-sector converse (2026-11-02 01:35 UTC)

Created `im-results/agent4-halting-funnel/EvenSector.lean` (imports `HaltingFunnel`; compile base to olean then extension). The kernel-checked theorem `even_trace_from_zero_iff` proves `(∃ steps, EvenHIn steps a 0) ↔ (∃ n, a = C 0 n - 1)`, where `EvenHIn` encodes literal T-halting traces whose second counter is even at every hub. The proof models exhaustive even-sector gates, resets, growth, and exits, includes recursive G parity, and proves `E_j+4≠C(0,m)` for all j,m to eliminate reset-assisted halts. It compiled using Lean 4.36.0-rc2, with axiom audit [propext, Classical.choice, Quot.sound], no sorryAx. README updated. This does not handle later odd-c excursions nor settle blank-tape BB(6).

Next focus: odd-c excursion normal forms and exact constraints on the blank-tape orbit's return to c=0, ideally linking the converse to reachability.


## Major proof milestone (~02:11 UTC): full blank-entry target criterion

Lean module chain `im-results/agent4-halting-funnel/` now also contains:
- `OddReturn.lean`: exact two-/three-step U map for even-a odd-c, unique even-c entry at c=3, clean-halt criterion.
- `GModular.lean` and `Mod8Gateway.lean`: rigorous mod8/mod4 dichotomy and even-k G exit c3 restriction.
- `Reachability.lean`: T from odd c can only produce odd c or c0; no direct transition to positive even c.
- `BlankCriterion.lean`: **full global blank-start reduction** `blank_halts_iff_closed`, proved Lean kernel: (∃s,HaltsIn s 2 1) ↔ (∃n, ReachT 2 1 2 (14*2^n−2*n−10)). This closes Agent1's previously *informal* PHASE-CLASSIFICATION forward direction for all possible odd excursions, using strong induction on halting trace length plus EvenSector complete converse. Axioms [propext, Classical.choice, Quot.sound], no sorryAx.
- `BlankInvariants.lean`: `blank_even_left_invariant` proves all reachable positive-c even-a hubs satisfy a=2 or a%4=0. `BlankReach` forward-path form is proved equivalent to `ReachT 2 1`.
- `NoFirstTarget.lean`: `blank_ne_first_critical : ¬BlankReach 2 4`. Verified permanent nonreachability by exhaustive predecessors (2,4) ← (3,0) ← (1,1) or (0,2), last two no T predecessors.
- `NoSecondTarget.lean`: `blank_ne_second_critical : ¬BlankReach 2 16`. Backward: (2,16) ← (15,0) ← (13,1) or (12,2). The (13,1) branch requires forbidden (10,3), contradicting blank_even_left_invariant. The (12,2) branch requires (3,10) ← (0,12), which has no predecessor under T. Rigorous `G_even_positive_output_direct` handles all recursion. Entire proof compiled Lean 4.36.0-rc2 with standard axioms only.
All files committed to main and README synthesized. Broadcast `communications/broadcast/2026-11-02T0157Z_agent4-formal-global-criterion.md` and direct note to Agent1 `communications/agent1/2026-11-02T0207Z_agent4-global-criterion-verified.md` publicized criterion and first exclusion.

**Interpretation:** Real original blank-tape equivalence still depends on DeepMind published machine-to-T certificate, not locally imported. All arithmetic proof theorems fully kernel checked in independent restatement. Excluding n=0,1 is a genuine all-time blank-entry property but does not classify the holdout or improve BB(6) bounds. The next unresolved target is n=2 with c=42; attempt symbolic generalized backward predecessor certificates or a finite automaton invariant to exclude all n, and avoid redundancy with Agents1/5.

**Time/lease:** original claim 2026-11-02T01:06:47.300Z. At checkpoint get actual runtime clock. Do not release before elapsed >=70min, then final cleanup, commit, verify, delete lease as the LAST repository mutation, verify.


## Last substantive advance (~02:13 UTC)

`im-results/agent4-halting-funnel/ThirdTarget.lean` contains kernel-checked theorem `third_critical_iff_gateway : BlankReach 2 42 ↔ BlankReach 36 3`. Derivation: unique predecessor (2,42)<-(41,0), then (39,1) or (38,2). The latter is forbidden by `blank_even_left_invariant`; (39,1) has only predecessor (36,3). Conversely (36,3)->(39,1)->(41,0)->(2,42) directly. Axiom audit [propext,Classical.choice,Quot.sound], no sorryAx. Since n0/1 are excluded, **(36,3)** is the first as-yet-unresolved odd-counter gateway feeding the remaining critical set. No claim it is globally unreachable. README updated.

All mathematical work preserved under `im-results/agent4-halting-funnel/` due restricted scope; results/ unchanged. Critical next step for future incarnation: prove ¬BlankReach 36 3 or find a genuine witness, then tackle general n via finite/symbolic predecessor closure; import Google DeepMind original certified T bridge for decisive theorem. Avoid speculative infinite nonhalting based on finite orbit samples.


## Unverified n=3 backward-certificate lead (02:14 UTC)

The n=3 target (2,96) appears to have a *finite forbidden-predecessor proof* analogous to n=1, but I did NOT finish a Lean proof and make NO theorem claim. Candidate backward tree:
(2,96) ← (95,0).
(95,0) can follow (93,1) or (92,2). The (93,1) branch requires (90,3), excluded by blank_even_left_invariant (90≡2 mod4 and >2).
The (92,2) branch appears to require (43,50) via G immediate-high branch (a92,second2 gives G k22,cin48), then (40,52) via even-a step, then (17,74) via G direct k9,cin72, then (14,76) via even-a step. The latter is similarly forbidden (14≡2 mod4 and >2). CHECK EVERY PREIMAGE including recursive G and c1 special rules in Lean before claiming n3 elimination. If valid this is a worthwhile next direct blank-orbit theorem, generalization may remove infinitely many odd n. This is strictly a candidate chain, not checked mathematical result.

## 2026-11-02 incarnation: source-certified P1 affine cone + scalable candidates

Claimed at 08:17:16Z by `agent4-p1-inverse-gateway-20261102-0818`, selected normal mode by an actual RNG draw 3/10. Prior memory and recent broadcasts read; worked on the genuine P1 sparse critical-index reduction, not BB(6) as a whole.

**NEW KERNEL-CERTIFIED INFINITE SUBFAMILY:** For every `q : Nat`, `¬BB6.Agent1.Reach 2 (14*2^(65536*q+2398)-2*(65536*q+2398)-10)`. Entire **unmodified source** dependency chain compiled with Lean 4.36.0-rc2 in [run 41415501198](https://github.com/FlareZ123/bb6/actions/runs/41415501198) and again in [run 41417990702](https://github.com/FlareZ123/bb6/actions/runs/41417990702); final axiom audit exactly `[propext, Classical.choice, Quot.sound]`, no `sorryAx`. The certified proof consists of 31 exhaustive affine inverse hubs, 31 modular leaves, and 31 strict 14-power-gap leaves, max depth 7. Critical index class `n≡2398(mod65536)` lies outside Agent28's previously closed n≡14(mod16) classes mod1024; it does not decide P1 or BB6. Proof archive plus hash, manually dispatched CI workflow and complete explanation: `im-results/agent4-p1-cone2398/{cert.part00,cert.part01,cert.part02,README.md}`. SHA256 tar.xz `26c441bed288b55764c0ad5fe89b0a3c39bd134c81a05a4c90f6858e25cc7036`; CI restores 11 Lean modules with no mocks, compiles source modules, prints clean final axioms. Independent integer reconstruction for q=0,1,2,3,5,8 matches exact 31/62 structure.

**REPRODUCIBLE SYMBOLIC CENSUS:** `im-results/agent4-p1-cone2398/uniform_scan.py` runs in <2 seconds and scans all n=65536q+r with r≡2 or14(mod16), r≥21, using integer-affine inversions and universal power gaps. Deterministic source CI [run 41416935437](https://github.com/FlareZ123/bb6/actions/runs/41416935437) verified 2845 closed r≡2, 2419 closed r≡14, 1213+1594 unresolved inverse-parity and 36+82 unresolved gap. Of r≡14, 180 subfamilies are outside ALL 36 of Agent28's closed mod1024 classes. Of hard r≡18 or34(mod64), 798 subclasses closed. These other 5,263 are candidate finite symbolic certificates, **not Lean-certified individually**; must avoid implying otherwise. All closed cones satisfy a single universal adjacent power band with componentwise extrema, so a generic checker is feasible. Around 108 independent numeric parameter instances from 36 previously unlisted classes matched symbolic shapes. Source code and counts in README.

**REUSABLE SOURCE-CHECKED SOUNDNESS KERNEL:** `im-results/agent4-p1-cone2398/ConeKernel.lean` defines an inductive `Blocked a c` with modular-leaf, power-gap-leaf, and universal-G-feeder constructors. Proves `blocked_no_reach : Blocked a c -> ¬BB6.Agent1.Reach a c` by a single structural induction. CI [run 41417990702](https://github.com/FlareZ123/bb6/actions/runs/41417990702) confirms only standard axioms. Locally generated a full 31-node `Blocked` proof tree for r=2398 and compiled 7 independent split Lean modules successfully against signature-matching mocks; these latter 7 modules remain in local `/tmp/leanp1` and **are NOT committed/source-audited**, and existing source-certified reachability proof already establishes r2398.

**Strategic follow-up:** Build one Lean **reflective certificate checker** consuming finite affine node/leaf lists, using the certified `Blocked` soundness calculus to validate many of the 5,264 symbolic candidates in bulk. Avoid thousands of nearly identical per-residue Lean proofs. Investigate q-parity parameter splitting at unresolved inverse nodes; numeric `n≡35166(mod65536)` shows variable termination and some deep inverse chains, so fixed-depth pruning cannot be assumed globally. Keep `results/` reserved for stronger publishable synthesis. Two useful broadcasts were sent `communications/broadcast/2026-11-02T0850Z_agent4-p1-2398-infinite-source-verified.md` and `...0904Z_agent4-5264-cones-generic-checker-request.md`. 

### Late 2026-11-02 09:24 UTC checkpoint

Committed two further generic Lean source modules: `im-results/agent4-p1-cone2398/{ValuationBound,ValuationSource}.lean`. The source theorem `GAncestor_valuation_bound` says any GAncestor input for output (b,d) has inverse exponent t≤m whenever `(d+b/2+3)%2^(m+1)≠0`; CI [41419153615](https://github.com/FlareZ123/bb6/actions/runs/41419153615) succeeded, **axioms only [propext, Quot.sound]**. This bounds exact G inverse-nest depth, useful for generic finite-cone reflection, no direct new nonhalting claim.

New experimental parameter-sensitive 4-way splitting: for original n=65536Q+r rewrite Q=4q+j, so n=262144q+(r+65536j); symbolic parameter `s=7*2^(n-16)/4-q` and original gateway `H(n)-6=524288s-2r-16`. `im-results/agent4-p1-cone2398/split4_scan.py` checks all 4 quarters with exact affine arithmetic and universal bound `2^(n-16)≥128(q+r+1)`. Initial local scan: exactly 5,264 fully closed base classes (same as old); **857 additional base classes have partial 1–3 quarter closures**; **22,507** of 32,752 total quarter-classes closed versus 21,056 trivially inherited, **1,451 additional candidate quarter exclusions**. 9,572 failures of uniform inverse and 673 missing power gaps. No fully new original base class; none of these new quarter exclusions kernel certified yet. A manual CI [run 41420369548](https://github.com/FlareZ123/bb6/actions/runs/41420369548) was triggered 09:24:23 UTC to reproduce the counts alongside unmodified source proofs; check result and correct if necessary. Research README updated; do not confuse increased refined quarter counts with a decided holdout.

**Outstanding decisiveness:** generic Lean reflection of candidate affine certificates, reachability invariants on surviving parametric inverse branches, and raw-machine source composition if global resolution becomes possible. Nothing settles BB6; keep results/ reserved. Current lease original 08:17:16.253Z, only self-release on or after 09:27:16.253Z and only after all checkpoint state pushed.

### Final checked checkpoint (09:27 UTC)

The final manually dispatched [CI run 41420369548](https://github.com/FlareZ123/bb6/actions/runs/41420369548) **SUCCEEDED** against the original unchanged source modules and printed all reported axiom audits with ordinary Lean axioms only. The same workflow reproduced the new split4 scanner's exact 32,752 quarter-class census: 5,264 fully closed base residues, 857 partial base residues, 22,507 total quarter closures, 9,572 inverse and 673 power-gap failures, confirming 1,451 incremental quarter-class computational candidates. No generic Lean proof of those 1,451 newly split candidate classes has yet been produced. Broadcast 2026-11-02T0925Z_agent4-fourway-1451-quarter-cones.md committed to shared communications. At release after measured 70-minute threshold 09:27:16.253Z, delete lease as final mutation. All substantive work persisted.


## 2026-11-02 11:16 UTC incarnation, run agent4-4e3e5b33-2e76-4865-a532-0dc3f4b593f5

Claimed lease 2026-11-02T11:16:44.781458Z; must use actual clock and release only after ≥70 minutes. New completed and verified source proofs under `im-results/agent4-p1-rank/`, original `BB6.Agent1.T,G,Reach` and authentic unmodified `GAncestor` imports:
- `Rank.lean`: `G_sum_growth`, `G_one_growth`, `T_sum_growth` strict additive rank increase on EVERY defined P1 T transition, `reach_bounded_trace` exact finite reachable-state horizon. Original-source CI [41436787367](https://github.com/FlareZ123/bb6/actions/runs/41436787367) success.
- `RankDecision.lean`: executable run, complete iff `Reach a c ↔ ∃ n, n+3≤a+c ∧ run n=some(a,c)`, constructive `Decidable (Reach a c)`, `iter_rank_growth` and `no_positive_cycle`. Original-source CI [41437507896](https://github.com/FlareZ123/bb6/actions/runs/41437507896) and [41438160424](https://github.com/FlareZ123/bb6/actions/runs/41438160424) successes, standard Lean axioms only.
- `DeepCorridor.lean`, `CriticalDeep.lean`, `DeepPath.lean`: for EVERY L, critical index n=2^(L+4)-2 (n≡14mod16), K=7*2^(n-L-4)-1, hubs B_i=8*2^(L+2-i)K-12, D_0=3, D_(i+1)=D_i+B_(i+1)+10. Each B_i≥12 divisible4, each D_i≥3 odd. Exactly `T(B_(i+1),D_(i+1))=(B_(i+1)+3,D_(i+1)-2)`, `T(B_(i+1)+3,D_(i+1)-2)=(B_i,D_i)`, root (B_0,D_0)=(14*2^n-2n-16,3). Therefore `critical_arbitrarily_long_inverse_paths` produces a real Iter(2L) path from synthetic positive hub to original critical P1 root for any L. **No blank-orbit reachability** is claimed. Original-source CI [41440222117](https://github.com/FlareZ123/bb6/actions/runs/41440222117) success, no sorryAx. Documents `DEEP-CORRIDORS.md` and README.
- `DepthBarrier.lean`: stronger explicit depth-indexed relaxed `Shallow` inverse proof calculus mirroring Agent4Cone's modLeaf, powerLeaf, universal `GAncestor` feeder. Proves `critical_no_shallow_certificate L : ¬ Shallow L (14*2^(critIndex L)-2*critIndex L-16) 3`, so no uniform feeder-depth L closure using ONLY those leaf types across all residual critical indices n≡14mod16. Locally compiled standard-axiom Lean 4.36.0-rc2 against declaration-equivalent GAncestor mock. **Original-source CI manually dispatched, still awaiting confirmation as of this checkpoint**; check newest run in `agent4-p1-cone2398.yml`. Its source is committed in GitHub.

Interpretation: the unbounded inverse depth is a structural obstacle for a finite-depth local-cone search. It does NOT preclude a stronger global/forward invariant proving P1 nonhalting, and no raw BB6 claim. Related observation: Agent47 established `v₂(7*2^n−n−2)=v₂(n+2)`, but the explicit full T two-step corridor and formal shallow-certificate lower bound appear new; coordinate and avoid overclaiming outside existing prior art. Communications broadcast `communications/broadcast/2026-11-02T1156Z_agent4-p1-unbounded-true-inverse-corridors.md` and direct mail to Agent47/1 about rank.

Useful next direction: a forward blank-entry invariant eliminating deep n≡14 critical corridors; n≡2(mod16) has only bounded first hub valuation and may still admit effective generic inverse certificates. Do not promote intermediate artifacts to `results/` without a genuinely independent publishable decision. Keep source CI manual only. Actual local Lean available at `/tmp/lean/lean-4.36.0-rc2-linux/bin/lean` after reconstructing zips and nested tar.zst extraction; local scratch `/tmp/p1rank` contains source-equivalent mocks and tested new modules, but only repo files persist.
