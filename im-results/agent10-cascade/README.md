# Machine #746: dyadic return-image barriers

Original source: `google-deepmind/cryptids`, `BusyBeaver/BB6/M_1RB0LF_1LC1RA_0RE0RD_HHH1LE_1LF1RC_1LC1LA.lean`, pinned Git blob `6955c0d454833fb188620475f6f72aa7244f09da`. The source-indexed C/P semantics and exact C episode map appear in [Agent 7's SourceMacro.lean](../agent7-cascade-odd-fibers/SourceMacro.lean). The blank-rooted sequence reaches post-initial reset C(2,0). The fatal reset heights are `c_n = 4*2^n-n-4`.

## New Lean proofs, Agent 10, 2026-11-03 19:08 UTC incarnation

All four linked Lean modules compiled locally with **Lean 4.36.0-rc2**, without `sorry` or extra axioms; `#print axioms` of their final theorems reported `[propext, Classical.choice, Quot.sound]` or a subset. The full original **repository source dependency** manual CI is dispatched through [the manual workflow](../../.github/workflows/agent10-746-exit-source.yml); check its run result before describing this as GitHub-source-verified. Local imports used byte-for-byte matching minimal definitions of `SourceMacro.Cstep` and `CascadeOdd.ancestor` plus an exact independent copy of `ReverseResidue.lean` for rapid compilation; these are weaker provenance than compiling the actual full dependency files.

1. [TerminalExit.lean](TerminalExit.lean) supplies the missing rigorous dyadic *terminal-gap* argument from [Agent 7's paper notes](../agent7-cascade-odd-fibers/TERMINAL-GAP-NOTES.md). For every n≥10 it proves existence of the unique crossing interval `(2n+3)2^i ≤ 2^n+n < (2n+3)2^(i+1)` and locates the following inverse height `T_(i+1) = 8*2^(n-1)+n-1-(2n+3)2^(i+1)` strictly inside the open gap `(4*2^(n-1)-3, 6*2^(n-1)-1)`. It proves that no even-reset image interval `[6*2^m-1,8*2^m-3]`, for any m, contains that terminal height. The proof imports Agent 7's `GapCore.terminal_lower_gap`.
2. [GapOddJoin.lean](GapOddJoin.lean) composes the preceding gap with [Agent 7's `ReverseResidue.mod3_ancestor`](../agent7-cascade-odd-fibers/ReverseResidue.lean), showing that the terminal height also has residue **different from 2 modulo 3** when n mod6 is 0,1,2,3. It handles the remaining n=6,7,8,9 by kernel-checked exact arithmetic. Main theorem `CascadeGapJoin.all_excluded_residue_gate` covers **all n≥6** in those four classes.
3. [SweepInvariant.lean](SweepInvariant.lean) proves a new all-time, structural source-C-map invariant: every C state reached from a reset satisfies either `b=0`, `b=2`, or `a+2=4*2^m` and `b` odd. A successful edge into a reset C(u,0) must have `u mod3=2` or lie in one of the above dyadic even-image intervals. The proof is symbolic for **every** source-C-map state satisfying the invariant. In particular, `CascadeSweep.root_excludes_nonimage` rules out any such forbidden height along the entire orbit from C(2,0).
4. [RootTerminal.lean](RootTerminal.lean) composes the two arguments: for every n≥6 in the four classes it kernel-proves that a particular terminal `T_(i+1)` is *not* reachable on the genuine post-initial C(2,0) orbit **of the copied exact C-episode map**. This is a quantified all-time rooted exclusion for an infinite family of terminal gap heights, not an original machine nonhalting decision.

The original source module import and the raw physical Turing-machine semantics are not established by these four standalone statements. Agent 7's `SourceMacro.C_step_sound` and `EpisodeFuel.C_step_exact_fuel` give the independently verified C/P connection in their copied source model. Source-to-actual-blank-machine connection should reuse the original pinned Cryptids proof, not be inferred from copied code.

## Remaining fatal gate: the essential backward-chain bridge

**The result does not yet prove the fatal heights c_n unreachable.** To propagate from reachable c_n to reachable terminal T_(i+1), one needs a source-sound *inverse ancestry* theorem: if a reset height u in the scale-p even image interval is reached (u%3≠2), its preceding reset height h must be `h=2u-8p-m` for p=2^m, with proven uniqueness of the dyadic band m and no premature reset. Iterating this over all in-band T_j would contradict `root_excludes_terminal`. Existing [Agent 7 reverse audit](../agent7-cascade-odd-fibers/reverse_audit.py) supplies finite evidence but does not replace this universally quantified first-return inversion.

The earlier proposed exclusion for n mod6 in 0,1,2,3 remains a **candidate full fatal-gate exclusion**, pending this precise chain bridge and source provenance. Complementary classes n mod6 in {4,5} admit source-C synthetic predecessor paths by [Agent 7's ResetChain.lean](../agent7-cascade-odd-fibers/ResetChain.lean); none of these proves blank reachability.

No root-machine halting verdict, new BB(6) bound, or BB(6) exact value is established. Preserve intermediate findings under `im-results/`; external novelty is unreviewed.

## 2026-11-04: Simultaneous blank-root fatal-index shielding through n=100

**Scope:** The checked-in original-copy source-indexed `CascadeSource.Cstep` acceleration, with genuine post-initial root `(2,0)`. This is an all-time exclusion for the accelerated orbit, while the original third-party Cryptids high-level import is a separate proof obligation. Original six-state nonhalting and BB(6) remain open.

[ManyShield.lean](ManyShield.lean) proves a general finite-prefix/monotone-cutoff inference rule `shieldMany_sound`: any finite exact C-step prefix avoiding a Boolean target predicate, followed by a state of mass `2a+b` strictly exceeding a common target-mass cap, excludes *all* targets selected by the predicate from the whole future orbit. A `none` transition also terminates this check soundly. This builds on Agent 7's `Mass.lean` and `LowGates.lean` finite-list/mass technique, independently generalized to a symbolic indexed family. The specific certificate checks up to 7,000 C episodes with common cap `2*(4*2^100-104)`; `badThrough 100` captures all fatal `c_n=4*2^n-n-4` for 4≤n≤100, n mod6∈{4,5}. Two finite `decide` coverage and mass bounds quantify the conclusion universally over n within this finite range.

[RootMinIndex.lean](RootMinIndex.lean) converts `ReachC` to `Orbit`, combines this certificate with the existing all-natural four-class theorem `CascadeSmallFatal.all_four_class_indices` and the six small indices, and proves:

- `no_fatal_through_100`: for **every** natural n≤100, `¬ReachC (2,0) (c_n,0)`;
- `halt_requires_index_ge_101`: any reached `(a,1)` entails a reached fatal `(c_n,0)` at **n≥101** and n mod6∈{4,5}.

The manual **unchanged checked-in dependency** [Lean CI run 41769574780](https://github.com/FlareZ123/bb6/actions/runs/41769574780) compiled `SourceMacro, Mass, SweepInvariant, RootTerminal, ResetAncestry, FatalExclusion, SmallFatal, GateNecessary, ExactGate, ManyShield, RootMinIndex` with Lean 4.36.0-rc2. It printed standard Lean axioms only and no `sorryAx`. [OriginalMinIndexBridge.lean](OriginalMinIndexBridge.lean) is prepared to import the pinned *unmodified upstream Cryptids* original high-level machine and transport the n≤100 cutoff; this additional import must be reported only when its own CI succeeds. A previous attempt of `OriginalNextBridge` failed on an external-to-workspace source-file path before Lean elaboration, not on a mathematical counterexample.

**Novelty/overlap:** Agent 7 independently established the same shield strategy with an explicit finite list for surviving indices n≤47 and a bound n≥52 in [SurvivingSmall.lean](../agent7-cascade-odd-fibers/SurvivingSmall.lean) and [SurvivingExactGate.lean](../agent7-cascade-odd-fibers/SurvivingExactGate.lean). The n≤100 certificate is a stronger finite cutoff and a general reusable Boolean predicate checker, but a deeper structural advancement is required to eliminate the infinitely many n≥101 candidates. These facts are intermediate, without external novelty review, and stay under `im-results/`.

## 2026-11-04: Binary-logarithm source certificate through n=256

**Now fully checked against the unmodified checked-in source Lean files:** [GitHub Actions 41772085638](https://github.com/FlareZ123/bb6/actions/runs/41772085638), Lean 4.36.0-rc2, successful, only standard Lean axioms in the source-checked theorem audits. This extends the earlier all-index n≤100 cutoff.

[FastShield.lean](FastShield.lean) supplies the universally quantified **symbolic** identity
`Nat.log2 (4*2^n-n-4)=n+1` for every `n≥2`, with proved lower and upper exponential bounds. Because the binary logarithm uniquely recovers the index, the predicate `badFast N` decides whether any source-indexed C-reset belongs to the surviving fatal-index family through `N` directly from its binary logarithm, avoiding a scan of all possible n values. The checker uses the source-proved strict mass invariant `M(a,b)=2a+b`, a fixed prefix fuel 39,000, and the cap `2*c_256`. The executable certificate is `by decide` with ordinary kernel reduction, not `native_decide`.

The general `fast_root_excludes N fuel n` theorem proves a transfer for *any* index upper bound `N`, given a successful exact `shieldMany` certificate, while `blank_excludes_surviving_through_256` checks the specific bound. [RootMin256.lean](RootMin256.lean) composes this all-time exclusion with the previously proved four mod-six disallowed classes and the first six exceptions. Its theorem `no_fatal_through_256` excludes every indexed fatal height `c_n`, regardless of residue, for `n≤256`; `halt_requires_index_ge_257` requires a reached `c_n` at `n≥257, n mod 6 in {4,5}` for any source-compressed halt.

The [unmodified Cryptids original-source bridge workflow](../../.github/workflows/agent10-746-original-cryptids.yml) separately compiles against pinned upstream commit `c86f15861709b76042998c5211c7b2f83991621b`, Lean 4.35.0-rc4. The [OriginalRawGate.lean](OriginalRawGate.lean) theorem is intended to strengthen the *original raw six-state machine* halting iff from Agent 7's `n≥52` gate to `n≥257`. **Original-source check PASSED:** [GitHub Actions run 41772098475](https://github.com/FlareZ123/bb6/actions/runs/41772098475), pinned unmodified upstream Lean 4.35.0-rc4. The complete original checked-in proof chain, original high-level next relation, Agent 7 physical raw halting iff, and Agent 10 strengthened raw iff all compiled successfully. The emitted `#print axioms` for `Agent10Raw746.original_machine_halts_iff_surviving_257` was exactly `[propext, Classical.choice, Quot.sound]`, with no `sorryAx`. **Now proved for the actual six-state blank-tape TM:** `IsHalt target ↔ ∃ n≥257, n mod6∈{4,5}, ReachC (2,0) (c_n,0)`. This is a completed exact reduction to an unresolved infinite candidate family, not a halting verdict. These findings still leave infinitely many candidate fatal resets and do not decide this holdout or BB(6); they belong to intermediate `im-results/` rather than externally reviewed `results/`.

## 2026-11-04: first-return inverse closed form and reduced backward search (new experiment)

[reset_inverse_fast.py](reset_inverse_fast.py) eliminates all intermediate C/P sweep states from the existing source-indexed #746 search and enumerates the **complete first-reset predecessor set** of a given reset height under the closed first-return formulas. This is an independent, symbolic derivation plus a Python experiment, **not yet a Lean-certified theorem for the inverse algorithm**. It should not be used as a substitute for Agent 7's source-proven [C-episode reverse certificate](../agent7-cascade-odd-fibers/ReverseCertificate.lean) until the closed-form inverse relation has a source-connected proof. The prior Agent 7 [reverse_audit.py](../agent7-cascade-odd-fibers/reverse_audit.py) already exploits the unique even-return inverse, and [reverse_well.py](../agent7-cascade-odd-fibers/reverse_well.py) exhaustively handles full C-state predecessors. The contribution here is the direct handling of **both** even and arbitrary valuation-length odd return predecessors without materializing C-episode states.

### Derivation of the exact source-indexed reset map

Write `R(h)` for the first next C-state `(u,0)` after `(h,0)`, or no reset if the source machine instead halts. For `p=2^k`, the sweep after the initial C(2,2h+1) episode has, after k large-branch transitions,
`A_k=4p-2`, `B_k=2h+2k+9-8p`.
The large guard is equivalent to `h+k+5>=8p`. Let k be the **first** index at which the guard fails. Such a k exists because powers of two eventually dominate h+k. For k>=1, the previous guard is `h+k+4>=4p`; for k=0, h>=0. If `h+k+4=4p`, then `B_k=1` and the return halts, precisely the known fatal height `h=4*2^k-k-4`.

Otherwise the first underflow produces
`a0=4p+floor((h+k)/2)`, with second coordinate zero if h+k is even and two if h+k is odd. In the even case `R(h)=a0`. In the odd case, set `q=a0+3` and `t=v2(q)`. Every C-state `(a,2)` with odd a effects `a+3 -> 3*(a+3)/2`; after exactly t such steps, a is even. The final `(a,2)` step resets at
`R(h)=(3^(t+1)*(q/2^t)-5)/2`.
No halting transition occurs in this B=2 chain.

### Complete inverse formula

For a proposed reset target u, there are exactly these predecessor forms:

1. **Direct even-phase predecessor.** For some unique `p=2^k`, `6p-1<=u<=8p-3`; the predecessor is `h=2u-8p-k`. Candidate p is the largest power of two at most `(u+1)//6`. For k=0 the band contains only u=5 and returns h=2.
2. **Odd-phase predecessor.** Necessarily `3|(2u+5)`. For each `0<=t<v3(2u+5)`, put `q=2^t*(2u+5)/3^(t+1)`. Either `q=7`, giving the unique k=0 predecessor h=1; or there is a unique k>=1 with `6*2^k+1<=q<=8*2^k-1`, giving `h=2q-8*2^k-k-5`. Candidate p is the largest power of two at most `(q-1)//6`.

Both directions follow by substituting these expressions into the first-failure inequalities and the above source-C episode formulas. Each returned predecessor satisfies `0<=h<u`. Thus the reverse graph from any finite u is finite and the complete ancestor set is enumerable without an arbitrary fuel cutoff. Each input produces at most one even candidate and at most `v3(2u+5)` odd candidates. The Python function filters by the exact dyadic bands; it never guesses the reset scale by simulating all intervening C sweeps.

### Reproducible experimental results and limits

The script's `self_test()` validates h<100000 against inverse membership, compares all target u<10000 against all h<500, and conducts 2,500 seeded random large-integer round trips (seed 74620261104, widths 32,64,256,1024,8192 bits). In a separate independent simulator, the direct R formula agreed with actual `SourceMacro.Cstep` episodes for every h<100000. These tests confirm implementation consistency; they are not a replacement for mathematical/Lean source proof.

Its `audit(257,2048)` exhaustively expanded every reset parent of each **597** h-index candidates `n in [257,2048], n%6 in {4,5}`, under the derived inverse. All reverse cones ended without h=2. A total of **1,036,567** reverse nodes were visited across the 597 targets; largest was **3,106** nodes at n=2039. Deterministic digest (ASCII lines `n:nodes:edges:0\n` in increasing n, SHA256):
`6483385549d25f3b540ad45d9edf40fa1bf6432b8126e07a6767782ea2573984`.
Examples: n=257 has 380 reverse nodes, n=263 has 378; n=10000 has 15,194 and n=10001 has 15,126. For comparison the existing unoptimized C-state inverse reports 14,148 nodes for n=100, where the reset inverse has 141. These are finite computational results for a copied source model, **not formally certified exclusions**, not a universal argument for all candidate n, and not a BB(6) upper bound.

**High-value next step:** Encode the complete first-reset semantics and the two inverse cases in Lean, reusing exact `SourceMacro.Cstep` / `ResetAncestry` / `CascadeSource.C_step_sound` and the original pinned Cryptids source bridge. Then use the finite reverse certificates to certify an entire new bounded candidate interval. A deeper target is a symbolic invariant in the inverse reset graph applying to all n mod6 in {4,5}, avoiding an ever-growing finite cutoff. Document exact first-return source proof before advertising any kernel-certified extension.
