# Uniform odd-branch ancestors of the complementary #746 cascade fatal heights

**Agent 7, 2026-11-03, R-20261103T0900Z-agent10-cascade. Status: locally Lean-kernel-checked all-natural source-indexed C/P reachability theorem and global mass invariant. Exact original source transitions have been copied verbatim into a self-contained Lean module but the upstream DeepMind module has not been imported and source CI remains pending. No blank-origin machine decision or BB(6) bound. External novelty not reviewed.**

## Exact model and provenance

Original source: Google DeepMind cryptids module
`BusyBeaver/BB6/M_1RB0LF_1LC1RA_0RE0RD_HHH1LE_1LF1RC_1LC1LA.lean`,
blob `6955c0d454833fb188620475f6f72aa7244f09da`. The six-state RLE is `1RB0LF_1LC1RA_0RE0RD_---1LE_1LF1RC_1LC1LA`. Its certified accelerated root is `C(0,3)`, reached after seven primitive steps. The original source's Lean `State.C(a,b)` actually encodes displayed `C(a,b+1)`; we adopt **source-indexed** `C(a,b)` throughout. The original `next` goes from C to P and back. Eliminating the P sweep gives the next-C partial map

```text
C(a,0) -> C(2,2a+1)
C(a,1) -> HALT
C(a,b) for b>=2, d=b-2:
    if d>=2a, C(2a+2,d-2a)
    otherwise, C(floor((6a+d+[8 if d even else 5])/4),
                 (6a+d+[8 if d even else 5]) mod 4)
```

These cases were independently tested against the literal C/P source-indexed rules in 20,000 synthetic episodes using [verify.py](verify.py). The **all-input Lean proof** [SourceMacro.lean](SourceMacro.lean) defines the nine C/P clauses exactly as the original source and establishes `CascadeSource.C_step_sound` for their C-to-C elimination, including both exhaustive sweep regimes. In addition [EpisodeFuel.lean](EpisodeFuel.lean) establishes `CascadeSource.C_step_exact_fuel`: for every b≥2, the first subsequent C is at precisely a+2 source-indexed accelerated transitions. Original-source import and manual CI are still missing, so do not mislabel this as a compiled import of Google DeepMind's module.

Let `R(h)` be the first return from C(h,0) to another state with second coordinate zero, or HALT if the initial return cascade encounters C(_,1). A fatal reset height has form

`c_n=4*2^n - n - 4`.

Agent 10's independent programme claims an exclusion for `n mod 6 in {0,1,2,3}`. This note studies the **complementary indices** and does not reassert Agent 10's other-class theorem.

## Exact new infinite arithmetic certificate

For every `n>=4` with `n mod6 in {4,5}`, there exists a **nonblank synthetic reset height** `h>=0` from which `R` reaches `c_n` in **at most five reset returns**, comprising a valuation-one odd-exit return followed by at most four even-exit returns. The explicit choices are:

| n mod18 | 4 | 5 | 10 | 11 | 16 | 17 |
|---|---:|---:|---:|---:|---:|---:|
| j | 0 | 0 | 4 | 2 | 2 | 4 |

For n>=10 define `p=2^(n-1)`, `T_i=8p+n-1-(2n+3)*2^i`, `Q_j=2T_j+5`, `q=Q_j/9`, `a=2q-3`, and `h=2a-4p-n+3`. Then:

1. `Q_j` is divisible by 9 and `q` is odd, proven by six periodic residue identities `2^18=1 mod9`.
2. The uniform inequality `31*(2n+3)<=2^n`, true for every `n>=10`, guarantees `3p-2<=a<=4p-4`, `14p<=Q_j<=16p`, and `6p-1<=T_i<=8p-3` for all `i<=4`. Thus the arithmetic uses valid positive cascade ranges.
3. The choice `h` has a cascade at exponent `n-2` with odd exit and `v2(a+3)=1`. Its exact reduced return is `R(h)=(9q-5)/2=T_j`.
4. For each `i<j`, `T_(i+1)` has a cascade at exponent `n-1` with even exit and `R(T_(i+1))=T_i`, because `T_(i+1)+8p+n-1=2T_i`.
5. `T_0=8p-n-4=4*2^n-n-4=c_n`.

For n=4,5, the finite witnesses `(j,a,h)=(0,23,13)` and `(0,51,36)` complete the statement.

The [CascadeOdd.lean](CascadeOdd.lean) theorem `CascadeOdd.all_surviving_have_odd_parent` proves the six-way modular selection, integer bounds, exact valuation-one arithmetic, and every intermediate chain identity **for all natural n**. It compiles in Lean 4.36.0-rc2, importing `Std`, without `sorry` or extra axioms; `#print axioms` reports `[propext, Classical.choice, Quot.sound]`. **Stronger source-model theorem:** [ResetChain.lean](ResetChain.lean) proves `CascadeChain.all_complementary_source_reachable`, for every n≥4 in the two complementary classes, `∃h, CascadeSource.Reach (C h 0) (C (4*2^n-n-4) 0)`. Its `Reach` is the reflexive-transitive closure of the literal original C/P `next` clauses copied into [SourceMacro.lean](SourceMacro.lean). All stage guards, the odd-exit phase, the even-return descent and both small n are proved by Lean; the theorem's only axioms are `[propext, Classical.choice, Quot.sound]`. The original third-party imported module is not part of the local compilation. No GitHub Actions source check was dispatched during the runner incident.

**Exact fatal-gate certification:** [CascadeFatal.lean](CascadeFatal.lean) proves `CascadeFatal.every_fatal_height_halts`: every indexed target `c_n=4*2^n-n-4`, for arbitrary n, reaches a source C-state with `next=none`. Combining that theorem with the all-natural complementary predecessor theorem yields `CascadeFatal.complementary_halting_seeds`: for every n≥4 with n mod6 in {4,5}, **some synthetic C(h,0) halts** under the faithfully copied C/P rules. Both theorems compile locally with only standard Lean axioms. No result about the original blank C(0,2) or physical machine's runtime follows.

**Further global theorem:** [Mass.lean](Mass.lean) proves that every successful C-to-C source-indexed episode strictly increases `M(a,b)=2a+b`, including the entire underflow branch. Its `orbit_mass_mono` and `future_target_exclusion` are kernel-checked all-time corollaries: after a source-indexed C orbit reaches mass greater than `2t`, that orbit cannot later visit reset `(t,0)`. This is a reusable finite-prefix plus monotone-cutoff tool. It does not exclude the infinitely many higher fatal targets.

## Independent exclusion-side audit and partial uniform proof

The companion [reverse_audit.py](reverse_audit.py) independently checked the opposite index classes, n mod6 in {0,1,2,3}, through n=2048: 1,367 candidate heights, 1,385,795 exact even-inverse edges, longest chain 2,036, all terminating in a non-image interval gap with no 2 mod3 odd-exit possibility. The fixed SHA256 terminal digest is `00562d6cd505e61d872d5868dd44b640121070475bdab08da8c8ddaa6dd7ca96`. This is finite evidence, not an all-index exclusion.

The new [ReverseResidue.lean](ReverseResidue.lean) proves for *all* n≥4 with n mod6 in {0,1,2,3}, and any natural i satisfying the exact untruncated inverse height equation `T_i+(2n+3)2^i=8*2^(n-1)+n-1`, that `T_i mod3 ≠2`. It is a kernel-checked all-index obstruction to an odd-exit predecessor, using only standard axioms. The separate uniform proof that each even-inverse chain terminates in the gap between adjacent dyadic even-exit image intervals has not yet been Lean-verified.

The auxiliary [GapCore.lean](GapCore.lean) proves a reusable parity unit-gap: if u is even, k odd, 2p=u s, n<s, and k s≤2p+n, then k s+s≤2p. Its derived `terminal_lower_gap` bounds the next inverse below-step above 4p−3, the upper endpoint of all smaller dyadic images. This is Lean-verified under its explicitly stated hypotheses. Translating the complete terminal-exit conditions to those hypotheses remains a separate obligation.

## Independent reproduction

Run `python verify.py` for 20,000 independent C/P source episodes, plus all 100 complementary-class indices 4<=n<=300 and their complete forward witness chains. Output on the original local run:

```text
PASS: 20000 direct original-C/P episode checks; 100 source-C reset ancestry checks n<=300; max depth 4; every surviving residue class covered
n=4, n%18=4, j=0, odd-parent=13, entry=56, fatal=56
n=5, n%18=5, j=0, odd-parent=36, entry=119, fatal=119
n=10, n%18=10, j=4, odd-parent=1263, entry=3737, fatal=4082
n=11, n%18=11, j=2, odd-parent=3094, entry=8102, fatal=8177
n=16, n%18=16, j=2, odd-parent=101817, entry=262019, fatal=262124
n=17, n%18=17, j=4, odd-parent=203360, entry=523712, fatal=524267
```

## Interpretation and remaining obligation

The demonstrated odd-exit ancestors rule out a simplistic argument that all complementary fatal heights are excluded merely because the parity-constrained even-exit image has gaps and no odd-exit preimage. This is a **synthetic inverse-orbit compatibility theorem**. The authentic blank reset starts at height `2`; none of our constructed `h` values is proved to occur along that specific orbit. A true blank-origin invariant, or a certified actual halt, is still necessary. The result does **not** establish halting, nonhalting, the exact BB(6), or a new upper bound. Strong next work: source-level Lean bridge for `R`, independent adversarial validation and an actual blank-root-sensitive invariant that separates height 2 from the constructed synthetic ancestors.

The related original-source issue is [the Agent 10 cascade programme](../../research/issues/R-20261103T0900Z-agent10-cascade.md); intermediate work stays here, not under academically reviewed `results/`.

## Fixed low fatal gates: candidate finite-prefix mass proof

The independent exact source-indexed blank-height C orbit beginning at (2,0), computed using [verify.py](verify.py)'s original C/P rules, reaches C(2,119) at the 21st compressed C episode with mass 123. This crosses the mass of c_4=56 (mass 112), and none of the 21 preceding C states equals C(56,0). It reaches C(218,0) at episode 28 with mass 436, crossing c_5=119 (mass 238); no preceding C state equals C(119,0). By the all-time proved [Mass.lean](Mass.lean) `future_target_exclusion`, a *separately kernel-checked* finite forward-prefix certificate through episodes 21 and 28 would upgrade these to source-indexed all-time blank reset exclusions. At this writing the prefix checks are independent executable computation, **not yet Lean certificates**, and therefore these exclusions must not be presented as formally proved. This offers a narrowly scoped transfer test for the source-valid monotone mass method, distinct from the synthetic ancestor family.


## Two source-indexed genuine-root fatal reset exclusions (2026-11-04)

[LowGates.lean](LowGates.lean) now gives reusable `CascadeSource.shield` and the proved general `shield_sound` theorem. The Boolean checker follows a finite source-C episode prefix, rejects the target at every visited prefix node, and accepts only when the last state's weighted mass exceeds the target's mass (or when `Cstep` terminates without touching it). Its soundness uses the previously proved all-time `orbit_mass_mono`, so a true certificate excludes the target across *every* future compressed transition, regardless of orbit length.

From the authentic blank-derived post-initial source-indexed root `C(2,0)`:

- After exactly 21 C episodes, `C(2,119)` has mass `123 > 2*56=112`; a kernel `decide` certificate checks the entire prefix never visits `C(56,0)`. Theorem: `blank_excludes_fatal_four : ¬Orbit (2,0) (56,0)`.
- After exactly 28 C episodes, `C(218,0)` has mass `436 > 2*119=238`; likewise, `blank_excludes_fatal_five : ¬Orbit (2,0) (119,0)`.

Both locally compile in Lean **4.36.0-rc2** against same-definition local `SourceMacro.Cstep` and `Mass` with standard kernel axioms `[propext, Classical.choice, Quot.sound]`, no `sorry`. The unchanged repository-source chain subsequently passed [manual CI 41767951949](https://github.com/FlareZ123/bb6/actions/runs/41767951949). **Originality correction:** Agent 10 had already formally excluded both heights, and indeed all first six indexed fatal heights, in [SmallFatal.lean](../agent10-cascade/SmallFatal.lean) and [earlier successful CI 41706900676](https://github.com/FlareZ123/bb6/actions/runs/41706900676). This LowGates proof is an independent recheck and a reusable generic cutoff certificate; do not present the two exclusions as a new mathematical discovery. The original DeepMind TM-to-accelerator module is still not imported by this copied-source module.


## Strengthened source-model complete halting criterion through index 47

[SurvivingSmall.lean](SurvivingSmall.lean) generalizes the cutoff to an arbitrary finite set of potential targets. The kernel proof `shieldSet_sound` states that a true Boolean certificate, excluding target membership throughout a finite forward prefix and establishing a strict weighted-mass threshold for **every** target at the final node, excludes every listed target for all future source-C episodes. With a concrete 1,943-episode certificate at the authentic post-initial root `C(2,0)`, the kernel checked

`blank_excludes_survivors_through_47 : ∀ n ≤ 47, n%6∈{4,5} → ¬Orbit (2,0) (4*2^n-n-4,0)`.

Combining with Agent 10's already source-checked [ExactGate.lean](../agent10-cascade/ExactGate.lean), [SurvivingExactGate.lean](SurvivingExactGate.lean) proves the exact, stronger remaining source-model criterion:

`(∃ a, ReachC (2,0) (a,1)) ↔ ∃ n, 52≤n ∧ (n%6=4∨n%6=5) ∧ ReachC (2,0) (4*2^n-n-4,0)`.

This eliminates the 14 otherwise-surviving finite indices 4,5,10,11,16,17,22,23,28,29,34,35,40,41,46,47 (16 values total), including the two already resolved by Agent 10. The next possible index is 52. **Unmodified shared proof-module verification** [manual CI 41769080509](https://github.com/FlareZ123/bb6/actions/runs/41769080509) **succeeded**, compiling original repository `SourceMacro`, `Mass`, `SurvivingSmall`, all nine Agent10 supporting modules, and `SurvivingExactGate`. The axioms are standard `propext`, `Classical.choice`, `Quot.sound`; no `sorryAx`. The source is the accurately copied high-level accelerated transition, **not** an imported check of the upstream Cryptids physical TM bridge. No global nonhalting result or BB(6) bound is established, and extending the finite cutoff indefinitely would not itself decide the remaining infinite family.


## Original upstream Cryptids source import and rooted exclusion (2026-11-04)

The previous CI failure for the upstream bridge was an infrastructure/source-staging error: Lean's project environment rejected proof inputs under `/tmp`, outside the checkout root. The [manual original-source workflow](../../.github/workflows/agent10-746-original-cryptids.yml) now stages source under the pinned Cryptids project root, preserves the exact upstream commit `c86f15861709b76042998c5211c7b2f83991621b`, builds unmodified `BusyBeaver.BB6.M_1RB0LF_1LC1RA_0RE0RD_HHH1LE_1LF1RC_1LC1LA`, and checks the original machine's `highLevelNext` against Agent10's all-input [OriginalNextBridge.lean](../agent10-cascade/OriginalNextBridge.lean).

In addition, [OriginalSurvivingBridge.lean](OriginalSurvivingBridge.lean) formalizes two source-connected consequences: no genuine original `highLevelStart` orbit reaches a surviving-index fatal reset with n≤47, and every actual reached indexed fatal reset must have n≥52 and n mod6∈{4,5}. **Manual original-source Lean CI [41769707538](https://github.com/FlareZ123/bb6/actions/runs/41769707538) succeeded**, compiling these theorems from the actual pinned, unchanged upstream Cryptids high-level transition definition with standard kernel axioms only. The upstream source itself contains its independently verified true-blank TM-to-high-level acceleration proof `isHalt_iff_highLevel_acceleration`; the two newly stated theorems concern actual high-level orbit visits. They do not assert a new direct theorem equivalent to raw-machine halting, which would require an additional finite-reachability/halting transport statement. The original accelerated machine is still undecided.


## Exact logarithmic source-C predecessor enumeration and sound reverse certificates (2026-11-04)

In [WellInverseCases.lean](WellInverseCases.lean), the source-C relation is inverted **exhaustively** under the previously proved blank-root phase-language invariant `b∈{0,2} ∨ ∃m, a+2=4*2^m ∧ b%2=1`. All five inverse cases and their guards are established for arbitrary natural counters and arbitrary actual source-C edges, with no finite search assumptions. In [PreimageCandidates.lean](PreimageCandidates.lean), `source_well_preimage_complete` proves that every invariant-compatible predecessor of `C(u,v)` belongs to a concrete list with O(log(u+2)) candidate terms, using `Nat.log2` and the dyadic sweep-phase form. Both compile in the full unchanged repository dependency chain.

[ReverseCertificate.lean](ReverseCertificate.lean) implements `preimageEdges(u,v)` by filtering that complete candidate list for the exact `Cstep` equality and a decidable phase invariant. The fully quantified theorem `reverseCert_sound` proves: for *any* target `x` and finite fuel `k`, if `reverseCert k x=true`, then `¬CascadeSweep.ReachC (2,0) x`. It uses the previously proved actual blank-root `SweepInvariant.well_reachable` to make the candidate list exhaustive on the genuine root orbit. Fuel exhaustion is conservative (false), root appearance is false, and every candidate edge must recursively receive a valid certificate. **Manual standard Lean 4.36.0-rc2 dependency-chain CI [41772793093](https://github.com/FlareZ123/bb6/actions/runs/41772793093) succeeded**, with no `sorryAx`, and only standard logical kernel axioms in the generalized soundness theorem. This is a rigorous reusable theorem about the copied exact high-level C-step model, whose original-upstream correspondence was separately verified by [41769707538](https://github.com/FlareZ123/bb6/actions/runs/41769707538).

The independent [reverse_well.py](reverse_well.py) mirrors that exact inverse grammar and checks it against the full forward `Cstep` on a rectangular finite state grid. Empirical complete inverse-cone searches, each following **all computed invariant-compatible predecessors** without truncation, found:

| Fatal index | Source-invariant reverse nodes | Maximum reverse depth | Root seen |
|---:|---:|---:|:---|
| 52 | 3,363 | 2,491 | no |
| 53 | 3,741 | 2,538 | no |
| 100 | 14,148 | 9,393 | no |
| 101 | 14,005 | 9,791 | no |

These are finite exact computational reports; they only become kernel-checked exclusion statements if the per-target Boolean certificate itself is evaluated by Lean's trusted reduction. The abstract `reverseCert_sound` proof alone does **not** certify `reverseCert k x=true` for the listed large inputs. A direct kernel `by decide` for n=52, fuel 2600 was too expensive in a local limited run and was **not** included as a theorem. Do not claim this reverse search settles #746. Separate Agent10 `FastShield.lean` / `RootMin256.lean` has already certified a stronger forward finite cutoff through n=256 using an independent method. Larger reverse-cone searches can be substantially costlier, with n=400 and n=1000 truncated at the explicit limit 100,000 nodes.

The exact predecessor classification and conservative checker may be useful for proving parameterized *backward-closed* global invariants that directly exclude all infinite complementary fatal heights, which the current finite cutoffs cannot solve. Further work must connect source-level symbolic properties to a truly all-index theorem or a genuine blank-reached halt; finite nonmembership observations are not a machine verdict.
