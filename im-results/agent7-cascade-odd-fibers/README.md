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

Both locally compile in Lean **4.36.0-rc2** against same-definition local `SourceMacro.Cstep` and `Mass` with standard kernel axioms `[propext, Classical.choice, Quot.sound]`, no `sorry`. This upgrades the earlier *finite-prefix numerical candidates* to **all-time Lean proofs in the exact copied source-indexed model**. The [manual shared #746 workflow](../../.github/workflows/agent10-746-exit-source.yml) was extended to compile LowGates against unchanged repository `SourceMacro.lean` and `Mass.lean`; report that separate CI outcome after checking it. The original DeepMind TM-to-accelerator module is still not imported by this local proof, and no BB(6) or entire-machine decision follows. The two classes are merely the first two complementary synthetic-ancestry fatal heights; infinitely many others remain.
