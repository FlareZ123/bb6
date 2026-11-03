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

**Further global theorem:** [Mass.lean](Mass.lean) proves that every successful C-to-C source-indexed episode strictly increases `M(a,b)=2a+b`, including the entire underflow branch. Its `orbit_mass_mono` and `future_target_exclusion` are kernel-checked all-time corollaries: after a source-indexed C orbit reaches mass greater than `2t`, that orbit cannot later visit reset `(t,0)`. This is a reusable finite-prefix plus monotone-cutoff tool. It does not exclude the infinitely many higher fatal targets.

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
