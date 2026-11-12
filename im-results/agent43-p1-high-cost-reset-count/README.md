# P1: counted inverse-history energy, walls and one-shallow obstructions

**Research synthesis, 12 November 2026.** These are mathematical restrictions on P1's inverse histories. The one-, two-, three-, and four-shallow exclusions are now verified for legal **unchanged-source `inverseAt` transitions** for every critical index n≥14 and arbitrarily long depth-two blocks. Consequently, any legal depth-0/1/2 inverse trace reaching the exact shifted wall has at least five shallow edges. The five-shallow original-source lift now proves at least six shallow edges for n≥83 (PR #62, CI 43299542235). These are source-word exclusions, not an unrestricted blank-root decision or BB(6) solution. Agent50's all-count reset-density theorem remains the strongest general quantitative result.

## Strongest genuine original-source deductions

**Unrestricted reset energy.** [CountedEnergySource.lean](CountedEnergySource.lean) and [CountedEnergyCostSource.lean](CountedEnergyCostSource.lean) certify for every original critical counted inverse history with `n>=14` the upper energy bound

```
m <= n+1+(2*n+3)*z
```

where `m` is total inverse cost and `z` counts genuinely positive-depth resets. It covers arbitrary zero-depth interludes. [Original-source CI 42122986713](https://github.com/FlareZ123/bb6/actions/runs/42122986713) and [42123746362](https://github.com/FlareZ123/bb6/actions/runs/42123746362).

**Small-left wall cost exclusion.** [CountedWall148Source.lean](CountedWall148Source.lean) proves that for `n>=148` a genuine source history on `b=4*(m+n)` must have `n+z<m`, for every reset count and every zero-depth tail. [Original-source CI 42125396876](https://github.com/FlareZ123/bb6/actions/runs/42125396876). Agent50 independently proved the stronger half-plane generalization for `b<=4*(m+n)`, in [SubwallAllCount.lean](../agent50-p1-subwall/SubwallAllCount.lean), original-source [CI 42149985248](https://github.com/FlareZ123/bb6/actions/runs/42149985248). The historical derivations in [WallAboveNPlusZ.md](WallAboveNPlusZ.md) are superseded by these source certificates.

**Exceptional right-five dichotomy and reset floors.** [DepthIndexedResetFloor.lean](DepthIndexedResetFloor.lean) certifies a full original-source dichotomy: a genuine history ending at right counter five either has `3*2^n <= (2*n+3)*z`, or its last positive reset has exactly depth `n+1` and its genuine predecessor lies on the shifted wall `W=b+4m+4n+20=12*2^n`. The predecessor's exact inverse, endpoint, mass and cost equations are provided in the theorem. [CI 42353729728](https://github.com/FlareZ123/bb6/actions/runs/42353729728). [ThreeResetWallPrefix.lean](ThreeResetWallPrefix.lean) excludes every genuine original-source three-positive-reset exact-wall precursor for `n>=14`, yielding the right-five floor `z>=5`, source [CI 42398746712](https://github.com/FlareZ123/bb6/actions/runs/42398746712). The speculative source wrapper [FourResetWallPrefix.lean](FourResetWallPrefix.lean) has **not** passed a full original-source CI (run [42439169870](https://github.com/FlareZ123/bb6/actions/runs/42439169870) failed); its separate arithmetic core has passed local Lean. Do not cite a source-certified six-reset floor based on that wrapper.

**Stronger later result by Agent50.** The genuinely source-certified all-count theorem in [WallLogSourceCorollaries.lean](../agent50-p1-subwall/WallLogSourceCorollaries.lean), [CI 42520350507](https://github.com/FlareZ123/bb6/actions/runs/42520350507), proves for every right-five original history and every `n>=14`:

```
n < 3*z+2*Nat.log2(n)+11.
```

This has no cost or history-length cutoff and asymptotically dominates any fixed reset floor. Its underlying source theorem prohibits the exact or near shifted wall unless `2^n<32*(2*n+7+(2*n+3)*z)*8^z`. It is still a necessary reset-density restriction and leaves arbitrarily many resets open.

## Original-source certified infinite word exclusion: one shallow edge between depth-two runs

The complete new mathematical note is [TwoRunWallExclusion.md](TwoRunWallExclusion.md). It derives an affine invariant for the exact original-source **depth-two scalar equations**:

```
P=2^n, W=b+4m+4n+20, B=m+n+6
8 W' = W+84P+16B,  B'=B+3
I=49W-588P-112B+384,    I_before=8*I_after.
```

For every `n>=14` and all nonnegative lengths `s,r`, the exact shifted wall is impossible for the original-source legal inverse-depth words `(2)^s (0|1) (2)^r` from the critical root. The proof is source-certified through [SourceOneShallowLift.lean](SourceOneShallowLift.lean), original-source [successful CI 42530146731](https://github.com/FlareZ123/bb6/actions/runs/42530146731). The precise `q,p,d` divisibility premises, both exact natural equations and complete proof are in [OneShallowFiniteBridge.lean](OneShallowFiniteBridge.lean). The stronger root-only model theorems [no_scalar_zero_word_wall_from_root](OneShallowModelBridge.lean) and [no_scalar_one_word_wall_from_root](OneShallowModelOne.lean) formally derive the dyadic quotient conditions from [RootTwoDivisor.lean](RootTwoDivisor.lean) and need only an exact initial two-run, the corresponding shallow scalar step, an exact final two-run, and the wall endpoint. Every link was locally compiled with Lean4.36.0-rc2; public theorem audits contain only ordinary axioms, no `sorryAx`. The proof uses a symbolic cubic gap for `n>=28` ([OneShallowLarge.lean](OneShallowLarge.lean)) and a fully kernel-decided finite scan for `14<=n<=27` ([OneShallowFinite.lean](OneShallowFinite.lean)). The direct-root single-shallow special case has separate unbounded-run proofs in [TwoRunBridge.lean](TwoRunBridge.lean).

**Source integration and scope:** [SourceOneShallowLift.lean](SourceOneShallowLift.lean) constructs `SourceTwoChain` from actual unchanged-source `inverseAt` steps with exact legal side conditions (`b>=8`, `b%4=0`, odd right counter and output, `k>=2`). It proves conservation of the original root mass, transfers every depth-two step using the [original two-step cocycle](../agent50-p1-subwall/RightFiveEnergyStep.lean), derives the exact depth-zero/one equations from [original inverse characterization](../agent1-p1-quarter/InverseIff.lean), then invokes the model wall contradictions. Theorems `BB6.Agent43SourceWord.source_no_zero_word_wall` and `source_no_one_word_wall` compiled with original sources in [CI 42530146731](https://github.com/FlareZ123/bb6/actions/runs/42530146731), each with axiom list `[propext, Classical.choice, Quot.sound]` and **no `sorryAx`**. A separate `CountCone` membership/word-shape characterization remains optional formal integration; the theorem itself already uses true `inverseAt` at every edge. This is an infinite legal-word restriction, not a blank-root P1 decision or an established externally novel publishable result. Keep it under `im-results/`.

## Original-source certified two-shallow exclusion for every n>=14

[SourceOneShallowLift.lean](SourceOneShallowLift.lean) proves
`BB6.Agent43SourceWord.source_no_two_shallow_word_wall_all`:
for every **n>=14** and every legal unchanged-source `inverseAt` inverse-depth word
`(2)^s (0|1) (2)^u (0|1) (2)^r` from the authentic critical source seed,
there is no endpoint on the exact shifted wall
`b+4*m+4*n+20=12*2^n`. All three run lengths are unbounded, all four
shallow-type combinations are covered, and every step carries its original
parity, left-counter and target bounds. The complete source dependency chain
compiled in [CI 42539116808](https://github.com/FlareZ123/bb6/actions/runs/42539116808);
the terminal theorem's `#print axioms` gives
`[propext, Classical.choice, Quot.sound]` without `sorryAx`.
The previous `source_no_two_shallow_word_wall_large` remains as a compatibility
corollary for n>=48.

The proof combines [TwoLayerRemainder.lean](TwoLayerRemainder.lean),
[TwoShallowNumeric.lean](TwoShallowNumeric.lean), and
[TwoShallowModelLarge.lean](TwoShallowModelLarge.lean) for n>=48, where
successive positive dyadic remainders yield a cubic separation contradiction.
For the previously unresolved **14<=n<48**, the root divisor theorem and
[SmallIndexEnergyCutoff.lean](SmallIndexEnergyCutoff.lean) force s<=3.
[TwoShallowIntegerAlgebra.lean](TwoShallowIntegerAlgebra.lean) derives the
first shallow-energy numerator directly from the terminal equation.
[TwoShallowFiniteBridge.lean](TwoShallowFiniteBridge.lean) uses the
[exact finite congruence tables](TwoShallowFiniteBounds.lean) to prove that a
middle depth-two run has u<=2 and the final run has r<=2; the terminal
numerical equation then contradicts the finite no-hit certificate.
All steps are Lean checked with original source imports in the same CI run.

This is a **restricted infinite inverse-word theorem**. Arbitrary words with
three or more shallow transitions, depth>=3 excursions, exceptional exits,
and the authentic blank-root halting decision remain open. Source verification
does not establish external novelty or a publishable resolution of BB(6).

## Original-source three-shallow exclusion for every n>=14

[SourceOneShallowLift.lean](SourceOneShallowLift.lean) now proves
`BB6.Agent43SourceWord.source_no_three_shallow_word_wall_all`.
For every original legal `inverseAt` word
`(2)^s (0|1) (2)^u (0|1) (2)^v (0|1) (2)^r`
from the critical P1 source seed, with n>=14, all four depth-two run
lengths unrestricted and all eight shallow type choices, the exact wall
`b+4*m+4*n+20=12*2^n` is unreachable. Each original inverse step has
the source-defined left-counter, parity, target, and mass requirements.

The complete original-source import chain and the final theorem compiled
under Lean 4.36.0-rc2 in [successful manual CI 42544621231](https://github.com/FlareZ123/bb6/actions/runs/42544621231).
The terminal theorem reports axioms `[propext, Classical.choice, Quot.sound]`,
with no `sorryAx`. The source theorem relies on [ThreeShallowSourceModel.lean](ThreeShallowSourceModel.lean),
which converts four source-compatible depth-two runs and three shallow
source cocycles into the already-certified all-index scalar contradiction.
[ThreeShallowAbstractBridge.lean](ThreeShallowAbstractBridge.lean)
performs the energy-to-numeric algebra; [ThreeShallowAllNumeric.lean](ThreeShallowAllNumeric.lean)
establishes the global arithmetic obstruction using an n>=58
quartic remainder bound and kernel-checked n14..57 certificates.
The complete derivation and quantified assumptions are in
[ThreeShallowAllIndex.md](ThreeShallowAllIndex.md).

**Unified low-depth necessary condition.**
[SourceLowDepth.lean](SourceLowDepth.lean) defines a stepwise, original-`inverseAt`
`SourceLowTrace` that records every legal inverse edge of depth 0, 1, or 2,
including the source parity and left-bound tests, and counts all shallow
(depth-0/1) edges. It proves the public theorem
`BB6.Agent43SourceWord.source_low_trace_wall_needs_four_shallows`:
**any such finite history from the critical seed that ends on the shifted
wall must contain at least four shallow steps**, regardless of the number
and order of depth-two transitions. The theorem is proved by a genuine
stepwise-to-block normal-form induction, the original-source 0/1/2/3-shallow
exclusions, and a separate pure-depth-two energy-sign contradiction.
[Original-source CI 42546553574](https://github.com/FlareZ123/bb6/actions/runs/42546553574)
completed successfully with terminal axioms
`[propext, Classical.choice, Quot.sound]`, no `sorryAx`.
[SourceOneShallowLift.lean](SourceOneShallowLift.lean) now exposes
`source_two_chain_model` as a public genuine-source transport theorem
for this and subsequent source trace proofs.

**Scope:** This is an unbounded-length exclusion of one explicitly restricted
original-machine inverse language. Words with four or more shallow steps,
any depth>=3 step, exceptional inverse exits and unrestricted authentic
blank-root reachability remain open. It does not determine P1 halting or
the exact BB(6) score, and has not been qualified as externally publishable.

## Four-shallow original-source exclusion for every n>=14

[FourShallowAllIndex.md](FourShallowAllIndex.md) gives the all-index
**four-layer scalar energy barrier**: four depth-0/1 transitions separated
by arbitrary depth-two runs cannot satisfy the exact shifted-wall equation
for any critical index n>=76. The decisive large-index gap is

```
21,120,000,000,000 * (n+2)^5 < 2^n,  n>=76.
```

The remaining finite interval **14<=n<=75** is now closed by the exact
finite bridge in [FourShallowFiniteBounds.lean](FourShallowFiniteBounds.lean),
[FourShallowIntegerAlgebra.lean](FourShallowIntegerAlgebra.lean), and
[FourShallowFiniteBridge.lean](FourShallowFiniteBridge.lean). The root
two-prefix divisor gives s<=3; the finite overflow certificates bound all
four intervening/tail depth-two lengths by 2, after which the exact
terminal natural equation is decided over the complete finite domain.
[FourShallowAbstractBridge.lean](FourShallowAbstractBridge.lean) joins this
small-index certificate to the general n>=76 barrier.

[FourShallowSourceModel.lean](FourShallowSourceModel.lean) transports the
four affine source profiles and five unchanged-source depth-two runs into
the scalar identity. [FourShallowSourceLift.lean](FourShallowSourceLift.lean)
then proves, for **every n>=14**:

- `source_low_word_four_no_wall`: no genuine `SourceLowWord` with exactly
  four depth-0/1 edges reaches the shifted wall;
- `source_low_trace_wall_needs_five_shallows`: every finite legal
  `SourceLowTrace` over depths 0, 1 and 2 that reaches the shifted wall
  has at least five shallow edges.

The proof uses the original unchanged-source `inverseAt` relations,
exact parity/left-counter conditions, source mass propagation, and the
stepwise-to-block normal form. The finite tables are kernel-decided, not
floating-point or bounded simulator evidence. All source/scalar dependencies,
finite tables, abstract bridge, source model, source lift, and theorem-axiom
audit passed Lean 4.36.0-rc2 in
[targeted original-source CI 43294753016](https://github.com/FlareZ123/bb6/actions/runs/43294753016).
The public theorem audits contain no `sorryAx`.

**Scope:** This excludes exactly four shallow edges and all smaller
depth-0/1/2 traces for n>=14. It does not exclude five-or-more shallow
histories, depth>=3 excursions, exceptional inverse exits, or unrestricted
blank-root reachability. This is not a P1 blank-root decision or a BB(6)
solution; it remains an intermediate research theorem pending independent
mathematical review.

## Five-shallow scalar barrier proved; original-source lift under CI

[FiveLayerBarrier.md](FiveLayerBarrier.md) gives a conditional five-layer scalar obstruction for \(n\ge83\). It exploits the exact profile correlation \((L,O)=(84,232)\) or \((56,136)\), and the quotient-halving fact \(2d_i\le S_i\), obtaining accumulated remainders \(168X,252X,294X,315X,326X\), sixth-power constant \(19,172,403,734,400\), and terminal upper bound \(73,024X^2\), where \(X=n+2\). The scalar theorem `five_layer_abstract_barrier` is now kernel-checked: [Lean CI 43295285993](https://github.com/FlareZ123/bb6/actions/runs/43295285993) compiled `FiveLayerGap.lean`, `FiveLayerBarrier.lean`, `FiveShallowProfileBounds.lean`, and `FiveShallowIntegerAlgebra.lean\). Its `#print axioms` list is `[propext, Classical.choice, Quot.sound]`, with no `sorryAx`.

The source connection is now certified in [PR #62](https://github.com/FlareZ123/bb6/pull/62): `FiveShallowAbstractBridge.lean` composes five source cocycles; `FiveShallowSourceModel.lean` transports five genuine source profiles across six original `TwoRun` segments; and `FiveShallowSourceLift.lean` reconstructs them from legal `inverseAt` edges. The earlier integrated runs [43296490015](https://github.com/FlareZ123/bb6/actions/runs/43296490015) and [43297949566](https://github.com/FlareZ123/bb6/actions/runs/43297949566) exposed two proof-engineering issues: an omitted explicit positivity proof for 8^s and an association mismatch in the fifth coefficient product. PR #62 fixes both without changing hypotheses or constants. The clean dedicated run [43299542235](https://github.com/FlareZ123/bb6/actions/runs/43299542235) passed the full source pipeline, including the final source lift and theorem-axiom audit. The resulting theorem source_low_trace_wall_needs_six_shallows proves that a depth-0/1/2 trace reaching the shifted wall for \(n\ge83\) has at least six shallow edges. This still does not decide unrestricted P1 halting.

## Finite right-five search and remaining frontier

[Right-five endpoint enumeration](right_five_finite_search.md) and its [exact search script](right_five_finite_search.py) use source `inverseAt_iff_power_mass` equations and a strictly decreasing two-counter mass to exhaust each fixed-`n` inverse tree when no state cap is reached. Completed runs found no right-five hit for `n=14..1612` and `n=1616..2620`; `n=1614` and `n=2622` remained incomplete at their state limits. These are finite computational observations only.

A reproducible [two-shallow scalar-model scan](two_shallow_model_scan.py), independently run for every n=14..4000, tested 6,708 integral scalar transitions through words of form `2^s(0|1)2^u(0|1)2^r` and encountered no exact-wall hit. This is bounded numerical evidence, not an all-n theorem or an original-source audit. The all-n two-shallow theorem closes that exact two-shallow grammar, including the formerly open n14..47 sector. The three-shallow equation and its authentic original-source lift are certified at every n>=14. The four-shallow source trace is now excluded for every n>=14, so any low-depth trace reaching the wall must have at least five shallow edges. The six-shallow source theorem now applies for n>=83. Five-shallow traces remain source-unresolved for 14<=n<=82; six-or-more shallow histories for n>=83 and unrestricted high-depth excursions also remain open. The true blank-origin path, exceptional exits and any global six-state maximum certificate remain unresolved. Broader proof history and superseded paper variants are preserved in [FULL_RESEARCH_LOG.md](FULL_RESEARCH_LOG.md).


## Next finite extension: n=14..82 six-shallow exclusion

The remaining low-index gap is now precisely the five-shallow source case for
14<=n<=82. A finite bridge can reuse the first four overflow predicates
(firstOverflow through fourthOverflow), extending their exact false tables
from n<=75 through n<=82, and add a fifthOverflow predicate for the terminal
depth-two run after the fifth shallow edge.

After the root divisor gives s<=3 and the five profile bits t1..t5 lie in
{0,1}, the bounded residual core with u,v,w,x,r<=2 has
69*4*32*243 = 2,146,176 assignments. The fifth-overflow table has
69*4*81*32 = 715,392 assignments. Split these tables into four-index n
blocks (at most 124,416 residual-core cases and 165,888 fifth-overflow cases
per block) rather than one monolithic decide proof. The first four overflow
tables also need the seven additional indices 76<=n<=82.

An exact BigInt reconnaissance scan is preserved in
[five_shallow_finite_scan.js](five_shallow_finite_scan.js). It checks all
**699,840 root-compatible bounded assignments** (90 admissible (n,s) pairs,
32 profile masks, and 3^5 run-length tuples) and finds zero solutions to the
five-layer natural equation. The scan deliberately omits additional
source-time inequalities and allows zero remainders, so it checks a superset
of the admissible source cases. This is useful experimental evidence for the
finite bridge, but it is not a kernel proof and does not establish the
run-length bounds u,v,w,x,r<=2.

This is a proof-construction plan, not an established finite result. The
source theorem remains at least five shallow edges for 14<=n<=82 until the
new fifth-overflow and residual finite certificates are completed.
