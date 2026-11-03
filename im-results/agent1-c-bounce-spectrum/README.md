# Exact excluded mass-gain residue class for Machine C (Agent 1)

**Original-source Lean 4.36.0-rc2 verified, 2026-11-03 16:41 UTC. Intermediate all-input structural theorem.** Machine C itself remains undecided, and this theorem does not improve BB(6).

## Result

Let `F = BB6.Agent46.secNext`, the genuine deterministic first-return section map. If `k>0` and `F(a,k)=some(x,y)`, put `W(a,k)=a+2k` and `Δ=W(x,y)-W(a,k)`. Then, without a recursion-depth or input-size bound,

```
Δ ≥ 4
Δ % 6 ≠ 2 .
```

Equivalently **none** of the infinitely many increments `8+6r`, for `r≥0`, can occur on a successful positive-right section edge. Theorem [DeltaSpectrum.lean](DeltaSpectrum.lean) is the *direct original-source* arithmetic statement:

```lean
BB6.Agent46.section_no_gain_8_plus_6r
  (a k x y r : Nat)
  (hk : 0<k) (h : secNext (a,k)=some(x,y)) :
  x+2*y ≠ a+2*k+8+6*r
```

[DeltaSpectrumClass.lean](DeltaSpectrumClass.lean) proves the fully quantified modulo-six consequence, and provides an exhaustive **necessary** positive-gain superclass presentation. It does not assert that every permitted increment is attained.

## Proof decomposition

The source gives the complete zero-high section with the following cases:

1. Direct half-plane: `a≥2,k>0,2k≤a` has exact mass gain `4`, already certified in [ExactDeltaFour.lean](../agent1-forward-mass/ExactDeltaFour.lean).
2. High even-left bounce (`a≥2`, a even) has odd middle input `K=a-1`, where Agent3's authentic all-depth [BounceInverse.lean](../agent3-c-bounce-inverse/BounceInverse.lean) gives gain `7+3n`.
3. High odd-left bounce (`a≥3`, a odd) has even middle input and for returned `y≥4` gain `7+3n`, by the original even-middle cost theorem. Its special `y=3` exit has gain `5+3n` and a source-enforced even `n`, hence gain `5+6r`.
4. Low-left `a=0`, `k≥2` has odd-middle bounce gain `9+3n`; its `k=1` exception gains `6`.
5. Low-left `a=1`, `k≥4` has even-middle bounce with gain `10+3n` when `y≥4`; for exceptional `y=3`, the parity of the initial bounce height forces odd depth and gain `11+6r`. Its `k=1,2,3` exceptions gain `5,7,7`.

The nontrivial missing ingredient was the **unbounded-depth exceptional even-middle `y=3` branch**, where the original `BounceInverse` even-output theorem explicitly assumes `y≥4`. [EvenThree.lean](EvenThree.lean) proves for every successful even-middle bounce with `y=3`:

```
∃ n, c+2K+4+3n=x+6 ∧ (c+n)%2=0.
```

This all-depth cost-plus-parity law, plus the original existing `bounce_even_output_invariants`, `bounce_odd_output_invariants`, and `section_mass_four_if_right_positive`, removes the full `2(mod 6)` gain class after the exact exceptional section case split. The elementary `DeltaSpectrumClass` presentation is

```
Δ = 4 or Δ = 6 or
(∃ n, Δ = 5+6n) or
(∃ n, Δ = 7+3n) or
(∃ n, Δ = 9+3n).
```

This representation is a necessary superclass, not an iff for every individual source input.

## Verification and provenance

- [Original-source CI 41675999479](https://github.com/FlareZ123/bb6/actions/runs/41675999479), commit `bdc0e16d588a72326efb0eaef21676d45684e40c`, compiled the original Agent8/11/21/46 source chain, Agent3 original mass and bounce inverse proofs, and new [EvenThree.lean](EvenThree.lean)/[DeltaSpectrum.lean](DeltaSpectrum.lean). `section_no_gain_8_plus_6r` axiom audit: `[propext, Classical.choice, Quot.sound]`, no `sorryAx`.
- [Original-source CI 41676539730](https://github.com/FlareZ123/bb6/actions/runs/41676539730), commit `a9f17d5b58d537b8553c90264d8b3a86c84fb673`, also compiled [DeltaSpectrumClass.lean](DeltaSpectrumClass.lean). The `section_gain_mod6_ne_two` and `section_gain_possible_classes` axioms match the same standard foundational set.
- Existing manually triggered [agent1-c-mass-four.yml](../../.github/workflows/agent1-c-mass-four.yml) is the authoritative repeatable source integration; no new on-push workflow.

The source implements genuine section transitions over all `Nat` inputs, even ones unreachable from blank. Since Agent38's original-source theorem proves the **genuine blank-origin orbit always has `k>0`**, every defined transition along that orbit obeys the new forbidden-gain theorem. This is an unbounded structural restriction on **edges**, not an exclusion of an infinite terminal-state family; no claim about Machine C eventually halting follows from it. Its external novelty and possible relation to known return-map spectra have not been independently assessed.

## Research opportunities

A potential consequential next step is deriving a genuine-root invariant across the full sequence of variable permitted gains, combining this spectrum with Agent15's complete two-parameter Diophantine stopping locus. The current increment restriction alone does not prevent reaching any of those targets, and cannot be promoted to `results/` as a Machine C resolution.
