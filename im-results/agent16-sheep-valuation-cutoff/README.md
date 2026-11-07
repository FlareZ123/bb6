# Sheep generic power-parent valuation: sharpened all-time cutoffs

**Agent 16, 7 November 2026. Intermediate mathematical research.** This is a new, all-quantifier refinement of the source-valuation bound for generic incoming first-even returns into a power of two in the six-state Sheep holdout `1RB1LA_0LC0RC_1LE1RD_1RE1RC_1LF0LA_---1LE`. The arithmetic obstruction is locally Lean-kernel checked under Lean 4.36.0-rc2 with no admitted axioms. The original-source composition [`SheepSharpSource.lean`](SheepSharpSource.lean) is submitted for verification in [manual CI 42342521962](https://github.com/FlareZ123/bb6/actions/runs/42342521962). Its success or failure must be checked before describing that last bridge as source-certified. This result does **not** prove that the original blank orbit reaches or avoids any halting power, and does **not** decide BB(6).

## Exact theorem

For a legal even generic Sheep section input \(x=2^a v\), with \(a\ge1\) and odd \(v\ge5\), assume its first even return reaches \(2^j\) after exactly \(h\) hidden odd section returns. Define

\[
\begin{aligned}
A_3(h)&=30+2((h-15)\bmod 3)+5\left\lfloor(h-15)/3\right\rfloor,\\
A_5(h)&=168+2((h-100)\bmod 5)+8\left\lfloor(h-100)/5\right\rfloor.
\end{aligned}
\]

Here the first expression is used only for \(h\ge15\), the second only for \(h\ge100\). Then

\[
h\ge15 \Longrightarrow a<A_3(h),
\qquad
h\ge100 \Longrightarrow a<A_5(h).
\]

The second is stronger in its stated range. This improves Agent 17's previous uniform bound \(a\le2h+2\) [`UNIFORM-VALUATION.md`](../agent17-sheep-geometric-rays/UNIFORM-VALUATION.md). For instance, at \(h=100\) the previous upper bound was \(a\le202\); the new necessary upper bound is \(a\le167\). Its asymptotic cutoff slope is \(8/5\) rather than \(2\).

The signed residue theorem and both explicit gap inequalities are individually proven with no finite target-exponent or hidden-return cutoff. The new bound applies to all exponents \(j\), any generic odd part \(v\), and arbitrarily large \(h\). Agent 17's separately certified special-source exclusion eliminates the exceptional \(v=3\) branch for every power target.

## Proof

The generic first-even return equation, already derived from the actual source section dynamics, is

\[
2^{j+h+1}=3^h(2^{a+1}+1)v+K_h(a),
\qquad
K_h(a)=3^h(2a-3)+2^{h+1}.
\]

For \(a\ge3\), \(K_h(a)\) is odd. The right-hand side modulo \(M_a=2^{a+1}+1\) says \(2^{j+h+1}\equiv K_h(a)\pmod {M_a}\). Agent 40's all-natural, kernel-certified [signed-power residue gap](../agent40-sheep-third-preimages/ResidueGap.lean) rules this out as soon as \(1<K_h(a)<2^a\).

The Lean module [`SheepSharper.lean`](SheepSharper.lean) establishes two all-natural families of strict inequalities:

* \(K_h(a)<2^a\) for \(h=15+r+3q,\ a\ge30+2r+5q,\ 0\le r<3,\ q\ge0\).
* \(K_h(a)<2^a\) for \(h=100+r+5q,\ a\ge168+2r+8q,\ 0\le r<5,\ q\ge0\).

The first uses the induction \((h,a)\mapsto(h+3,a+5)\). The key inequality is \(27(2(a+5)-3)\le32(2a-3)\), valid for \(a\ge29\), with \(3^3=27\), \(2^5=32\). The second uses \((h,a)\mapsto(h+5,a+8)\), relying on \(243(2(a+8)-3)\le256(2a-3)\) for \(a\ge152\), with \(3^5=243\), \(2^8=256\). The initial cases \(h=15,16,17\) and \(h=100,101,102,103,104\) are exact kernel calculations. The separate monotonicity lemma \(K_h(a+1)=K_h(a)+2\cdot3^h\le2K_h(a)\) extends each grid certificate to every larger \(a\).

[`SheepPowerCutoff.lean`](SheepPowerCutoff.lean) imports Agent 40's unmodified `ResidueGap.lean`, proves the oddness of \(K_h(a)\), and establishes the universal power-equation exclusions `no_power_generic_three` and `no_power_generic_five`. [`SheepSharpSource.lean`](SheepSharpSource.lean) composes those exclusions with Agent 14's original-source `even_edge_to_algebra` and `generic_inverse_equation` and Agent 17's [unrestricted exceptional-source theorem](../agent17-sheep-geometric-rays/SpecialSourceNoPower.lean). The intended result `original_power_generic_cutoffs` classifies every actual even-source incoming power edge into a generic branch with both valuation cutoffs.

## Reproduction and verification boundary

The two stand-alone modules, using the exact existing `ResidueGap.lean` dependency, compiled locally with Lean 4.36.0-rc2. Printed axioms for `val_gap`, `val_gap_five`, `no_power_generic_three`, `no_power_generic_five`, and `generic_source_diophantine` contain only Lean's ordinary `propext`, `Quot.sound`, and, for modular arithmetic, `Classical.choice`. The code uses no `sorry`, `admit`, or `native_decide`.

The source-composition CI uses the existing manual [Agent 22 original Sheep workflow](../../.github/workflows/agent22-sheep-source-bridge.yml), against pinned Google DeepMind Cryptids revision `ced8f9f44f67a167d5ecc03e687b048c67926371`, rather than installing a duplicate workflow. That bridge is **not** independently verified by the local stand-alone compilation alone.

**Research boundary:** This reduces the inverse arithmetic search range at large \(h\), but the true blank-root orbit's reachability of power-of-two gates is unchanged. The result is kept in `im-results/` pending independent review and assessment of mathematical novelty. The next decisive target is a root-specific all-time invariant or exclusion that eliminates an entire surviving halting-gate class without repeated finite residue refinements.
