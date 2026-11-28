# F321: a source-kernel-certified parity-aware finite quotient restricts all terminal gates to 15 classes modulo 384

**28 November 2026 — Agent 31. Main theorem (Lean 4.36.0-rc2, original counter-map relation).** Let `CounterReach 1 1 n a d` mean that the exact five-branch F321 source-counter return map has reached `(a,d)` from authentic source seed `(1,1)` after `n` live transitions. Then for every natural `d,n`,

```lean
BB6.Agent31F321Mod384.terminal_mod384_candidates (d n : Nat)
  (hr : BB6.Agent31F321Density.CounterReach 1 1 n (d+1) d) :
  d % 384 ∈ [37,61,115,133,139,157,181,211,229,235,253,277,325,331,349]
```

Consequently a fully explicit union of **369 residue classes modulo 384** cannot be the halting gate of the authentic F321 source-counter orbit at **any finite time**, with **no lower cutoff on d**. This set has natural density exactly `369/384 = 123/128 = 96.09375%`. Equivalently, every hypothetical reached terminal index belongs to just 15 residue classes (density `5/128`), not an assertion that any surviving class is reached.

**Rigorous status:** [manual GitHub Actions 46124258798](https://github.com/FlareZ123/bb6/actions/runs/46124258798) succeeded on commit `12776a5a17f5eeeb832c85143f54f1bb2a878d7d`; the proof statement above and the complete source transport were checked by Lean's kernel, with no `sorryAx` and `#print axioms terminal_mod384_candidates` yielding only `[propext, Classical.choice, Quot.sound]`. The theorem is about the exact published *counter map as restated locally*, not yet an imported original six-state tape-machine theorem, not a Raw132 parent Cover, and not the value of BB(6). The machine-to-counter bridge remains external.

## Sound mathematical reduction

The published F321 counter return map has the following nonhalting branches:

| Condition | Output |
| --- | --- |
| `a ≥ d+2` (high) | `(a−d−2, 2d+3)` |
| `a=d` (equal) | `(2a+4,1)` |
| `a<d`, `d≥3a+1` (far) | `(4a+6,d−3a)` |
| `a<d<3a+1`, `d−a` even (middle-even) | `(4a+6,2)` |
| `a<d<3a+1`, `d−a` odd (middle-odd) | `(4a+6,1)` |

The missing halt branch is precisely `a=d+1`. The only genuine first move is `(1,1)→(6,1)`. Reduce both counters modulo `M=384`; write the residues `(x,y)`. Define a deliberately *overapproximating* quotient relation with the following abstract edges:

```text
H  : (x,y) ↦ (x−y−2,2y+3)    [all residues]
F  : (x,y) ↦ (4x+6,y−3x)      [all residues]
M2 : (x,y) ↦ (4x+6,2)         [when x+y even]
M1 : (x,y) ↦ (4x+6,1)         [when x+y odd]
E  : (x,y) ↦ (2x+4,1)         [when x=y modulo 384]
```

All outputs are reduced modulo 384. High and Far drop their integer inequalities, and Equal's modular equality is necessary (but not sufficient) for the integer equality. Crucially, the parity of `d−a` equals that of `d+a`, and since 384 is even, `(x+y)%2=(a+d)%2`; thus retaining the **middle parity guard is sound**, unlike the earlier quotient allowing both middle outputs at each residue.

Starting from `(6,1)`, the reachable closure of these abstract edges has **7,414** of `384²=147,456` possible residue pairs. Its intersection with the terminal diagonal `(d+1,d)` consists of **exactly the 15 classes** in the theorem. The other 369 classes are excluded by soundness: any genuine counter run projects into the quotient closure after its first step. The exceptional original seed is handled separately and is not a halting gate.

The odd/even middle guard is the significant improvement: the previous [modulo-96 source-kernel quotient](2026-11-28-f321-mod96-sound-quotient-275over288-agent2.md) allowed both middle outputs at every residue. The new theorem excludes a larger full arithmetic set of hypothetical gates, at all depths; its complement density `5/128≈3.90625%` improves the previous explicit `13/288≈4.51389%` complement density. The exact sets should not simply be subtracted without checking containment; the comparison is in their standalone exclusion densities.

## Combining with the explicit inverse-ray families (paper density corollary)

The previously established *independent* inverse-ray theorem excludes parameters of the form `d=8k+3` whose base-four expansion of `k`, read from least significant digit, begins with any number `t` of digits `2` and then has **digit 0 at any t**, **digit 3 at even t**, or **digit 1 at odd t**; see the [33/40 theorem](2026-11-28-f321-70-percent-halt-ray-exclusion-agent31.md) and [odd-depth theorem](2026-11-28-f321-odd-depth-base-four-rays-agent2.md). These exclusions can be intersected with the new modulus-384 gate list to sharpen the explicit natural density of all-time forbidden parameters **from 123/128 to 1109/1152 = 96.26736…%**.

Indeed, of the fifteen allowed residue classes only five are `3 mod8`: `r=115,139,211,235,331`. Their corresponding `k=(r−3)/8` modulo `48` are `14,17,26,29,41`. Of these, only `k≡26 (mod48)` has its first **two** low base-four digits equal to `2,2`; `14` has `2,3`, and the other three begin with digit `1`. Thus only the `d≡211 (mod384)` class has a nontrivial intersection with these three infinite ray families. Conditioned on its fixed `2,2` prefix, the first subsequent non-`2` digit occurs with the following relative probabilities, obtained as convergent geometric sums of *disjoint* arithmetic progressions:

```text
[zero]  (any depth t≥2):     ∑_(j≥0) (1/4)^(j+1)       = 1/3
[three] (even t≥2):         ∑_(j≥0) (1/4)^(2j+1)      = 4/15
[one]   (odd t≥3):          ∑_(j≥0) (1/4)^(2j+2)      = 1/15
Total excluded fraction within d≡211(mod384) = 2/3.
```

The congruence `k≡26 (mod48)` additionally fixes a class modulo 3, but `3` is coprime to every power of `4`; hence the low higher base-four digits are still equidistributed conditional on this progression. Tail densities vanish by the common length-`j` digit-`2` prefix, giving a genuine natural density for the union. The additional excluded density is `(1/384)·(2/3) = 1/576`; total excluded density is

```text
123/128 + 1/576 = 1109/1152,
residual candidate density = 43/1152.
```

**Evidence distinction:** the parity-aware modulo-384 universal statement and Agent2's odd-depth ray theorem are Lean source-kernel accepted; the set-theoretic combination and exact density arithmetic in this section are paper derivations, not a new separately compiled Lean theorem. The remaining `43/1152` parameter density is only an upper bound on which hypothetical terminal indices may be reached, not a halting probability or resolution of the authentic orbit.

## Source-accepted certificate and reproducibility

The proof source is in [Mod384Graph.lean](../im-results/agent31-f321-mod384/Mod384Graph.lean) and [Mod384Source.lean](../im-results/agent31-f321-mod384/Mod384Source.lean).

- The graph embeds the **exact 147,456-bit set** in a `Nat` mask and kernel-checks every reachable node's five possible abstract successors, including the parity and equality guards, via `closed_graph : ∀ x y : Fin 384, ...`. It separately kernel-checks `seed_live`, `forbidden_gate_373`, and a complete gate-manifest theorem `gate_table_complete`. The graph closure's axiom list is `[propext]`.
- The source module imports the **literal** `BB6.Agent31F321Density.CounterMove` relation from `SourceCounter.lean`. Its `source_closed` case split verifies each real move is represented by an abstract edge and has axioms `[propext, Quot.sound]`. Its `source_reached_live_or_seed` transports closure over *arbitrarily many* genuine source moves, and `terminal_mod384_candidates` proves the universal theorem above with standard axioms only. The standalone illustrative `terminal373_never` also compiles with standard axioms only.
- The independent, zero-dependency [verify.cjs](../im-results/agent31-f321-mod384/verify.cjs), run as part of the same CI, recomputes the breadth-first fixed point, enumerates all 15 allowed diagonal indices, verifies the mask literal, and checks the exact 7,414/369 counts. It is a diagnostic; kernel-checked closure and source transport establish the theorem.
- The manual [CI workflow](../.github/workflows/agent31-f321-affine-terminal.yml), invoked with `mod384_only=true`, uses Lean 4.36.0-rc2. [Run 46124258798](https://github.com/FlareZ123/bb6/actions/runs/46124258798) finished successfully and the `sorryAx` gate passed.

## Research frontier

This is a stronger **no-cutoff, all-time counter-map restriction**, not a blank-start nonhalting decision: 15 infinite arithmetic progressions remain possible under the abstract graph. The separate [density-one backward modular sieve](2026-11-28-f321-density-one-bounded-inverse-exclusion-agent31.md) has a depth-dependent cutoff and gives a different, asymptotic quantification. Current scalable explorations at moduli 1,536 and 6,144 further shrink the candidate density but have not been accepted by a source-kernel checker. The decisive future problem is to eliminate every remaining possible terminal gate along the *authentic* root, compose the counter-map theorem with the pinned original tape-machine reduction, then discharge the Raw132/global Cover obligations. Merely increasing the modulus without a root-complete argument will not settle BB(6).
