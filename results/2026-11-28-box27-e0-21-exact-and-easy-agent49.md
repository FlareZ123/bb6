# Source-certified five-hole Raw10 Box27 subfamilies (Agent49)

**28 November 2026. Exact local maximum and a disjoint large finite classification.** This is a result about a bounded branch of Raw10, not a proof of the global BB(6) maximum.

## Exact weighted bound for E0=21

In the standard 25-code representation of a six-state two-symbol machine, slot order `A0,A1,...,F1`, consider

```
[8,?,11,?,13,13,14,17,21,?,?,?]
```

where all five question marks vary independently over codes 0–24. The resulting cylinder has exactly `25^5 = 9,765,625` complete tables. Every machine has **weighted halting score at most 108** (ordinary blank-start halting length, plus the source-defined incoming blank delay), or else it never halts. This is sharp: `[8,4,11,24,13,13,14,17,21,15,3,0]` halts after 107 live primitive steps, with zero incoming delay, scoring 108.

The original-source Lean 4.36.0-rc2 theorems `BB6.Agent49.Box27Slice.parent_bound`, `attainer_halts`, and `attainer_in_slice` were accepted in [CI 46091498528](https://github.com/FlareZ123/bb6/actions/runs/46091498528), dependency-closed proof artifact **15241468718** (`raw10-box27-slice`). The sharper theorem

```lean
BB6.Agent49.Box27Slice.exact_weighted (B : Nat) :
  (∀ m, compatible root m → WeightedBound B m) ↔ 108 ≤ B
```

passed original-source [CI 46092558221](https://github.com/FlareZ123/bb6/actions/runs/46092558221). This is exact within the entire five-hole physical cylinder, not just a sample or terminal-sequence calculation.

Proof: a deterministic first-hole tree branches on all 25 possible transitions at each unresolved query, with 101 checked finite halt leaves (mass 432,725), 1,959 source-checked side cycles (mass 9,321,375), 324 checked last-hole leaves (mass 8,100), and 41 source-checked two-sided finite-stack automata (mass 3,425). Total mass `9,765,625`; no residual. The largest automaton has 97 joint states. `im-results/agent49-raw10-box27/generate_slice.py` generates the certificate source, `Box27SliceCore.lean` checks each leaf, and `Box27SliceSource.lean` joins all child Covers, with no finite cutoff assumed as evidence of nonhalting. Original-source axiom audits reject `sorryAx` or `native_decide` as a proof premise.

## Twenty additional E0 values, 195,312,500 complete tables

Fix A0=8, B0=11, C0=C1=13, D0=14, D1=17 as above, and let E0 take any code in

```
{0,1,2,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20}.
```

For every such E0, leave A1,B1,E1,F0,F1 free. Each of these 20 cylinders has `25^5` completions, and all have `WeightedBound 108`. The source checker proves a finite halt or a one-sided repeating cycle before the five free transitions matter. `BB6.Agent49.Box27EasyE0.source_bound` and its 20 exhaustive checked witnesses passed [CI 46092810166](https://github.com/FlareZ123/bb6/actions/runs/46092810166). Reproduce from `im-results/agent49-raw10-box27/Box27EasyE0.lean`.

These 20 cylinders are pairwise disjoint, and disjoint from the E0=21 exact cylinder, so the two audited results jointly classify **21 × 25^5 = 205,078,125** complete tables in the D0=14,D1=17 section with **weighted upper bound 108**.

## Completion of all 25 E0 children, 244,140,625 complete tables

The four remaining E0 cases were independently checked in the same original six-state two-symbol machine semantics:

| E0 | Exact weighted maximum | Original-source Lean CI |
| ---: | ---: | --- |
| 3 | **141** | [46094172421](https://github.com/FlareZ123/bb6/actions/runs/46094172421), `Box27Slice03.exact_weighted` |
| 22 | **149** | [46113905945](https://github.com/FlareZ123/bb6/actions/runs/46113905945), `Box27Slice22.full_exact_weighted` |
| 23 | **143** | [46094175250](https://github.com/FlareZ123/bb6/actions/runs/46094175250), `Box27Slice23.exact_weighted` |
| 24 | **255** | [46094310742](https://github.com/FlareZ123/bb6/actions/runs/46094310742), `Box27Slice24.exact_weighted` |

The E0=24 attainer `[8,21,11,18,13,13,14,17,24,0,3,6]` makes 254 live moves with zero incoming blank delay. Because every complete table with these fixed D0=14,D1=17 transitions has exactly one E0 code, the 25 independently source-accepted children yield an exhaustive disjoint union of **25×25⁵=244,140,625 complete machines**. Every one has `WeightedBound 255`; this threshold is sharp because of that E0=24 attainer. The explicit one-theorem parent binder `Box27D17Parent.exact_weighted` remains a separate compilation/audit edge; the finite disjunction of accepted child results already establishes the mathematical classification.

### Exceptional E0=22: 25-completion nonhalting closure

The earlier E0=22 classification left exactly the partial table

```text
[8,24,11,8,13,13,14,17,22,15,4,?]
```

with F1 unrestricted. A concrete two-sided finite-stack automaton with **ten stack states on each side and a 306-element joint control relation** now proves all 25 completions nonhalting. Its certificate is `Box27ExceptionalFAR.lean`, generated deterministically by `generate_exceptional_far.py`; Lean checks `BB6.Agent4Automata.check` and the original-source table identity, then derives `BB6.Agent49.Box27Slice22.exceptional_never`. Unconditionally (no leftover exceptional hypothesis), `Box27Slice22.full_exact_weighted` establishes exact weighted 149 across its entire 9,765,625-table E0=22 cylinder. The original-source build and axiom audit both **passed** [CI 46113905945](https://github.com/FlareZ123/bb6/actions/runs/46113905945).

## Limits and next quantifier

The complete E0 partition is **only the fixed D0=14,D1=17 section** of original `raw10Remainder[27]!`. The other D0/D1 settings, other Raw10 boxes and the global canonical roster remain open. These local bounds do **not** determine the exact value of BB(6). Additional source-domain nonhalting cylinder proofs and an exact larger parent union are under active construction in `im-results/agent49-raw10-box27/`; their coverage percentages are not accepted mathematical claims until original-source Lean compilation and standard-axiom audits succeed.

All proofs use Lean's ordinary trusted logical axioms (propositional extensionality, quotient soundness, and classical choice where dependencies require it), with reproducible source and CI artifacts.
