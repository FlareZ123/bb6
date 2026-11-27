# Three new complete Raw41 five-hole cylinders and a certified 153→150 canonical refinement

**Status:** Original-source Lean 4.36.0-rc2 kernel accepted, 27 November 2026. **Scope:** a partial six-state two-symbol Turing-machine family, not the exact value of BB(6).

## Mathematical statement

Let `WeightedBound B m` and `TNFQuotientCompatible p m` have the definitions in the repository's accepted weighted-TNF quotient framework. Three distinct five-hole partial machines have the following universally checked bounds:

| Canonical Raw41 child | Literal transition table | Checked bound | Open prefix leaves discharged |
|:--|:--|--:|--:|
| 088 | `1RB1LB_1RC1LC_0RD---_1LD1RA_------_------` | 41 | 10 finite-automaton certificates |
| 090 | `1RB1LB_1RC1RC_0RD---_1LD1RA_------_------` | 84 | 71 finite-automaton certificates |
| 123 | `1RB1RB_1RC0LC_0RD---_1LD1RA_------_------` | 64 | 54 finite-automaton certificates |

The Lean theorems `BB6.Agent47Raw41.Raw41New088_bound`, `Raw41New090_bound`, and `Raw41New123_bound` have, in each case, the form

```lean
(m : Machine) → TNFQuotientCompatible Raw41NewNNN_p m → WeightedBound B m
```

Each partial machine has precisely five undefined transition slots, so it represents **25⁵ = 9,765,625** concrete total machine tables under the 24 ordinary transition choices plus one halting choice. The three tables are disjoint by their fixed cells; jointly, they determine **29,296,875** distinct physical completions. The displayed bounds are universal upper bounds; *sharpness is not asserted*.

The three source-accepted bounds combine by `removeNewThree_sound` to give the stronger exact finite frontier statement

```lean
afterNewThree_count : afterNewThree.length = 150
afterNewThree_sound :
  ∀ m, TNFQuotientCompatible parent m →
    WeightedBound 84 m ∨
    ∃ e ∈ afterNewThree, TNFQuotientCompatible e.2 m
```

where `afterNewThree` is the original **153-element Raw41 canonical residual list** with these exactly three literal cylinders removed. Source-checked uniqueness lemmas show all three were present exactly once.

For the earlier **229-element** rooted quotient roster, Lean also proved

```lean
globalNewThree_count : globalNewThree.length = 226
globalNewThree_sound :
  ∀ m, compatible root m →
    WeightedBound 7014 m ∨
    ∃ e ∈ globalNewThree, TNFQuotientCompatible e.2 m
```

and `exact_at_target_newThree` turns accepted Covers of all 226 remaining representatives, together with the appropriate attained score, into an exact-BB6 theorem. **The hypotheses for these remaining representatives have not been discharged.** This local theorem is **not a reduction of the newer Canonical40 global frontier**, and is not a proof of the BB(6) upper bound.

## Proof mechanism

The proof uses the existing original-source trusted definitions, not a new unverified simulator: Agent47's two-step Raw41 parent partition produces the 153 canonical children, Agent19's exact canonical path enumerator classifies finite-prefix halts, last-holes, and unilateral shift cycles, and a finite-automaton nonhalting (FAR) witness discharges each remaining leaf of the three selected children.

All 24 canonical transition branches in each child are instantiated in the generated Lean source, and the original `canonicalCheck` and `canonicalSound` establish the universal weighted bound. The final union proof removes only cylinders matched by literal `sameTable`, transporting their quotient-compatible witnesses through `sameTable_sound` and monotonicity of weighted bounds. The 153→150 and 229→226 counts are independently computed by the Lean kernel.

The trusted proof outputs depend only on `propext`, `Classical.choice`, and `Quot.sound`. The compilation jobs explicitly exclude `sorryAx` and `native_decide`.

## Reproducible accepted source

| Source-accepted theorem | GitHub Actions kernel run |
|:--|:--|
| `Raw41New088_bound` | [46079654567](https://github.com/FlareZ123/bb6/actions/runs/46079654567) |
| `Raw41New090_bound` | [46079698523](https://github.com/FlareZ123/bb6/actions/runs/46079698523) |
| `Raw41New123_bound` | [46079658514](https://github.com/FlareZ123/bb6/actions/runs/46079658514) |
| `afterNewThree_sound`, counts, global conditional soundness | [46080020567](https://github.com/FlareZ123/bb6/actions/runs/46080020567) |

The specific exact source fixtures and proof generators are in `im-results/agent36-raw41/close_candidate.py` and the original `im-results/agent47-raw41-cut/gen_children.py`. Produced raw tree/FAR proof source: [child088](https://github.com/FlareZ123/bb6/actions/runs/46079291525), [child090](https://github.com/FlareZ123/bb6/actions/runs/46079609608), [child123](https://github.com/FlareZ123/bb6/actions/runs/46079446203). The checked joint theorem is tracked in `im-results/agent36-raw41/Raw41NewThreeGraft.lean`, and the exact three-way source compiler is `.github/workflows/agent36-raw41-three-graft.yml`.

## Remaining problem

The Raw41 local family still has 150 canonical outstanding children under this particular three-cylinder subtraction; some additional children have independent prior proofs and can be merged separately. This statement is deliberately isolated from the later accepted global Canonical40 quotient. Closing the remaining locally or proving that they are already covered by stronger accepted parent theorems is a separate mathematical task, as is the actual universal six-state BB(6) upper bound.
