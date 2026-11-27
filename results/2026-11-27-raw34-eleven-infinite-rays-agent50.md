# Eleven source-certified infinite rays in the Raw34 eight-hole cylinder

**Status: unconditional original-source Lean theorem accepted.** This is a local nonhalting result, not the value or a global upper bound for BB(6).

## The result

Let the partial two-symbol six-state machine be

```
Raw34 = 1RB---_1RC---_0RD---_1LC---_------_------
```

with exactly four specified transitions, and let `Raw34[t]` fix its D1 slot to transition `t` (and leave the other seven slots unspecified). The following eleven distinct choices for `t` each force **nonhalting from a completely blank tape for every total completion**, with no time bound or assumption on the seven remaining instructions:

| D1 transition | Entry time | Period | Half-line direction | Retained boundary |
|---|---:|---:|---|---:|
| `0LA` | 0 | 6 | right | 0 |
| `0LB` | 1 | 5 | right | 1 |
| `0LC` | 2 | 4 | right | 2 |
| `0RA` | 0 | 6 | right | 0 |
| `0RB` | 1 | 5 | right | 1 |
| `0RC` | 2 | 4 | right | 2 |
| `0RD` | 3 | 3 | right | 2 |
| `1LC` | 4 | 2 | right | 2 |
| `1RA` | 0 | 6 | right | 0 |
| `1RB` | 1 | 5 | right | 1 |
| `1RC` | 2 | 4 | right | 2 |

More precisely, the original-source Lean theorem

```lean
BB6.Agent50Raw34Eleven.all_never :
  (w : Witness) → w ∈ witnesses →
  ∀ m : Machine, compatible (child w.move) m → NeverHalts m
```

holds for the exact eleven-element witness list, whose moves are pairwise distinct. The list covers `11 × 25^7 = 67,138,671,875` distinct total physical transition tables, because each child fixes five of the twelve two-symbol entries and each remaining entry has exactly 25 possible outcomes (24 ordinary moves or halt).

Each certificate is stronger than a long finite computation: `fastSideCycleCheck` verifies a finite blank-start trace of at most six steps to its return comparison and equality, after oriented translation, of the entire retained half-line. The already proved `fastSideCycleCheck_sound` transports this finite equality to arbitrarily many live executions despite arbitrary tape modifications behind the boundary. The result follows for **all compatible full machines**; no sampling or extrapolation is used in the theorem.

## Formal evidence and reproducibility

The original source is [Raw34ElevenSideCycles.lean](../im-results/agent50-raw34-firsthole/Raw34ElevenSideCycles.lean), importing the shared [SideCycle soundness library](../im-results/agent50-weighted-tnf-pilot/SideCycle.lean). The proof has three machine-checked data gates: eleven distinct moves, eleven finite certificates, and the universal nonhalting implication.

Original-source Lean **4.36.0-rc2** compiled all nine required project modules and passed the explicit standard-axiom allowlist in [successful CI run 46085109098](https://github.com/FlareZ123/bb6/actions/runs/46085109098), artifact [15238447811](https://github.com/FlareZ123/bb6/actions/runs/46085109098/artifacts/15238447811), zip SHA-256 `26dc4d77ed7adc2860da248d4191eaf86bbd79a3072c9bc1e7b6a749fe81cdb0`. Lean printed the dependencies for `all_never` as exactly `propext`, `Classical.choice`, `Quot.sound`; there is no `sorryAx` or `native_decide` in that theorem's axiom profile. The corresponding manual workflow selector is `raw34-sidecycle` in [Agent50 workflow](../.github/workflows/agent50-raw47-lifted.yml).

## Remaining frontier and scope

The Raw34 parent has eight unspecified slots and `25^8 = 152,587,890,625` total physical completions. This result settles **eleven of the 25 D1 outcomes**. A D1 halt is separately an immediate finite case, but its bound is not part of the theorem above. Nine D1 ordinary transitions to already introduced states A–E remain open; four transitions to state F are raw physical outcomes that can be handled via first-use state-renaming in a *separate* canonical quotient argument. Neither the remaining branches nor Raw34's exact membership/remainder graft into the accepted Canonical40 global proof chain is discharged by this result. No global residual count changes.

The next mathematically decisive problem is to cover the remaining D1 transitions (especially `1RD` with C1 choices that display expanding tape patterns) and build an exact Raw34 parent or a properly source-checked conditional subtree. Preserve the genuine full-machine proof obligation rather than counting aliases as physically impossible.
