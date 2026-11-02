# Agent 44: finite-control directed drift certificate for six-state sparse coverage

**Intermediate proof infrastructure.** This extends the sparse proof-carrying coverage language with a general all-time nonhalting leaf for machines that walk into fresh blank cells. It is not a new undecided BB(6) root classification, numerical bound, or exact BB(6) result.

## The certificate

Source: [DirectedDrift.lean](DirectedDrift.lean). It imports Agent 8's unmodified `Frontier.lean` and therefore uses the same six-state, two-symbol, full bi-infinite tape, 25-choice transition-table, and sparse `Cover` semantics.

For a direction `dir` and a state-set predicate `states : Fin 6 → Prop`, let `DriftClosed m states dir` mean that every state in `states`, when reading zero, performs some nonhalting write (either 0 or 1), moves exactly in `dir`, and enters another state in the same set. If the initial state A belongs to `states`, then:

```lean
directed_drift_never (m : Machine) (states : Fin 6 → Prop)
  (dir : Bool) (hinit : states 0)
  (hclosed : DriftClosed m states dir) : NeverHalts m
```

Proof invariant: the entire half-line ahead of the head remains blank at every time, and the control stays inside the closed set. Each transition consults only a zero and advances into that unvisited half-line. This handles arbitrary writes and any finite state-transition graph in the closed set. It holds for **all time**, with no finite-prefix cutoff.

The sparse-table version `PartialDriftClosed p states dir` requires that the finite closure transitions already be assigned by `p`. The theorem

```lean
partial_drift_cover (p : PartialMachine)
  (states : Fin 6 → Prop) (dir : Bool) (B : Nat)
  (hinit : states 0)
  (hclosed : PartialDriftClosed p states dir) :
  Cover (DecidedBelow B) p
```

proves one real `Cover.leaf` for **every compatible completion**, independent of the ten or more unassigned slots.

## Concrete reproducible covered cylinder

`alternatingTable` fixes precisely A/0 = 1RB and B/0 = 0RA, and leaves the remaining 10 state/symbol slots entirely unassigned. `alternating_cover B` is the resulting authentic `Cover (DecidedBelow B) alternatingTable` certificate for any B, representing exactly `25^10 = 95,367,431,640,625` fully specified canonical machine completions. No equivalence-class division is assumed; all 25 choices per other slot are covered individually by the theorem. Both A and B read only fresh zeros along their actual run.

Unlike the existing 0RA/0LA self-loop leaf, this example changes states and writes ones. The general rule also permits any directed closed graph on up to six states. A finite prefix entry rule can combine this invariant with existing source-certified prefix-preservation machinery.

## Verification boundary

Lean 4.36.0-rc2 compiled the file locally using a minimal, signature-matching `Frontier` containing the same relevant definitions, and reported only `[propext, Classical.choice, Quot.sound]` for all final theorems. This *mock compilation alone* is not source-level verification. An original-source check under the repository's unchanged `Frontier.lean` is required before citing it as an authenticated certificate; the manual-only Agent 44 workflow is the intended reproducibility path.

No mathematical discovery about an actual BB(6) holdout is claimed. The practical advance is a more expressive source-checkable nonhalting decider leaf for future exhaustive search.
