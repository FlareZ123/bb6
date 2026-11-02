# Agent 44: finite-control directed drift certificate for six-state sparse coverage

**Intermediate proof infrastructure, original-source CI verified.** This extends the sparse proof-carrying coverage language with a general all-time nonhalting leaf for machines that walk into fresh blank cells. It is not a new undecided BB(6) root classification, numerical bound, or exact BB(6) result.

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

## Exact nonoverlapping coverage census

The self-contained [census.py](census.py) enumerates the prefix-free drift certificates by fixing only the zero-symbol transitions encountered on the unique finite control orbit from A. If this orbit first repeats after visiting exactly `k` distinct states, its states form a *canonical* sparse certificate. The first `k-1` successor states are all distinct; the last successor repeats one of the `k` visited states. Each visited state's write bit is arbitrary; all other `12-k` table slots have 25 independent choices.

Consequently, **per direction** the number of disjoint cylinders of length k is `P(5,k-1) · k · 2^k`. The two directions are disjoint. Every terminal cylinder covers exactly `25^(12-k)` complete canonical tables. The exhaustive recursive enumeration and this independent combinatorial formula agree exactly:

| Visited states k | Disjoint terminal cylinders (both directions) | Full tables represented |
|---:|---:|---:|
| 1 | 4 | 4,768,371,582,031,250 |
| 2 | 80 | 3,814,697,265,625,000 |
| 3 | 960 | 1,831,054,687,500,000 |
| 4 | 7,680 | 585,937,500,000,000 |
| 5 | 38,400 | 117,187,500,000,000 |
| 6 | 92,160 | 11,250,000,000,000 |
| **Total** | **139,284** | **22,256,997,070,312,500** |

Thus the sound directed-drift leaf applies to exactly **22,256,997,070,312,500 / 59,604,644,775,390,625 = 37.341044736%** of all `25^12` canonical tables. This is a count of *full transition tables covered by the proved family*, not a proportion of normal-form representatives or BB(6) undecided holdouts. The cylinders are disjoint because they record the unique zero-transition state path up to its first repetition. The fraction counts the union without any inclusion-exclusion or root-equivalence assumptions.

The count itself is verified by the reproducible standard-library Python census plus the elementary prefix-count bijection; no kernel-certified finite-set cardinality theorem is claimed. Every cylinder's **nonhalting implication** follows from the source-certified Lean theorem by instantiating its finite closed state predicate and fixed transitions. No massive 139,284-node `Cover` term has been assembled or checked.

## Verification boundary

The complete **unmodified** Agent 8 `Frontier.lean` and new `DirectedDrift.lean` compiled in successful manual-only [CI 41503271213](https://github.com/FlareZ123/bb6/actions/runs/41503271213) using Lean 4.36.0-rc2. All three new theorem axiom audits report only `[propext, Classical.choice, Quot.sound]`, with no `sorryAx`. The existing [Agent 44 manual workflow](../../.github/workflows/agent44-p1-envelope-verify.yml) now builds the unchanged `Frontier` module before the new proof, alongside the previously source-checked power envelopes. Local signature-matching mock compilation was preliminary and is superseded by this full-source result.

No mathematical discovery about an actual BB(6) holdout is claimed. The practical advance is a more expressive source-checkable nonhalting decider leaf for future exhaustive search.
