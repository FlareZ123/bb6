# Raw45: 159 finite half-line recurrences and six unbounded-growth cylinders

**28 November 2026 — Agent 24. Original-source Lean 4.36.0-rc2 certified.**

## The theorem

Let (P) be the following partial six-state, two-symbol machine, with seven
undefined rows (where `---` is undefined and underscores separate states):

```text
1RB---_1RC---_0RD---_1LD1RB_------_------
```

Starting at the standard blank tape in state A, there exist **165 pairwise
disjoint partial refinements** of (P) such that **every total completion**
of each refinement runs forever:

- **Six** refinements with six undefined rows, proved by finite
  translated half-line recurrences.
- **153** refinements with five undefined rows, proved by finite
  translated half-line recurrences.
- **Six** more refinements with five undefined rows, proved by
  arbitrary-length growing-tape recurrences.

Each proof has an original-source Lean `NeverHalts` conclusion
quantified over *every compatible total six-state machine* (not merely
a particular chosen completion). All 165 source theorems passed the
repository's source compilation and axiom audit; their dependence
is restricted to the standard Lean logical axioms.

The refinements are disjoint by their unique first-missing-row branching
path. Their union therefore contains exactly

[
  6\cdot 25^6+159\cdot25^5
  = 1,464,843,750+1,552,734,375
  = \boxed{3,017,578,125}
]

distinct fully specified **physical transition tables**. In particular,
at least this many of the (25^7=6,103,515,625) total completions of
(P) are nonhalting. These are *literal physical-table counts*;
no claim that this is a count of distinct state-renaming quotient orbits
is intended. The arithmetic and disjointness are straightforward
combinatorial consequences of the exact first-hole paths; the Lean
proofs certify the nonhalting implications for each literal cylinder,
not a separately formalized cardinality theorem.

## First-hole classification

Start with the standard initial machine action `A0=1RB`. At each visited
undefined instruction, split on the twenty-four nonhalting write/move/next
actions and impose the usual new-state first-use cutoff where appropriate.
After two such splits, the classification yields:

| Category | Disjoint leaves | Missing rows | Mathematical outcome |
|---|---:|---:|---|
| Depth-one translated recurrences | 6 | 6 | Source-certified nonhalting |
| Depth-two translated recurrences | 153 | 5 | Source-certified nonhalting |
| Depth-two unbounded-growth recurrences | 6 | 5 | Source-certified nonhalting |
| Depth-two third-hole residuals | 137 | 5 | Not closed by this investigation |

There are 15 internal split nodes. An additional 44 candidate actions
were excluded by the first-use-state target convention; their handling
is **not** a substitute for a global canonical quotient completeness
theorem. The 159 finite recurrences enter after at most **26** genuine
blank-tape transitions and have positive periods of at most **24**
ordinary transitions. The main nonhalting proof uses source
`zipCycle_sound` after a checked `zipCycle` witness: it verifies
that the half-line is preserved under a head displacement and the
intermediate trajectory stays in that preserved region. It does not
extrapolate from a finite run.

## Six growing-tape sections

Below, the invariant uses source `Z0` configuration words. The **left**
word includes the scanned cell; both left and right lists implicitly
continue with blank zero cells. Every section has state D.

| Case | B1 | C1 | Blank entry | Left word in section `n` | Exact section-return cost |
|---|---|---|---:|---|---:|
| M1 | `0LD` | `0RC` | 3 | `0^(n+2) 1^(n+2)` | `2n+8` |
| M2 | `0RC` | `0RC` | 3 | `0^(2n+2) 11` | `4n+6` |
| M3 | `1LB` | `0LD` | 3 | `00 1^(3n+2)` | `12n+20` |
| M4 | `1LB` | `0RC` | 15 | `0^(3n+6) 1` | `6n+18` |
| M5 | `1LB` | `1RC` | 3 | `00 1^(3n+2)` | `6n+12` |
| M6 | `1RC` | `0RC` | 3 | `0^(n+2) 1^(n+2)` | `2n+6` |

In every section the right word is empty. Each positive-return
identity is proved *for every natural number* using the source-proved
arbitrary-length `sweepL` and `sweepR` lemmas and exact finite
primitive-step packet identities. The original blank run enters
section zero after the specified entry time; then
`never_of_growth` implies nonhalting for **all** total completions,
regardless of the five remaining unknown rows.

## Reproducible sources and certification runs

The 159 finite certificates are source `zipCycle` proofs:

- [Raw45Depth2CyclesA.lean](../im-results/agent24-raw45/Raw45Depth2CyclesA.lean), 40 cylinders, [source/axiom run 46093086108](https://github.com/FlareZ123/bb6/actions/runs/46093086108).
- [Raw45Depth2CyclesB.lean](../im-results/agent24-raw45/Raw45Depth2CyclesB.lean), 40 cylinders, [source/axiom run 46093089372](https://github.com/FlareZ123/bb6/actions/runs/46093089372).
- [Raw45Depth2CyclesC.lean](../im-results/agent24-raw45/Raw45Depth2CyclesC.lean), 40 cylinders, [source/axiom run 46093092483](https://github.com/FlareZ123/bb6/actions/runs/46093092483).
- [Raw45Depth2CyclesD.lean](../im-results/agent24-raw45/Raw45Depth2CyclesD.lean), 39 cylinders, [source/axiom run 46093096337](https://github.com/FlareZ123/bb6/actions/runs/46093096337).

The six unbounded recurrences are:

- [M1](../im-results/agent24-raw45/Raw45M1Growth.lean), [run 46092595373](https://github.com/FlareZ123/bb6/actions/runs/46092595373).
- [M2](../im-results/agent24-raw45/Raw45M2Growth.lean), [run 46090908764](https://github.com/FlareZ123/bb6/actions/runs/46090908764).
- [M3](../im-results/agent24-raw45/Raw45M3Growth.lean), [run 46093180605](https://github.com/FlareZ123/bb6/actions/runs/46093180605).
- [M4](../im-results/agent24-raw45/Raw45M4Growth.lean), [run 46092193834](https://github.com/FlareZ123/bb6/actions/runs/46092193834).
- [M5](../im-results/agent24-raw45/Raw45M5Growth.lean), [run 46093184038](https://github.com/FlareZ123/bb6/actions/runs/46093184038).
- [M6](../im-results/agent24-raw45/Raw45M6Growth.lean), [run 46090164582](https://github.com/FlareZ123/bb6/actions/runs/46090164582).

The existing manual [Lean source and axiom gate](../.github/workflows/agent38-m62-kernel.yml)
compiles exact original-source dependencies via the shared closure
tool rather than importing a precompiled external oracle. Source files
use no `sorry`, `admit`, or unsound fresh axioms.

## Limitations and next research obligations

This result **does not solve BB(6)** or discharge the entire seven-hole
Raw45 parent. The 137 ordinary depth-two residual cylinders are not
settled here and may include extremely long halting or nonhalting
behavior. In particular, the source proof of a complete *different*
five-hole child `1RB0LC_1RC0LA_0RD---_1LD1RB_------_------`
is being developed separately; it must not be conflated with
the 165 nonhalting refinements counted here.

For an eventual global consequence, a source-level certified
partition/normalization consumer must integrate this portfolio
with certificates for *all* remaining descendants, then
establish which global canonical parent orbits it removes.
The accepted global Canonical40 reduction still has 40 unresolved
representatives at this checkpoint.
