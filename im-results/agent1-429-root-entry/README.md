# Exact blank-root entry into the #429 J chart

This intermediate result closes the initial physical-entry gap for the
#429 source chart.

## Theorem

`JRootEntry.lean` proves, in the original twelve-slot #429 transition
table, that the blank A-root reaches the canonical `J(0,0)` physical
configuration after exactly **35 ordinary transitions**.

The endpoint has A at absolute head coordinate 3. Relative to that head,
its tape is one exactly on

[
[-6,1]\cup\{3\},
]

and blank elsewhere. Equivalently, the absolute marked cells are
`[-3,4] ∪ {6}`. This is the `jTape 0 0` configuration from
`BB429JPhysical.jMark`: for (u=w=0), the hole predicate is empty and
the mark interval is ([-6,1]), with the additional mark at (3).

The proof is a kernel-checked computation of the actual raw run, not an
inference from a sampled trajectory or from the high-level arithmetic map.

## Why it matters

The source chart's `J(0,0)` start is now connected directly to the genuine
blank tape in the repository's `BB6Coverage.run` semantics. Future
all-time chart/frontier arguments can use this theorem as their base case,
without assuming a prepared J configuration.

## What remains open

This theorem proves only the 35-step entry. It does **not** prove that the
subsequent J/Junc orbit stays inside a safe chart, that every later C/0
event is a new global head record, or that #429 never halts. The main
remaining task is the all-time physical frontier/history invariant across
the complete J/Junc transition family.

## Reproduction

The manual workflow `.github/workflows/agent1-429-root-entry.yml`
rebuilds the source dependency chain and compiles this theorem under Lean
4.36.0-rc2. The file prints its theorem axioms for the CI log; no
`sorryAx` is permitted.
