# A source-checked 4063 bound for the Raw121 six-hole cylinder

## Theorem

Let
```
P = 1RB---_1RC---_0RD---_1LD1RE_---1RE_------
```
be the six-hole partial two-symbol Turing machine table used in the Raw121 dossier. In the repository's weighted first-write normal form, every total machine completion compatible with (P) satisfies the bound
```lean
theorem all121 : ∀ m, compatible p121 m → WeightedBound 4063 m
```
The theorem is implemented as `BB6.Agent11Raw121.all121` in `im-results/agent11-raw121/Raw121Data.lean`.

## Proof construction

The proof expands the parent into 24 first-hole child modules. The deterministic parent enumeration has 8,892 split nodes, 150,577 side-cycle leaves, 39,663 last-hole leaves, and 14,277 open leaves. The open leaves are completely partitioned into 14,156 FAR candidates, 71 one-block sweeps, 12 two-block sweeps, 14 nested quadratic recurrences, 6 recursive counters, 4 additional quadratic decompositions, 4 arbitrary-tail binary-fill families, 4 long affine candidates, 2 delayed first holes, and 4 exceptional symbolic-return families.

The FAR component uses 84 reusable finite return codes (83 occur in the selected witnesses). The non-FAR families use exact arbitrary-tail return invariants, recursive cost identities, delayed first-hole bounds, and original-machine nonhalting bridges. The 24 generated child modules are dependency-closed and checked against the original source definitions; no copied replacement semantics are used in the final parent theorem.

## Formal verification

Lean 4.36.0-rc2 CI run [45616647230](https://github.com/FlareZ123/bb6/actions/runs/45616647230) compiled six independent four-child shards, merged their dependency closures after source/object/provenance checks, and compiled the parent theorem from the union. The axiom audit accepted only `propext`, `Classical.choice`, and `Quot.sound`. The complete `raw121-parent-proof` artifact is attached to that run (artifact ID `15024725827`); the generated Lean sources and `parent-manifest.json` are committed under [`im-results/agent11-raw121/`](../im-results/agent11-raw121/README.md).

## Scope

This is a universal bound for one literal six-hole cylinder, not a bound for all six-state machines and not a determination of BB(6). The separate finite graft into the accepted canonical77 quotient roster was attempted in [workflow run 45621077513](https://github.com/FlareZ123/bb6/actions/runs/45621077513) and failed. This parent theorem is source-accepted, but no canonical roster reduction is accepted; a new shared-core consumer against the current canonical76 base must prove exact membership and pass source CI.
