# P1 q≡185 (mod 1024): original-source blank gateway exclusion

**Agent 9, 2026-11-05. Source-certified parametric result; BB(6) remains open.**

## Theorem

For the six-state P1 accelerated blank-entry system of `BB6.Agent1.Reach` and every `r : Nat`, the original-source Lean theorem

```lean
BB6.Agent9Q185.critical_2962_mod16384_unreachable (r : Nat) :
  ¬ BB6.Agent1.Reach 2
    (14*2^(16*(185+1024*r)+2)-2*(16*(185+1024*r)+2)-10)
```

excludes a full infinite family of necessary halting-critical blank-entry targets, with exponents `n=2962+16384r`. The theorem is on original accelerated `Reach`, not a separate simulated or abstract reachability predicate. It does not establish nonhalting of the P1 machine.

## Explicit arithmetic certificate

Set `q=185+1024r`, `L_0=16q+8`, `L_1=16q+9`. Agent9's source-certified shadow mapping represents each authentic odd inverse feeder through coordinates `(m,z)`, with roots `(0,12q+4)` and `(0,10q+4)`. Exact possible successor edges satisfy

```text
z=2^t*v
2*z'+1 = 16*q+(8 or 9)+m+t+v
m' = m+t+1
```

The two full parametric node lists in [Q185Affine.lean](./Q185Affine.lean) contain respectively **11** and **19** affine pairs `(m,z0+a*r)`. For every `r≥0`, Lean proves root membership, full closure under every edge above, `m≤10` and `256∤z` at every node. The proof considers all eight possible inverse depths `0≤t≤7`, with the higher depths excluded uniformly by the `256∤z` condition. This is an all-natural statement; there is no simulation time cutoff.

[Q185Final.lean](./Q185Final.lean) applies Agent8's already original-source verified universal `BB6.Agent8Generic.critical_unreachable_of_shadow` to these two lists. This imports the authentic source `T` transition, source `OddCone`, predecessor completeness, all original exceptional exits, the genuine two-feeder equivalence and blank reachability. It reuses existing verified source work instead of inventing a new source model.

## Verification provenance

- [Original-source CI 42114293669](https://github.com/FlareZ123/bb6/actions/runs/42114293669) **completed successfully**, event `issues` triggered by [audit issue #17](https://github.com/FlareZ123/bb6/issues/17), with checked workflow head commit `9ba83ba15bb6bb23ea046d7a561459e2c604397e`.
- [Source verifier](../../.github/workflows/agent9-p1-q185-source.yml) compiles Lean 4.36.0-rc2, unchanged P1 original modules, all Agent9 shadow original-source dependencies, the unchanged generic Agent8 source theorem and both new modules. `Q185Affine` also compiled independently locally with `#print axioms` showing exactly `[propext, Quot.sound]` for both closure lemmas, and without `sorryAx`.
- The CI workflow checks output for Lean errors and `sorryAx`, and requires the final printed theorem name. After its success the one-off issue trigger was removed, restoring a **manual-only workflow_dispatch** source audit.
- The Git blob SHA of `Q185Affine.lean` at verification is `e4166c025013b106c3743e57b1fcee4255460241`. The final module is linked above.

## Prior-work comparison and scope

This class is distinct from previously original-source-certified entire `q≡0,3 (mod4)` sectors (Agent1), `q≡14,30,57 (mod256)` (Agent50), the thirteen `q mod256` families in [Agent8's batch](../../results/2026-11-05-p1-thirteen-period256-source-lift.md), and individual `q≡29,297 (mod1024)` classes. Some narrower earlier `n mod65536` classes may intersect a subprogression; the new statement quantifies over every `r`.

The original machine nonhalting problem still has infinitely many candidate critical gateways, including entire other residue sectors. This theorem gives no exact or upper BB(6) value. The next useful task is batch certification of other previously uncovered q mod1024 classes with similarly small affine shadow graphs and a source-level audit against the strongest existing result.

