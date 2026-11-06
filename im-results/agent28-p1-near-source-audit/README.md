# P1 near-exponent reset density: certified original-source audit

**Source status:** Agent 50's mathematical near-exponent theorem is now verified by [manual Lean 4.36.0-rc2 run 42151457473](https://github.com/FlareZ123/bb6/actions/runs/42151457473) and [job 127675429796](https://github.com/FlareZ123/bb6/actions/runs/42151457473/job/127675429796), success on head `b3e74e3508034c1f7baed697ca4ed6ffd01e370c`. Agent 28 prepared the independent [original-source audit workflow](../../.github/workflows/agent28-near-reset-source.yml). Agent 50 owns the original proof modules; the [primary mathematical dossier](../agent50-p1-reset-nearn/README.md) predates the verification. P1 halting and BB(6) remain open.

## Certified theorem

For every `n >= 14`, every authentic source `OddCone (14*2^n-2*n-16) 3 b d m` satisfying either `b=4*(m+n)` or `d=5`, some faithful original-source `CountCone` witness has a positive-depth inverse reset count `z` with:

```
n <= (2*z+2) * Nat.log2(4*n+5)
```

The final Lean theorem is `BB6.Agent50Near.source_critical_either_gate_reset_near`. Separate original-source theorems are `source_critical_wall_reset_near` and `source_critical_exceptional_reset_near`. Necessary reset counts include z>=4 at n=70, z>=11 at n=200, z>=42 at n=1024 and z>=146 at n=4096. These bounds do not construct reaching histories.

## Proof mechanism and trust boundary

Agent50's pure `Prefix` induction maintains a positive dyadic defect until the first crossing of `m+Nat.log2(4*n+5)>=n`. Each source-supported inverse step satisfies exact remainder cancellation, and both source-certified terminal inequalities force such a crossing. The abstract theorem had compiled locally; original-source transport was previously unverified.

This audit decoded the four original near-exponent modules from the existing hashed source archives, verified all four SHA-256 digests, and compiled unmodified `GParity`, `GInverse`, `PosEvenForm`, `P1FiniteInverse`, `MassInverse`, `OddConeMass`, `P1InverseLog`, `InverseIff`, the Agent28 odd-word/defect modules and Agent50 existing source bridge, exceptional terminal cost-gap modules, and finally `ExtendedBudget`, `NearSourceAlgebra`, `NearSourceBridge`, `NearExceptionalBridge`.

The successful CI logs include the four final `#print axioms` outputs. Each lists exactly `[propext, Classical.choice, Quot.sound]`, with no mocked source declarations, user axioms or `sorryAx`. The theorem has an authentic source bridge and an auditable proof chain.

## Remaining mathematical problem

Reset count `z` is unbounded in the original inverse-cone grammar. The necessary inequality is consistent with arbitrarily large z. It does not establish blank-tape reachability or exclude high-cost positive-even exits and other machine branches. The highest-value next step is a blank-root-sensitive restriction on all remaining reset histories. External literature-level novelty and the global six-state coverage proof remain unverified; this finding stays in `im-results/`.
