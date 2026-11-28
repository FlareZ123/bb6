# F321 odd-depth base-four gate exclusion

A new original source-counter all-length obstruction for the F321 terminal
parameters
`d = (40·4^t−7)/3 + 32·4^t·u` for all odd `t≥1`, `u≥0`.
The parametric Lean theorem `BB6.Agent2F321OddDepth.odd_depth_gate_never`
uses the exact existing `SourceCounter.CounterMove` transition relation
and works for **all forward lengths**, not a sampled trace.

- [Full self-contained proof and scope](../../results/2026-11-28-f321-odd-depth-base-four-rays-agent2.md)
- [Lean 4.36.0-rc2 source-counter certificate](OddDepthSource.lean)
- [Independent BigInt inverse-checker](verify.cjs): `node im-results/agent2-f321-odd-depth/verify.cjs 101`
- [Successful original-source-counter CI 46118063802](https://github.com/FlareZ123/bb6/actions/runs/46118063802), standard axioms only, no `sorryAx`

The disjoint union with Agent31's previous explicit 33/40 families has exact
density **5/6**. This is **not** F321 nonhalting, original six-state full
coverage, or a Raw132/BB(6) decision.

For next work, investigate the still-live inverse trees in the complement:
`d≡5 (mod8)`, and among `d≡3 (mod8)`, initial digit-2 runs ending in
digit 1 at even depth or digit 3 at odd depth. The density-one sieve already
gives much broader asymptotic coverage, so only pursue stronger structural
families if they help exclude a root-specific remaining orbit rather than
accumulating isolated congruences.
