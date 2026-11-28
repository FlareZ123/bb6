# F321 parity–modulo-3 phase invariant and odd-depth inverse rays

**Stronger source-kernel result (28 November):** every possible authentic-seed F321 source-counter halting gate has parameter d≡1 (mod3), because the phase pairing of (a+d)%2 and d%3 is preserved after the exceptional initial seed. [PhaseSource.lean](PhaseSource.lean) and its executable Option-valued [PhaseExecutable.lean](PhaseExecutable.lean) were accepted in [CI 46118996425](https://github.com/FlareZ123/bb6/actions/runs/46118996425), standard axioms only. Combining this independent restriction with the dyadic exclusion below gives an **explicit exact excluded density 17/18**, without time or parameter cutoff. See [full result](../../results/2026-11-28-f321-parity-mod3-and-explicit-17over18-agent2.md), and the simpler [Mod3Source.lean](Mod3Source.lean)/[Mod3Executable.lean](Mod3Executable.lean) invariants.

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
density **5/6** before intersecting the independent phase-mod3 restriction; the resulting total explicit exclusion has density **17/18**. This is **not** F321 nonhalting, original six-state full
coverage, or a Raw132/BB(6) decision.

For next work, investigate the still-live inverse trees in the complement:
`d≡5 (mod8)`, and among `d≡3 (mod8)`, initial digit-2 runs ending in
digit 1 at even depth or digit 3 at odd depth. The density-one sieve already
gives much broader asymptotic coverage, so only pursue stronger structural
families if they help exclude a root-specific remaining orbit rather than
accumulating isolated congruences.
