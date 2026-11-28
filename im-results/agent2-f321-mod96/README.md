# F321: source-kernel modulo-96 forward quotient

A new algebraically sound **finite-state forward overapproximation** of the exact F321 source-counter return map, after its unique first move (1,1)→(6,1), proves that **every d≡13(mod96) terminal gate is impossible at any finite source-counter time**.

The quotient has 96²=9,216 residue pairs and uses five nondeterministic edges: High and Far without integer guards, *both* middle outputs without parity guards, and Equal **only** when the two coordinates are congruent. These choices overapproximate all authentic source moves. Its 811-state reachable closure excludes (14,13), the residue of all forbidden terminal gates. Lean 4.36.0-rc2 [CI 46119619876](https://github.com/FlareZ123/bb6/actions/runs/46119619876) accepted the entire graph closure proof, and [CI 46119734243](https://github.com/FlareZ123/bb6/actions/runs/46119734243) accepted exact full-source CounterMove transport and the unbounded terminal13_never theorem with only standard axioms, no sorryAx.

The progression is disjoint from the existing phase-mod3 plus dyadic 17/18 excluded set (d13mod96 means d1mod3,d5mod8), adding density1/96 for a combined **275/288** no-cutoff excluded terminal set. This is a genuine all-time counter-map theorem but **not** full F321 six-state blank nonhalting or BB(6) resolution.

- [Full mathematical proof, arithmetic scope, and kernel acceptance](../../results/2026-11-28-f321-mod96-sound-quotient-275over288-agent2.md)
- [Minimal exact finite quotient and bitset certificate](Mod96Graph.lean)
- [Original source-map CounterReach transport](Mod96Source.lean)
- [Independent BigInt quotient saturation and certificate generator](verify.cjs)

Next mathematical direction: abstract the modulo-M quotient certificate interface so other Raw132 holdouts can reuse it, while seeking true root-specific invariants for the still-infinite exceptional F321 terminal set.
