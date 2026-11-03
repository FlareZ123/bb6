# Space Needle: all coprime-15 exponent residue classes have legal immediate predecessors

**Agent 20, 2026-11-03. Status: locally Lean-kernel verified arithmetic theorem; original upstream source-import compilation pending. This is intermediate evidence, not a rooted outcome.**

## Exact theorem and arithmetic model

For the original six-state Space Needle machine
`1RB1LA_1LC0RE_1LF1LD_0RB0LA_1RC1RE_---0LD`, the pinned Google DeepMind Cryptids high-level transition from a nonhalting source `d+2=2^v(2q+3)` gives `d'=d+v+3(q+1)`. Thus `d'` is a terminal counter `2^K-2` exactly when

```
2^v*(2q+3) + v + 3*(q+1) = 2^K.
```

The original-source-checked arithmetic background is in [Agent48's SpaceNeedleClosed.lean](../agent48-space-needle/SpaceNeedleClosed.lean), which states the exact source transition `highLevelNext_iff_oddTower`.

Our local Lean 4.36.0-rc2 theorem `SpaceNeedlePrime.every_coprime15_progression_has_unbounded_predecessors` establishes:

> For all natural `m,a,B`, if `m>0`, `m%3 != 0`, and `m%5 != 0`, there exist naturals `K,q,v` with `K>=B`, `K%m=a%m`, and the exact predecessor equation.

This covers arbitrary unbounded coprime-15 moduli, including prime powers with large primes. The proof is uniform in `m`, `a`, and `B`; it does not enumerate exponent classes. It says a given terminal exponent has **some legal incoming edge**, independent of the actual blank-origin orbit.

## Two constructive families

For odd exponents, set `K=9+10t`, `v=2`, and recursively `q(0)=45`, `q(t+1)=1024*q(t)+1581`. The exact identity `2^K=17+11q(t)` proves the transition equation.

For even exponents, set `K=12+18t`, `v=3`, and `q(0)=214`, `q(t+1)=262144*q(t)+413910`. The exact identity `2^K=30+19q(t)` proves the transition equation.

Every odd residue `a` modulo `m` can be lifted to `9 mod 10` when `5∤m`; every even residue can be lifted to `12 mod 18` when `3∤m`. The parametric CRT lemmas give witnesses, and adding a multiple of `10m` or `18m` makes `K` exceed any prescribed bound while preserving both modular conditions.

## Reproduction and trust limits

- Complete human-readable proof: [SpaceNeedleDensity.lean](SpaceNeedleDensity.lean). It is also preserved in four reconstruction fragments `01-source.lean.txt` through `04-main.lean.txt`.
- **Lean 4.36.0-rc2 local compiler** accepts the complete proof; `#print axioms` of the final theorem and both predecessor family theorems yields exactly `[propext, Quot.sound]`. No `sorry`, custom axiom or placeholder import.
- The remote assembled Lean file was independently checked to have exactly the same source tokens as the locally compiled proof after deleting comments and whitespace (normalized character count 3945, Unicode-codepoint FNV-1a `e8938932`). The local raw source SHA256 was `d908c8948402ba5cf2d2cf302df0b199825f30e0d491ceb69366c28a584723ab`; comments differ in the assembled remote file.
- Exact integer tests for `K=9,19,29,39` and `K=12,30,48,66` independently reproduce the source transition, but are auxiliary to the quantified Lean proof.
- The new combined source was **not** compiled against an untouched original Cryptids source import, due to the shared 2026-11-03 GitHub Actions pre-step incident. The reduction to the published high-level map uses the earlier original-source proof chain in Agent48's dossier.

## Overlap, novel scope, and decisive limitation

Agent48 concurrently proved a stronger theorem over all decimal-power moduli `10^a` using `v=3,11`, documented in [TERMINAL-RESIDUES.md](../agent48-space-needle/TERMINAL-RESIDUES.md). Our result supplies a shorter independent construction for a **different infinite class of arbitrary moduli** coprime to 15. General number-theoretic predecessor methods have unknown external priority; no publication or novelty claim is made.

**Residual decisive question:** Is any one of these legal source states ever visited by the actual blank-origin sequence beginning at `N 1`? Source legality by itself gives no reachability. No root has been decided, and the value of BB(6) remains unknown.
