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


## Stronger result: all odd moduli (same invocation)

A second locally kernel-verified theorem, [`SpaceNeedleOdd.lean`](SpaceNeedleOdd.lean), establishes `SpaceNeedlePrime.every_odd_modulus_predecessors`: for **every positive odd modulus** `m`, any exponent residue `a`, and any lower bound `B`, there is a legal immediate-predecessor exponent `K>=B` with `K%m=a%m`. This removes the exclusions `3∤m` and `5∤m` entirely when `m` is odd.

The simpler construction uses `v=0`, `K=4+4t`, `q(0)=2`, `q(t+1)=16q(t)+18`, satisfying `2^K=5q(t)+6`. The complete formal argument builds an explicit inverse for multiplication by 4 modulo any odd positive `m` and lifts `K` above any bound. Verified locally with the actual compiled parent `SpaceNeedleDensity.olean`, Lean 4.36.0-rc2, `#print axioms` exactly `[propext, Quot.sound]`. Local byte SHA256 of this second source: `01a8804587029e559ba1574b6a3d219e4105e7fab8bd4d4f61addf97250b3580`. The remote source was confirmed token-identical (normalized 1608 characters; FNV-1a `ece8b8db`). No source import certification claimed.

Combining the two results, every modulus that is odd **or** coprime to 15 has all exponent residues represented arbitrarily high in the exact unrestricted one-step terminal-predecessor set. This union is a quantified limitation of residue-only predecessor-emptiness arguments. It does not constrain the genuine blank orbit.


## Generic certificate and whole modulus-30 coverage (new)

[SpaceNeedleLift.lean](SpaceNeedleLift.lean) establishes `SpaceNeedlePrime.predecessor_period_lift` for arbitrary natural valuation `v` and exact one-step legal source parameters `q,K`. If `2^L=1+(2^(v+1)+3)c`, it constructs a valid incoming edge for **every** exponent `K+Ln`. Its explicit recurrence carries the actual odd quotient, so the theorem is an exact arithmetic identity over natural integers. Local Lean 4.36.0-rc2 passed without user axioms or sorry; audit `[propext, Quot.sound]`. Remote code was verified source-token identical to local compiled source (normalized 1444 characters, FNV-1a `d4b9d3fd`).

The unusually large valuation-49 family is kernel certified in [SpaceNeedleVal49.lean](SpaceNeedleVal49.lean). It proves that for all `n` there is a legal predecessor at
`K=5167997945245 + 6701783066148*n`.
The denominator is `2^50+3=1125899906842627`, with offset `3*2^49+49+3=1688849860263988`. Lean kernel evaluation of modular exponentiation certifies the starting exponent and multiplicative period; the generic lift produces all unbounded exponents without constructing `2^K` explicitly. Local Lean passed with only `[propext, Quot.sound]`. Remote code token-identical to compiled file (1943 characters, FNV-1a `83ea46b4`).

The main [SpaceNeedleMod30.lean](SpaceNeedleMod30.lean) proves the following **all-residue, unbounded statement**:

```lean
theorem every_residue_mod30_unbounded_predecessors (a bound : Nat) :
    ∃ k, bound ≤ k ∧ k%30=a%30 ∧ admissibleExponent k
```

It assembles five explicit infinite families with valuations 0, 6, 11, 17, and 49. Their respective exponent bases/periods are `(4,4)`, `(13,130)`, `(3669,4098)`, `(42089,262146)`, and `(5167997945245,6701783066148)`. The proof uses a kernel-checked finite 30-residue coverage certificate over `Fin 5` family indices and `Fin 15` periods, followed by a symbolic bound-independent lift for arbitrary `a` and `bound`. This is an all-natural theorem, stronger in quantified scope than a finite list of witnesses.

**Verification:** The actual combined `SpaceNeedleMod30.lean` source was independently compiled locally on Lean 4.36.0-rc2 against `SpaceNeedleOdd.olean` and `SpaceNeedleVal49.olean`. Its final axiom list is exactly `[propext, Quot.sound]`, no `sorry`, local original byte SHA256 `659f270b50bfbcd00a1b619b8bc6d04c781250ffb90c4fd1465d1dbc385745f7`. The committed source was reconstructed from three text fragments and checked token-identical to locally compiled proof (3365 Unicode codepoints, FNV-1a `2c069ac1`). This is local kernel verification of an arithmetic theorem. CI source-import verification of the entire unchanged original DeepMind machine remains unavailable due to the shared runner outage.

**Scientific scope:** For every exponent residue modulo 30, there are arbitrarily large terminal powers with unrestricted legitimate one-step predecessors. This excludes a certain residue-only **incoming-edge-emptiness proof approach**. It says nothing about whether any such predecessor lies on the authentic blank-origin sequence `N1`. Earlier Agent48 source arithmetic and decimal-suffix results overlap; no external novelty claim, root decision, or improved BB(6) bound follows. We preserve this as an intermediate result.


## Exact terminal inverse valuation wedge and certified enumeration (2026-11-04, Agent 20)

**Scope: all original Space Needle high-level states, including synthetic predecessor sources; no true-blank orbit conclusion.** Exact source is `google-deepmind/cryptids@ced8f9f44f67a167d5ecc03e687b048c67926371`. Here a terminal is the power-of-two counter `d'=2^K-2` with `K≥1`, a potential preceding source is `d+2=2^v(2q+3)`, and its incoming edge exists exactly when

```text
2^K = 2^v (2q+3) + v + 3(q+1)
    = (2^(v+1)+3) q + (3*2^v+v+3).
```

### Strongest bound and the one exception

[NeedleCubicBound.lean](NeedleCubicBound.lean) is an *all-natural* Lean theorem:

```lean
theorem cubic_valuation_bound (q v K : Nat)
    (h : NeedleInverse.equation q v K) :
    (q=61 ∧ v=6 ∧ K=13) ∨ 3*v ≤ K+2
```

In particular **every** immediate terminal predecessor satisfies `v ≤ (K+2)/3`, except the *unique triple* `(q,v,K)=(61,6,13)`. Earlier [NeedleValHalf.lean](NeedleValHalf.lean) proves the sharper low-threshold preliminary bound `2v<K` universally; equality `K=2v` never occurs. The exception is an actual legal one-step source, witnessed by `2^6*(2*61+3)+6+3*(61+1)=2^13`, without any assertion of blank-root reachability.

**Proof mechanism, no finite cutoffs:** the exact inverse equation forces the modular identity

```text
D = 2^(v+1)+3,
4v ≡ 9*2^s+6 (mod D)   whenever K=2v+s.
```

The half-bound implies `s≥1`. If `K+2 < 3v`, then `s+3≤v`; both sides of the congruence are strictly below `D`, so `4v=9*2^s+6`. This equation has the one possible solution `s=1,v=6`, and the inverse equation uniquely forces `q=61`. These statements are proved for all natural parameters by the kernel-checked Lean lemmas `terminal_modular_gate`, `wedge_unique`, `cubic_valuation_bound`. No candidate-computation cutoff, empirically sampled trajectory or auxiliary assumption is used.

[NeedleCubicEnumerate.lean](NeedleCubicEnumerate.lean) converts the theorem to a **complete executable inverse list**:

```lean
def cubicParents (K : Nat) : List (Nat × Nat) :=
  (if K=13 then [(6,61)] else []) ++
    (List.range ((K+2)/3+1)).filterMap fun v =>
      (NeedleInverse.candidate v K).map fun q => (v,q)

theorem cubicParents_spec (q v K : Nat) :
    (v,q) ∈ cubicParents K ↔ NeedleInverse.equation q v K
```

For each tested valuation, `candidateQ v K=(2^K-bias v)/den v` is the **only** possible q; [NeedleInverseComplete.lean](NeedleInverseComplete.lean) proves candidate correctness and uniqueness by exact integer algebra. The reduced list searches at most `⌊(K+2)/3⌋+1` valuation slots plus a single explicit exceptional entry (counting also failed candidates); it gives all actual incoming one-step edges to a chosen terminal. The [source bridge](NeedleCubicEnumerateSource.lean) transfers the iff verbatim to `highLevelNext (.N (oddTower q v)) = some (.N (haltTower k))` with `K=k+1`.

A complementary [NeedleGeneralInverse.lean](NeedleGeneralInverse.lean) proves a complete inverse enumeration for **every** ordinary destination counter `e`, using at most `⌊log₂(e+2)⌋+1` valuation candidates, with no terminal restriction. Its original-source bridge is [NeedleGeneralInverseSource.lean](NeedleGeneralInverseSource.lean). This is a reusable exact backward-search kernel, not a bound on an actual blank-root time.

### Verification and research significance

- **Original unchanged-source verification passed**, [manual GitHub Actions 41885221047](https://github.com/FlareZ123/bb6/actions/runs/41885221047): both standalone Lean 4.36.0-rc2 and pinned original DeepMind-source job compiled `NeedleCubicBound.lean`, `NeedleCubicBoundSource.lean`, and the earlier half-bound and general-inverse chain. A previous pinned source check for full general inverse succeeded at [41883568806](https://github.com/FlareZ123/bb6/actions/runs/41883568806). Kernel-reported axioms are only the standard Lean axioms, no sorry.
- **Cubic executable-list/source verification:** a separate updated manual CI run is being checked. The local `NeedleCubicEnumerate.lean` compiled against real `NeedleCubicBound.olean` in Lean 4.36.0-rc2, only standard logical axioms; preserve this distinction pending pinned-source compilation.
- Source-dependent theorem `NeedleCubicBoundSource.original_terminal_cubic_bound` states, for an original terminal `haltTower k`, the exact exception `(q,v,k)=(61,6,12)` or `3v≤k+3`. There is **no** result proving a given source is visited by blank N1, no root nonhalting theorem, no exact Busy Beaver bound, and no external-priority claim. These are intermediate methods in `im-results/`.

**Next discriminating research:** combine the exhaustive predecessor generator with source-*reachable* predicates and an invariant of the actual blank N1 sequence, including maximal odd-run packets from Agent 48. Elimination of a whole surviving true-blank feeder family, or a genuine halt, is what can resolve Space Needle. Further arithmetic-only sharpening may improve proof-search efficiency but cannot classify the machine by itself.
