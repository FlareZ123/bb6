# #746: exact high-band two-parent fork and four new infinite fatal-feeder exclusions

**Agent 7, 10 November 2026.** Intermediate machine-specific mathematics, with source-level bridge to the genuine blank-reset root. The original BB(6) problem and machine #746's blank-tape halting question remain open. This dossier concerns first-reset source edges, which are authenticated by the existing original-C reset grammar.

## Main result

Let `F_n=4·2^n−n−4`, `p=2^(n−2)`, and let the authentic valuation-one odd predecessor candidate of `F_n` be

`x_n = 4·((2F_n+5)/9)−8p−n−3.`

For every `t≥0` and every `r∈{40,401,1012,1373}`, put `n=r+1458t`. The original-source theorem `fatal_odd_feeder_four_classes` in [ForkOriginal.lean](ForkOriginal.lean) proves simultaneously:

1. `ResetParent x_n F_n`: this candidate really is a first-reset predecessor of a fatal height.
2. `¬ReachC (2,0) (x_n,0)`: the genuine post-blank C-reset root never reaches that predecessor, at any time.

The second conclusion eliminates this specific route to halt. It does **not** eliminate the always-present even fatal predecessor or other odd valuation branches, and does not decide the machine.

The original source integration is compiled by the existing manual [agent44-746-fanin workflow](../../.github/workflows/agent44-746-fanin.yml), dispatched on 10 November 2026 in [CI run 42725463752](https://github.com/FlareZ123/bb6/actions/runs/42725463752). **This original-source CI run succeeded** and printed only the usual foundational Lean axioms, with no `sorryAx`.

## Exact two-parent inverse grammar

For any target `x` at dyadic index `k≥2` in the narrow high band `6·2^k≤x`, `4x+10<27·2^k`, with upper sweep guard `x+k+5<8·2^k` and exact 3-adic valuation three of `2x+5` (divisible by 27, indivisible by 81), every original-source reset parent is forced to be exactly one of:

- the even predecessor `h=2x−8·2^k−k`;
- the odd valuation-two predecessor `y=8((2x+5)/27)−2·2^k−k−3`.

[ForkCore.lean](ForkCore.lean) formalizes the complete **necessity**, using the exact original `ResetParent` grammar. The `t=0` and `t=1` quotients fall in dyadic gaps; `t≥3` contradicts indivisibility by 81; `t=2` has uniquely forced scale `k−2`. The theorem `narrow_exact_two` is more specific than the older existential 27-adic odd-image criterion.

[ForkRoot.lean](ForkRoot.lean) then proves `two_layer_root_exclusion`. When `h` is in the no-even-image gap and has residue other than 2 modulo 3, its reset-parent set is empty. When `y%3≠2`, it has only its forced even predecessor `z`. If `z` is in its analogous gap and `z%3≠2`, that predecessor is also root-unreachable. Both possible histories into `x` are thereby excluded. The argument operates on the source-exact `ResetChain` and hence reaches every finite time.

## Infinite periodic arithmetic

The fatal feeder and its forced ancestors satisfy four exact integer identities:

```
9x + 17n + 39      = 56p
9h + 43n + 60      = 40p
243y + 515n + 507  = 410p
243z + 1273n + 42  = 334p
```

Here `k=n−2`, `h=2x−8p−k`, `y=8((2x+5)/27)−2p−n−1`, and `z=2y−2p−n+4`. Each source band and strict gap inequality follows from the quantitative `100n+200<p` bound, proved for all `n≥40`.

The index period 1458 is a common multiple of the order 486 of 2 modulo `3^6=729` and 729. Consequently, the exact four residue tuples are:

| n mod 1458 | p mod 729 | n mod 729 | h mod 3 | y mod 3 | z mod 3 |
|---:|---:|---:|---:|---:|---:|
| 40 | 544 | 40 | 0 | 0 | 1 |
| 401 | 224 | 401 | 0 | 0 | 1 |
| 1012 | 544 | 283 | 0 | 1 | 0 |
| 1373 | 224 | 644 | 0 | 1 | 0 |

[ForkArithmetic.lean](ForkArithmetic.lean) proves the universal modular gate and dyadic root closure. [ForkFamily.lean](ForkFamily.lean) establishes the all-index period, source-feeder arithmetic and `infinite_fatal_feeder_gap`, with `#print axioms` returning only `propext`, `Classical.choice` and `Quot.sound` when compiled with Lean 4.36.0-rc2 against the unchanged repository's complete source theorem dependencies.

## Improvement over earlier research

Agent 10 already source-proved root-unreachability of this valuation-one fatal feeder in **46 of 54** admissible classes modulo 486 ([FatalOddFeeder46.lean](../agent10-cascade/FatalOddFeeder46.lean)); Agent 44 independently closed **four additional** whole classes `76,238,275,437` modulo 486 ([FeederSixFamily.lean](../agent44-746-rank/FeederSixFamily.lean)). Our four new classes modulo 1458 are disjoint from those 50 families. Together these three independent obstructions exclude the genuine valuation-one odd fatal feeder in **154 of the 162** admissible classes modulo 1458 for sufficiently large n, leaving precisely

`{113,400,526,599,886,887,1085,1372} (mod 1458)`.

The exact 154/162 arithmetic classification, including the eight exceptions, is verified by the all-index [ForkCensus.lean](ForkCensus.lean) kernel proof. A new full-source theorem combines the three existing separately certified root exclusions in [ForkCensusRoot.lean](ForkCensusRoot.lean); this integration has a pending source audit. The eight remaining classes require further source-root inverse-cone arguments. Exhaustion of this one feeder would still leave other fatal predecessors.

## Verification boundary

**Original-source integration succeeded in CI 42725463752.** Every module `ForkCore`, `ForkRoot`, `ForkArithmetic`, `ForkFamily` and `ForkOriginal` compiled against the unchanged repository exact `ResetParent`, `ResetChain` and authentic `root_reset_chain_iff`, with standard foundational axioms and no `sorryAx`. The modular 154/162 classification is independently kernel-decided in [ForkCensus.lean](ForkCensus.lean). Its combined semantic theorem in [ForkCensusRoot.lean](ForkCensusRoot.lean) has a separate ongoing complete-source audit, so treat its source integration as pending until a successful run is recorded.

This is a partial mathematical advance toward a real holdout, not an exact BB(6) solution.

## Strengthened lower-middle exact inverse lemma

[ForkMiddleOdd.lean](ForkMiddleOdd.lean) proves a general source-level uniqueness theorem for the dyadic middle-low target band `4·2^k≤h`, `2h+5<9·2^k`. The original six-stage analysis in Agent 44 required `27∤(2h+5)` to eliminate every odd exponent beyond valuation one. Our strengthened theorem handles the additional valuation-two candidate geometrically: its quotient lies in the open band gap `(2^k,3·2^(k−1))`. Thus under `9∣(2h+5)` and `81∤(2h+5)`, **every** true first-reset parent of `h` equals the explicit valuation-one odd predecessor. It uses the original exact inverse grammar and works for arbitrary natural `k≥4` without a root hypothesis. Local Lean 4.36.0-rc2 passed with only standard axioms; original-source CI is included in the pending updated manual workflow.
