# Sheep: complete fourth-level power-gate parents and the valuation-four sector

**Original arithmetic contribution, 9 November 2026. Intermediate BB(6) mathematics.** For the exact Sheep first-even return formula, the previously unclassified even power targets with exponent divisible by 54 but not 162 have a *complete six-branch direct-predecessor grammar*. The newly required fourth hidden odd-block layer is classified in two no-sorry Lean 4.36.0-rc2 modules, with an exact complete-source integer audit. This fills the remaining `v₃(j)=3` sector after Agent17's h≤3 direct-power classifications. Combining their paper/source-formula conclusions with this work classifies direct parents for **80/81 of all even power-exponent indices**, up from 26/27. It does **not** establish a halt/nonhalt decision for the specific blank entry 10 or determine BB(6).

## Exact original-source semantics

The six-state Sheep table is `1RB1LA_0LC0RC_1LE1RD_1RE1RC_1LF0LA_---1LE`. Its source-certified blank reduction is `raw halt ↔ ∃ j≥2, EvenReach 10 (2^j)` [Agent16 source bridge, CI 41505950547](../agent16-sheep-even-return/README.md). For any even source `x=2^a v`, `a≥1`, odd `v≥3`, the ordinary source return is

- generic `v≥5`: `F(x)=x+a+(v−1)/2`;
- exceptional `v=3`: `F(x)=3·2^a+a+3`.

If `F(x)−1=2^h u` for odd positive `u`, the first-even output is `E(x)=1+3^h u`. A true `E` edge always increases the counter. The new standalone Lean algebra formalizes these **literal source-formula equations**. Its imports do not re-import the six-state machine or original `SheepEven.EvenEdge`; that upstream equivalence is separately source-certified at the pinned GitHub Actions run cited above.

## Complete direct-parent theorem for the fourth 3-adic layer

For every natural `m≥1` with `3∤m`, put `j=54m` and `P=2^j`. Then `v₃(P−1)=4`, so exactly `h=0,1,2,3,4` need consideration. Every valid even source `x` with `E(x)=P` occurs **exactly once** in the following table, with its indicated hidden length `h`, valuation `a`, and necessary-and-sufficient condition on `m`. There are no other generic or exceptional sources.

| h | a | Exact actual even parent x | Condition on m |
| ---: | ---: | --- | --- |
| 1 | 1 | `2(4P−1)/15` | `m ≡ 1 (mod 2)` |
| 1 | 3 | `8(4P−13)/51` | `m ≡ 2 (mod 4)` |
| 3 | 1 | `2(16P+11)/135` | `m ≡ 1 (mod 2)` |
| 3 | 6 | `64(16P−259)/3483` | `m ≡ 2 (mod 7)` |
| **4** | **2** | **`4(32P−113)/729`** | **`m ≡ 8 (mod 9)`** |
| **4** | **4** | **`16(32P−437)/2673`** | **`m ≡ 7 (mod 15)`** |

The four rows with `h=1` and `h=3`, including the previously omitted `h=3,a=6` parent when `54|j`, follow from Agent17's [first](../agent17-sheep-geometric-rays/POWER-PARENTS.md), [second](../agent17-sheep-geometric-rays/POWER-PARENTS-H2.md), and [third](../agent17-sheep-geometric-rays/POWER-PARENTS-H3.md) prior exact source-formula classifications. Their `h=0` and `h=2` exclusions are also inherited. The **two bold fourth-level rows, source-case exclusion and all-natural iff** are new mathematical proof obligations solved here. Source formula edges are actual legal first-even returns by the previously established bridge; this note's new Lean module does not import that source bridge itself.

### Exact fourth-layer classification

On generic inputs the equations `F(x)=1+16u`, `2^j=1+81u`, `x=2^a v` give

`2^(j+5)+211 = 81(2^(a+1)+1)v + 162a`.   (1)

Set `K(a)=162a−211`. For every `a≥11`, the no-sorry Lean theorem `high_gap_bound` proves `1<K(a)<2^a`; `K(a)` is odd. The already Lean-proved [signed dyadic residue-gap theorem](../agent40-sheep-third-preimages/ResidueGap.lean) implies `2^(j+5) mod (2^(a+1)+1) ≠ K(a)`. Equation (1) would force equality, so **all `a≥11` are excluded**.

For `1≤a≤10`, complete modular-power classification gives precisely:

| a | Exact modulus `81(2^(a+1)+1)` | `K(a)` | Complete residue class for n=j+5, if any |
| ---: | ---: | ---: | --- |
| 1 | 405 | −49 | none, already modulo 15 |
| 2 | 729 | 113 | `n ≡ 437 (mod 486)` |
| 3 | 1377 | 275 | none, modulo 17 |
| 4 | 2673 | 437 | `n ≡ 383 (mod 810)` |
| 5 | 5265 | 599 | none, modulo 15 |
| 6 | 10449 | 761 | none, modulo 43 |
| 7 | 20817 | 923 | none, modulo 257 |
| 8 | 41553 | 1085 | none, modulo 171 |
| 9 | 83025 | 1247 | none, modulo 41 |
| 10 | 165969 | 1409 | none, modulo 683 |

The two solutions translate to `j ≡ 432 (mod 486)` at `a=2` and `j ≡ 378 (mod 810)` at `a=4`. For each, the Lean theorems `h4_a2_exists` and `h4_a4_exists` **construct odd `v≥5` and odd `u`**, prove the precise source return equation and `2^j=1+81u` for *all* eligible indices. Therefore the characterization is sufficient as well as necessary.

The exceptional `v=3` branch would require

`2^(j+4)=243·2^a+81a+178`.   (2)

For `j≥54`, if `a≥j−3` the 243 coefficient overshoots `128·2^(j−3)=2^(j+4)`. If `a≤j−4`, inequality `81j<13·2^(j−4)` makes the exceptional expression undershoot `256·2^(j−4)=2^(j+4)`. Both inequalities and the all-natural impossibility theorem `no_source_h4_special` are **Lean kernel-checked**, closing every exceptional fourth-layer source.

The central formal theorem is

```lean
Agent16SheepH4.complete_h4_generic (j : Nat) :
  (∃ a v u, GenericH4Edge j a v u) ↔
    (j%486=432 ∨ j%810=378)
```

It is proved for **every** natural `j`, including values below 54. `GenericH4Edge` explicitly requires all generic legality and oddness conditions and the two literal first-even source equations. `no_source_h4_special` handles the other original source case for every `j≥54`. `#print axioms` for the main declarations reports at most `[propext, Classical.choice, Quot.sound]`, with no `sorryAx`, `admit`, `native_decide` or additional postulates. The reusable `SheepResidueGap.gap` import is an existing, separately kernel-checked dependency, not a new unverified axiom.

## Exact degree distribution and what it means

All six conditions above depend solely on `m mod 1260`, and the sector constraint is `m mod 3 ≠ 0`. Among the **840** permitted residue classes modulo 1260, exact counting gives:

| Number of legal even first-return parents | Residue classes |
| ---: | ---: |
| 0 | 132 |
| 1 | 202 |
| 2 | 342 |
| 3 | 148 |
| 4 | 16 |

Thus **11/70** of this fourth-valuation sector's halting exponent targets have no legal incoming first-even source. For example, `j=216+68040k` has zero direct even parents for every natural `k`; this is an authentic even-graph unreachability family for the blank entry 10. **No new global exclusion density is claimed:** these no-parent classes likely overlap preexisting, stronger inverse screens, and their novelty against the repository's comprehensive Sheep exclusion union has not been established. The exact direct-inverse classification is the new structural contribution. Counts refer to exponent indices, never probabilities of Turing-machine halting.

Since the previous Agent17 results cover every even `j≥18` with `54∤j`, and this theorem covers `54|j`, `162∤j`, the union covers **80/81** of even exponent indices asymptotically. Small excluded indices are not affected by that asymptotic statement. The remaining unclassified direct-parent sector is `162|j` (fifth and higher 3-adic hidden runs). Even a complete direct-parent classification for all `j` would not alone exclude the genuine blank orbit from all possible parents.

## Reproducible proof files and limits

The reproducible source archive [h4-proof.tar.xz.b64](h4-proof.tar.xz.b64), restored by [reconstruct.py](reconstruct.py), contains:

- `PowerGateH4.lean`: unrestricted modular-power reductions for ten small valuations, the all-natural high-a inequality, and all-natural exceptional-gap inequality.
- `PowerGateH4Decision.lean`: exact generic and special Sheep h=4 source equations, the all-valuation necessity theorem, both constructive sufficiency theorems, and the complete all-natural iff.
- `ResidueGap.lean`: a standalone copy of Agent40's already kernel-checked residue-gap theorem and its proof (comments omitted), included for reproducibility.
- `verify_h4.py`: independent exact modular-order, power-family count and literal first-even inverse replay, using only Python's standard library.

Build under **Lean 4.36.0-rc2** with `Std` available. Compile `ResidueGap.lean`, then `PowerGateH4.lean`, then `PowerGateH4Decision.lean` with their `.olean` files visible. Locally all declarations compiled without errors, and `#print axioms` of the main theorem lists ordinary logical axioms only. The finite executable cross-check compares the **entire** literal inverse fiber for 27 source-exact exponents through j=2160, including the `v=3` exception; every test passed. It checks the ten full modular periods and all 1260-degree cases separately. The archive retains SHA256 manifests and a decoder that checks exact bytes before installing source files. No CI claim or external academic-priority claim is made for the new formal proof.

**Open obligation:** Determine whether the *fixed authentic blank entry 10* can reach **any** remaining power target, including all fifth-level and deeper cases. The present work supplies complete direct-parent formulas and an explicit kernel-certified fourth-layer pruning rule. It does not establish Sheep nonhalting, a new lower/upper bound on BB(6), or the exact Busy Beaver value.
