# Machine C integrated low/high sieve

## Status and scope

The current integrated criterion is in `im-results/agent3-c-bounce-inverse/ValSixJointFull.lean`.

Its central theorem is:

```lean
BB6.Agent3ValSix.blank_halts_iff_joint_val_six_full
```

It gives an exact equivalence for Machine C between blank-origin halting and two parameterized branches whose fixed targets are decided by `valSixMixedRootDecision`. The low and high parameter domains are still unbounded. This is a stronger exact sieve, not a solution of BB(6).

The theorem is built on the source-exact criterion in `ValSixJointFast.lean`, then adds stopping-equation pullbacks of original-source blank-unreachability theorems.

## Final parameter predicates

The low predicate is:

```lean
BB6.Agent11Joint.lowAllowed m ∧ ¬(128 ≤ m ∧ m % 128 = 0)
```

The high predicate is:

```lean
highAllowedValSixThree j m ∧
BB6.Agent19Five.highAllowed j m ∧
¬(j % 32 = 31 ∧ 3 ≤ m ∧ (j + 3*m) % 128 = 127) ∧
¬(j % 8 = 5 ∧ m % 8 = 4 ∧ (9*j + 39) % 128 = (3*m) % 128) ∧
¬(m % 32 = 21 ∧ j % 32 = 28) ∧
(BB6.Agent15.affineNormalize (2*j+3)
  (2^(2*m+2)*(j+3) - (j+3*m+5))).2 ≠ 4
```

The existing predicates retain the Agent3/11/19/29 joint restrictions. The new conjuncts remove four additional infinite parameter families.

## Four source-certified infinite families

### Low 124 family

For `m = 128*(r+1)`, the low stopping equation forces the blank target to have residue 124 modulo 128. `Low124Stop.lean` proves this target is unreachable.

- `low_124_family_previous_sieve` proves this family passes the earlier Agent11 low sieve.
- `low124_infinite_family_removed` proves the integrated predicate removes every member.

### High 124 family

For `j = 31` and `m = 32 + 128*r`, the high stopping equation forces the target into the original-source high-124 rectangle. `High124Stop.lean` proves unreachability.

- `high_124_family_previous_sieves` proves the family passes the earlier Agent3/11/19/29 high restrictions.
- `high124_infinite_family_removed` removes every member.

### Second sum-seven slope

For `j = 5` and `m = 28 + 128*r`, the high stopping equation gives `k % 16 = 2` and `(k + 10*j + 44) % 128 = 0`. Writing `j = 8*u + 5` and `k = 16*v + 2` yields `(5*u + v) % 8 = 2`, with `v ≥ 2`. This is exactly the input cylinder excluded by `OddSevenSecondCylinder.blank_no_second_slope`.

- `second_slope_family_previous_sieves` proves the full residue family passes the earlier high restrictions.
- `second_slope_infinite_family_removed` removes every member.

### New branch of the 27/0 rectangle

For `j % 32 = 28` and `m % 32 = 21`, the high stopping equation gives `(2*j+3) % 32 = 27`, `k % 32 = 0`, and `k ≥ 64`. The original-source theorem `MixedRectangle27Zero.blank_no_rectangle_27_zero` excludes the resulting blank-origin target.

The other branch, `j % 32 = 12` and `m % 32 = 5`, is already covered by `jointHighRectAllowed`. The integrated predicate therefore adds only the previously uncovered branch.

- `rectangle27_infinite_family_removed` removes the entire new branch.
- `rectangle27_sample_previous_sieves` proves the concrete pair `j = 28, m = 85` survives the previous exact high sieve.

## Independent M512 quotient comparison

`QuotientRectCensus.cpp` reproduces the finite M512 quotient graph and measures the parameter-family residue cycles. The quotient is an overapproximation, so quotient admission is evidence that this finite abstraction cannot eliminate the state. It is not evidence of actual reachability. The Lean source theorems establish actual blank-origin non-reachability.

The M512 graph census is:

- 67,633,152 quotient vertices;
- 27,858,704 reached states;
- 221,572,376 transition edges;
- 27/0 rectangle: 256 cells, 60 quotient-admitted;
- 25/4 rectangle: 256 cells, 0 quotient-admitted.

The parameter-family cycles give:

| Family | Cycle length | Quotient-admitted |
|---|---:|---:|
| Low 124 | 4 | 2 |
| High 124 | 4 | 2 |
| Second slope | 4 | 1 |
| New 27/0 branch | 16 | 4 |

For the new 27/0 branch, `j = 28, m = 85` projects to `(59,224,0)`, which the M512 quotient admits. The Lean source rectangle theorem excludes the actual blank-origin reachability. This is the clearest demonstrated improvement beyond the M512 quotient.

Concrete quotient-admitted stopping targets (the right coordinate is shown in closed form):

| Family | Parameters | Original-source target `(x,k)` | `k mod 512` |
|---|---|---|---:|
| Low 124 | `m=128` | `(1, 2^259 - 388)` | 124 |
| High 124 | `j=31,m=160` | `(65, 34*2^322 - 516)` | 508 |
| Second slope | `j=5,m=284` | `(13, 2^573 - 862)` | 162 |
| New 27/0 branch | `j=28,m=85` | `(59, 31*2^172 - 288)` | 224 |


The 25/4 rectangle was deliberately omitted from the final predicate. The independent census excludes all 256 of its quotient cells, so adding that source theorem would duplicate an existing stronger barrier.

To reproduce the quotient census:

```sh
g++ -O3 -std=c++17 QuotientRectCensus.cpp -o QuotientRectCensus
./QuotientRectCensus 512
```

The C++ computation is empirical. Its output is not used as a premise in the Lean theorem.
The preserved run output, including every residue-cycle state, is in [QuotientRectCensus-M512.txt](QuotientRectCensus-M512.txt).

## Axiom and proof audit

The combined Lean file prints axioms for the central iff and each new family theorem. The 124 source chain uses `Low124Cone.lean`, `Low124Rectangle.lean`, `Low124Stop.lean`, and `High124Stop.lean`. These compiled with only `propext`, `Classical.choice`, and `Quot.sound` in run `42247836737`.

Do not use `Low124SharpBlank.lean` as a certified proof. Its attempted `decide` reductions fail, and its emitted theorem depends on `sorryAx`. This integration intentionally uses the older parameter-specific source proofs.

The final refined joint build succeeded in CI run `42252457830` at 16:31:29 UTC. This run includes the removal of the quotient-redundant 25/4 condition, the isolated new 27/0 branch, the high-124 prior-sieve theorem, and the concrete 27/0 nonredundancy witness. Earlier successful run `42248919012` checked the preceding version with the full 25/4 and 27/0 parameter rectangles.

## External BB(6) context

The public Busy Beaver community tracker still lists BB(6) as unsolved. It records the June 2025 champion lower bound `S(6) > Σ(6) > 2↑↑↑5` and reports roughly 1,100 informal holdouts as of August 2026. This is background context only; none of the public lower-bound claims is used in the Lean proofs above. See [BusyBeaverWiki: BB(6)](https://wiki.bbchallenge.org/wiki/BB%286%29) and [bbchallenge's definition/status page](https://bbchallenge.org/story).

## Remaining mathematical gap

The existential parameter branches in `blank_halts_iff_joint_val_six_full` remain unbounded. No upper bound on `m` or `j` has been established, and no exact BB(6) value follows. The next useful work is to derive stronger symbolic restrictions on the surviving parameter domain, identify further source cylinders that eliminate M512-admitted states, or prove a finite bound for the remaining search.
