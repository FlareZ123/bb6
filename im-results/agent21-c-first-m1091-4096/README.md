# Machine C low first-stop inverse exclusions

**Status: original-source Lean verified.** The focused manual workflow [45154176898](https://github.com/FlareZ123/bb6/actions/runs/45154176898) completed successfully with Lean 4.36.0-rc2. The axiom reports for both final theorems contain only `propext`, `Classical.choice`, and `Quot.sound`; neither contains `sorryAx`.

## Theorem

For the unchanged Machine C section transition `BB6.Agent46.secNext`, starting from the blank-origin section state `(5,1)`, consider a low first-stop target `(1,k)` satisfying

`k + 3*m + 4 = 2^(2*m+3)`.

The original blank-origin orbit never reaches `(1,k)` if either

- `m ≡ 1091 (mod 4096)`, or
- `m ≡ 12355 (mod 16384)`.

The formal results are:

- `BB6.Agent21Low1091.first_stop_m1091_mod4096`
- `BB6.Agent21Low1091.first_stop_m12355_mod16384`

Each theorem excludes the target at every finite section-run time. This is not a bounded simulation result.

## Shared exact inverse chain

Writing `k = 1024*q + 819`, the complete original-source inverse classification forces the following five predecessor edges:

```text
(1, 1024*q + 819)
  <- (512*q + 408, 768*q + 612)
  <- (1280*q + 1018, 384*q + 305)
  <- (832*q + 659, 608*q + 481)
  <- (720*q + 568, 664*q + 523)
  <- (692*q + 543, 678*q + 532)
```

The arrows point from a target to its uniquely classified immediate source parent. The final state has even right coordinate. The source-certified even-right theorem forces the direct predecessor
`(x,y) -> (x+y-2, (y-2)/2)`
whenever `y >= 6` is even and `(x+y) mod 8` is neither 0 nor 7.

### First cylinder: q ≡ 0 (mod 4)

For `m = 4096*r + 1091`, the stopping equation implies
`q + 12*r + 4 = 2^(2*m-7)`,
so `q ≡ 0 (mod 4)`. One further direct even-right reduction reaches

`(1370*q + 1073, 339*q + 265)`.

Its right coordinate is odd and its coordinate sum is 2 modulo 4.

### Second cylinder: q ≡ 11 (mod 16)

For `m = 16384*r + 12355`, the stopping equation implies
`q + 48*r + 37 = 2^(2*m-7)`,
so `q ≡ 11 (mod 16)`. Writing `q = 16*v + 11`, three further direct even-right reductions reach

`(30056*v + 22129, 1356*v + 997)`.

Again, the right coordinate is odd and the coordinate sum is 2 modulo 4.

The source-verified all-time blank-section theorem `BB6.Agent38.blank_section_mod4` forbids such a state when the right coordinate is at least five. Both terminal right coordinates satisfy that bound.

## Relation to the exact Machine C criterion

Both progressions pass the previously maintained low restrictions: in particular, they have `m ≡ 67 (mod 1024)`, `m ≡ 3 (mod 16)`, and `m ≢ 0 (mod 128)`. Thus these are additional exclusions, not restatements of the earlier `jointLowAllowed`, `Agent11Joint.lowAllowed`, or `lowAllowedValSixFull` predicates.

The next useful step is to compose these two exclusions into a separate strengthened low-parameter predicate around `ValSixJointFull.lean`, while preserving its existing exact equivalence. The remaining low and high parameter existentials are still unbounded. Machine C halting and BB(6) remain unresolved.

## Reproduction

- Proof source: [`Low1091Source.lean`](Low1091Source.lean)
- Manual source workflow: [`agent21-low1875-source.yml`](../../.github/workflows/agent21-low1875-source.yml)
- Successful original-source verification: [GitHub Actions run 45154176898](https://github.com/FlareZ123/bb6/actions/runs/45154176898)
