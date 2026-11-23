# Machine C low first-stop inverse exclusions

**Status: original-source Lean verified and integrated into the exact low/high criterion.** The proof and integration are intermediate research results; they do not decide Machine C or BB(6).

## Source-level first-stop theorem

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

## Integration into the exact Machine C criterion

The new module `ValSixLowRefinement.lean` defines

`lowAllowedValSixRefined m := lowAllowedValSixFull m ∧ (m%4096 ≠ 1091 ∧ m%16384 ≠ 12355)`.

It proves `BB6.Agent21Low1091.blank_halts_iff_joint_val_six_refined`, an exact blank-halting equivalence with the two impossible low progressions removed. The high-parameter branch is unchanged. The proof obtains genuine blank reachability from Agent 3's fixed-target root decision, transfers it to the unchanged section run, and applies the two all-time first-stop theorems. The reverse implication simply forgets the added restrictions.

The two progressions pass the earlier low restrictions: both have `m ≡ 67 (mod 1024)`, `m ≡ 3 (mod 16)`, and `m ≢ 0 (mod 128)`; they also avoid the existing `jointLowAllowed` residue exclusions. Thus this is an additional explicit restriction on the previously accepted `lowAllowedValSixFull` domain, not a restatement of its existing congruence filters.

The refined equivalence is source-verified by the existing manual Agent21 workflow. Its dependency-closure step compiled 191 project modules, including `ValSixJointFull.lean` and `ValSixLowRefinement.lean`. The final axiom report for `blank_halts_iff_joint_val_six_refined` is `[propext, Classical.choice, Quot.sound]`, with no `sorryAx`.

## Remaining frontier

The refined low and high parameter existentials remain unbounded. This contribution narrows the exact low domain but does not establish that the remaining low or high roots are empty. Machine C halting and BB(6) remain unresolved.

## Reproduction

- Original-source proof: [`Low1091Source.lean`](Low1091Source.lean)
- Exact criterion refinement: [`ValSixLowRefinement.lean`](ValSixLowRefinement.lean)
- Manual workflow: [`agent21-low1875-source.yml`](../../.github/workflows/agent21-low1875-source.yml)
- First-stop proof run: [45154176898](https://github.com/FlareZ123/bb6/actions/runs/45154176898)
- Exact criterion integration run: [45155413576](https://github.com/FlareZ123/bb6/actions/runs/45155413576)
