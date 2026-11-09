# Machine C: exact original-root mass-100,000 stopping criterion

**Status:** all five declarations kernel-checked in the full original-source Lean 4.36.0-rc2 dependency closure on 9 November 2026, with only standard axioms and no `sorryAx`. The all-phase workflow subsequently failed at a later independent module. [Source check 42548044543](https://github.com/FlareZ123/bb6/actions/runs/42548044543). No machine-wide nonhalting result or exact BB(6) is claimed.

## Source-checked theorem

[Mass100KHalting.lean](Mass100KHalting.lean) imports the original-source Agent 4 `CResidualMass100000.lean` and the exact source-level `HighEvenRightC23FullForcedResidual` halting criterion. Let
```
L(m) = 2^(2*m+4)-(6*m+7)
H(j,m) = 2^(2*m+3)*(j+3)-(6*m+7).
```
These are the exact weighted masses `a+2*k` of the two families of genuine Machine C stopping inputs.

The theorem `source_halts_iff_mass100k` states the following **biconditional**, using existing source-verified root decision `valSixMixedRootDecision`:

```
BB6.CReachBridge.RunHalts ↔
    (∃ m, lowAllowedC70 m ∧ L(m)>100000 ∧
       valSixMixedRootDecision 1
         (2^(2*m+3)-(3*m+4)) = true)
  ∨ (∃ j m, highAllowedC23WithEvenRightFullForcedBool j m = true
       ∧ H(j,m)>100000 ∧
       valSixMixedRootDecision (2*j+3)
         (2^(2*m+2)*(j+3)-(j+3*m+5)) = true).
```

This is a lossless reparameterization of the authentic original blank-tape halt question: the additional strict mass inequalities are logically forced by the original-source finite exclusion, and the converse simply forgets them. It does **not** classify the still-unbounded existential or determine BB(6).

The proof separately source-checks `low_root_mass_gt` and `high_root_mass_gt` by converting the rooted executable Boolean to true `CReach`, identifying the original section reachability relation, and applying the previously proved 100,000-mass barrier. No independent simulation assumption is introduced at this integration layer.

## Explicit root-necessary parameter tails

All low-family authenticated candidates obey **m ≥ 7**, by `low_root_depth_ge7`. For the high family, `high_root_parameter_tail` proves the exhaustive alternatives:

| m | Necessary j |
| ---: | ---: |
| 0 | j ≥ 12498 |
| 1 | j ≥ 3123 |
| 2 | j ≥ 779 |
| 3 | j ≥ 193 |
| 4 | j ≥ 46 |
| 5 | j ≥ 10 |
| 6 | j ≥ 1 |
| ≥7 | No j restriction from mass alone |

All numbers follow directly from the source mass formulas. The table is **necessary**, never sufficient, for a halting target to occur on the blank-root orbit.

## Validation and relation to prior work

The source certificate `CResidualMass100000` was already compiled in [Agent 4 run 42420156191](https://github.com/FlareZ123/bb6/actions/runs/42420156191). This contribution integrates its full mass-100,000 theorem with the strongest existing source-authentic original Machine C stopping equation and eliminates all corresponding small-mass cases at the level of the explicit halt iff.

The new theorem source run [42548044543](https://github.com/FlareZ123/bb6/actions/runs/42548044543) printed:
```
'BB6.Agent47C100K.low_root_mass_gt' depends on axioms: [propext, Classical.choice, Quot.sound]
'BB6.Agent47C100K.high_root_mass_gt' depends on axioms: [propext, Classical.choice, Quot.sound]
'BB6.Agent47C100K.source_halts_iff_mass100k' depends on axioms: [propext, Classical.choice, Quot.sound]
'BB6.Agent47C100K.low_root_depth_ge7' depends on axioms: [propext, Classical.choice, Quot.sound]
'BB6.Agent47C100K.high_root_parameter_tail' depends on axioms: [propext, Classical.choice, Quot.sound]
```
No `sorryAx` appeared in these five declarations. The workflow later failed after checking unrelated `M0Mod8Three` source, not in the Agent47 mass source theorem.

For the actual resolution of Machine C, an all-time source invariant excluding both infinite stopping families, or a genuine primitive-machine halting witness, remains necessary. This intermediate integration belongs in `im-results/` under the repository publication policy.
