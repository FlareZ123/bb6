# Exact S-window carry states over the 9,968-transition finite trace

**Status:** finite source-derived computation for (D_{33}\to D_{10001}). This is not an all-time invariant or a BB(6) proof.

## Computation

For each transition (n=33,\ldots,10000):

- Recompute the exact root recurrence (D_n\to D_{n+1}).
- Use the correction-only S-window buffer (B_{\mathrm{corr}}=34\ell_S+122) at source and target.
- Extract the target digit-pair word on ([k_T+2,j_T-2)).
- Run both `ResetPatternDFA` and `ResetPostStateDFA.post_reset_pair`; their first-reset offsets agree.
- Map the first reset label to its exact closure seed, then feed the suffix through the 66-state paired-carry transducer.
- Independently feed the suffix through the 211-state universal subset DFA and compare the exact singleton path with its residual subset.

Detailed rows for the 84 non-singleton universal residuals are in [ExactSeedCarry84.md](ExactSeedCarry84.md) and [ExactSeedCarry84.json](ExactSeedCarry84.json).

## Finite-trace results

All 9,968 transitions passed all of the following source-derived checks:

1. The source affine update reproduces the next root coordinates.
2. The sign-based source branch agrees with the drain-derived threshold branch.
3. The sign-based target branch agrees with its drain-derived threshold branch.
4. The first accepting offset of `ResetPatternDFA` equals the first output offset of `post_reset_pair`.
5. Every reset label maps to the matching closure seed.
6. The exact seed path's end state belongs to the universal residual subset.

The universal subset DFA has rank 1 on **9,884** transitions and rank greater than 1 on **84**. Its rank histogram is:

| Residual rank | Count |
|---:|---:|
| 1 | 9,884 |
| 2 | 61 |
| 3 | 10 |
| 4 | 5 |
| 5 | 1 |
| 7 | 1 |
| 8 | 3 |
| 66 | 3 |

The 84 non-singleton subset states lie in recurrent components as follows: B1:13, B2:36, B3:2, B5:7, B7:6; the other 9,904 transitions are in transient/non-SCC subset states.

The exact paired end-state distribution reaches **all 66** states of the paired transducer. The exact active-branch projection reaches **49** branch-state IDs. Its five observed carry vectors are not merely a finite-trace observation: [\`PostResetCarryPairInvariant.lean\`](../agent49-parity623/PostResetCarryPairInvariant.lean) proves \`leftNext_valid\` and \`rightNext_valid\` for every allowed paired state and input digit, and proves \`allowed_step\` plus \`reset_output_suffix_closed\`. Consequently, for every finite suffix after one of the 54 reset-output seeds, the L carry is in \`{(-1,0),(0,0)}\` and the R carry is in \`{(-1,0),(-2,0),(-2,1),(-3,1)}\`. The union is the following five vectors:

| Active carry vector | Count |
|:---:|---:|
| ((-1,0)) | 3,241 |
| ((-3,1)) | 1,173 |
| ((-2,1)) | 1,788 |
| ((0,0)) | 1,989 |
| ((-2,0)) | 1,777 |

The target branch occurs L:4,097 and R:5,871 times. The first reset is always found after 3–12 symbols. The suffix length ranges from 0–13.

The target-active projection of the universal residual subset has sizes: 1:9,905; 2:47; 3:10; 4:3; 18:2; 36:1. The three rank-66 cases have empty suffixes. Among the 81 nonempty non-singleton cases, the projection sizes are 1:21, 2:47, 3:10, 4:3.

## Interpretation and next use

The exact seed path is deterministic on every one of the 9,968 scanned transitions, including the 84 cases where the universal subset does not collapse. Thus universal subset synchronization is stronger than necessary for this finite root trace. The actual paired end state is always available from the reset label plus the concrete suffix.

This does **not** establish that future S-windows always contain a reset. The post-reset carry bound itself is already formally established by the cited Lean invariant; the remaining global task is to prove that every future authentic S-window reaches one of the reset-output seeds and to connect the exact root windows to that reset mechanism. The 84 exceptional universal subsets need not be forced to collapse: the concrete reset label selects one exact seed, and the suffix then follows a deterministic 66-state path.

**Projection convention:** active means the target's branch, determined by its drain threshold. This computation gives 21 singleton / 60 nonsingleton active projections among the 81 nonempty exceptions, rather than the previously circulated 18/63 count. The source-branch projection gives 27/54. The discrepancy is explicitly unresolved; see the note in [ExactSeedCarry84.md](ExactSeedCarry84.md).
