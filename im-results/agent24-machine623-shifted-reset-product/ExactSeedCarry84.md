# Exact-seed carry paths for the 84 correction-only S-window exceptions

**Status:** finite source-derived replay. This resolves the actual singleton seed path for the scanned 84 cases; it is not an all-time invariant or a proof of BB(6).

## Method

For each source transition index listed in `SWindowPostResetSynchronization.md` (the scan is (D_{33}\to D_{10001})):

1. Recompute (D_n\to D_{n+1}) from the root recurrence and use the correction-only buffer (B_{\mathrm{corr}}=34\ell_S+122) for both S-windows.
2. Extract the target digit-pair word over ([k_T+2,j_T-2)).
3. Run both `ResetPatternDFA` and `ResetPostStateDFA.post_reset_pair`. Their first-reset offsets agree on all 84 words. The pair-output label maps to one exact seed in `PostResetCarryPairClosure.json`.
4. Feed the suffix after that first reset through the 66-state `PostResetCarryPairTransducer`, while independently feeding it through the 211-state universal subset DFA.
5. Project the universal residual subset onto the target's active branch (`target.g ≥ threshold`), and record the exact seed path's end state and active branch state/carry.

## Results

- All 84 source affine updates reproduce the next root coordinates exactly.
- Source and target sign-based branch choices agree with their drain-derived thresholds in all 84 cases.
- The first accepting offset of `ResetPatternDFA` equals the first output offset of `post_reset_pair` in all 84 cases.
- All 84 reset labels map to the matching closure seed; all 84 exact seed end states belong to the corresponding universal residual subset.
- The 84 universal residual subset ranks are: 2: 61, 3: 10, 4: 5, 5: 1, 7: 1, 8: 3, 66: 3.
- Their subset-state SCC distribution is: B1: 13, B7: 6, B5: 7, B2: 36, transient/non-SCC: 20, B3: 2.
- There are 45 distinct exact paired end states and 39 distinct exact active-branch state IDs.
- For the target-branch projection (distinct `L_state` or `R_state` IDs), all 84 cases have sizes 1: 21, 2: 47, 3: 10, 4: 3, 18: 2, 36: 1. Among the 81 nonempty suffixes the sizes are 1: 21, 2: 47, 3: 10, 4: 3.
- Three cases have empty suffixes: n=69 (seed=end=6, rank 66, active projection 18); n=93 (seed=end=1, rank 66, active projection 36); n=236 (seed=end=20, rank 66, active projection 18).

**Projection-convention note.** The table uses the *target's* active branch, since the suffix ends at the target's own S-window boundary. Under this convention the nonempty-suffix count is 21 singleton / 60 nonsingleton, not the 18/63 figure mentioned in an earlier message. Using the source branch instead gives 27/54. This discrepancy is left explicit for Agent 27 to reconcile; the exact paired end state and exact active state are unambiguous in the table.

The SCC label refers to the *universal subset state*, not to the exact singleton seed trajectory. In particular, membership of a subset state in B1/B2 does not imply that the actual root's singleton path is itself nonsynchronizing. The exact path is the `exactEndStateId` column.

## Exact table

| n | source→target branch | first reset / word length | suffix | seed | universal subset (SCC, rank) | exact end | active state / carry | active projection size |
|---:|:---:|---:|---:|---:|:---|---:|:---|---:|
| 33 | R→L | 4/7 | 3 | 0 | 10 (B1, r2) | 0 | 7 [-1,0] | 2 |
| 34 | L→R | 4/7 | 3 | 9 | 43 (B7, r3) | 9 | 188 [-3,1] | 3 |
| 35 | R→R | 5/8 | 3 | 9 | 43 (B7, r3) | 9 | 188 [-3,1] | 3 |
| 36 | R→R | 4/8 | 4 | 4 | 43 (B7, r3) | 9 | 188 [-3,1] | 3 |
| 37 | R→R | 4/8 | 4 | 4 | 43 (B7, r3) | 9 | 188 [-3,1] | 3 |
| 38 | R→R | 4/8 | 4 | 8 | 43 (B7, r3) | 45 | 193 [-2,1] | 3 |
| 40 | L→R | 3/8 | 5 | 4 | 130 (B5, r2) | 45 | 193 [-2,1] | 2 |
| 41 | R→L | 4/8 | 4 | 15 | 10 (B1, r2) | 39 | 12 [0,0] | 2 |
| 42 | L→L | 4/8 | 4 | 5 | 10 (B1, r2) | 0 | 7 [-1,0] | 2 |
| 43 | L→R | 3/8 | 5 | 8 | 64 (B2, r2) | 9 | 188 [-3,1] | 2 |
| 44 | R→R | 5/8 | 3 | 5 | 43 (B7, r3) | 9 | 188 [-3,1] | 3 |
| 45 | R→R | 4/8 | 4 | 5 | 130 (B5, r2) | 45 | 193 [-2,1] | 2 |
| 48 | R→R | 4/8 | 4 | 29 | 64 (B2, r2) | 9 | 188 [-3,1] | 2 |
| 50 | R→R | 5/8 | 3 | 10 | 130 (B5, r2) | 45 | 193 [-2,1] | 2 |
| 51 | R→L | 6/8 | 2 | 7 | 37 (transient/non-SCC, r4) | 0 | 7 [-1,0] | 2 |
| 55 | L→L | 5/8 | 3 | 10 | 127 (transient/non-SCC, r2) | 6 | 7 [-1,0] | 1 |
| 57 | R→R | 5/8 | 3 | 2 | 50 (B2, r2) | 19 | 128 [-3,1] | 2 |
| 62 | L→R | 6/8 | 2 | 27 | 45 (transient/non-SCC, r3) | 5 | 252 [-2,0] | 3 |
| 64 | R→R | 4/8 | 4 | 14 | 61 (B3, r4) | 18 | 98 [-3,1] | 2 |
| 66 | R→R | 5/8 | 3 | 8 | 59 (B5, r2) | 25 | 133 [-2,1] | 2 |
| 69 | L→L | 8/8 | 0 | 6 | 0 (transient/non-SCC, r66) | 6 | 7 [-1,0] | 18 |
| 72 | L→R | 4/8 | 4 | 2 | 62 (transient/non-SCC, r4) | 16 | 133 [-2,1] | 2 |
| 76 | R→R | 5/8 | 3 | 6 | 12 (B1, r2) | 41 | 77 [-1,0] | 1 |
| 77 | R→R | 6/8 | 2 | 4 | 49 (B2, r2) | 18 | 98 [-3,1] | 2 |
| 79 | R→R | 7/8 | 1 | 0 | 4 (transient/non-SCC, r8) | 12 | 107 [-1,0] | 4 |
| 80 | R→L | 6/8 | 2 | 3 | 31 (transient/non-SCC, r2) | 27 | 82 [-1,0] | 1 |
| 82 | L→L | 5/8 | 3 | 6 | 16 (B2, r2) | 3 | 162 [0,0] | 1 |
| 83 | L→R | 5/8 | 3 | 19 | 16 (B2, r2) | 42 | 197 [-1,0] | 2 |
| 84 | R→R | 6/8 | 2 | 6 | 28 (transient/non-SCC, r3) | 0 | 17 [-1,0] | 3 |
| 88 | L→R | 5/8 | 3 | 10 | 17 (B2, r2) | 4 | 222 [-2,0] | 2 |
| 90 | R→L | 6/8 | 2 | 12 | 15 (B2, r2) | 14 | 137 [0,0] | 1 |
| 92 | L→R | 7/8 | 1 | 12 | 4 (transient/non-SCC, r8) | 12 | 107 [-1,0] | 4 |
| 93 | R→R | 8/8 | 0 | 1 | 0 (transient/non-SCC, r66) | 1 | 47 [-1,0] | 36 |
| 94 | R→R | 4/8 | 4 | 7 | 68 (B2, r2) | 7 | 43 [-2,1] | 2 |
| 95 | R→L | 5/8 | 3 | 2 | 12 (B1, r2) | 2 | 57 [-1,0] | 2 |
| 96 | L→R | 5/8 | 3 | 25 | 64 (B2, r2) | 9 | 188 [-3,1] | 2 |
| 109 | L→R | 6/8 | 2 | 5 | 55 (transient/non-SCC, r5) | 48 | 13 [-2,1] | 3 |
| 110 | R→R | 6/8 | 2 | 4 | 40 (transient/non-SCC, r4) | 24 | 103 [-2,1] | 2 |
| 113 | R→L | 4/8 | 4 | 3 | 49 (B2, r2) | 15 | 82 [-1,0] | 1 |
| 117 | R→R | 5/9 | 4 | 1 | 71 (B1, r2) | 10 | 218 [-3,1] | 1 |
| 119 | R→R | 4/9 | 5 | 9 | 67 (B2, r2) | 51 | 8 [-3,1] | 2 |
| 120 | R→L | 7/9 | 2 | 9 | 45 (transient/non-SCC, r3) | 11 | 212 [0,0] | 1 |
| 124 | L→R | 5/9 | 4 | 4 | 66 (B2, r2) | 11 | 248 [-3,1] | 2 |
| 133 | R→L | 5/9 | 4 | 22 | 21 (B2, r2) | 35 | 57 [-1,0] | 1 |
| 144 | L→L | 4/9 | 5 | 1 | 17 (B2, r2) | 43 | 187 [0,0] | 1 |
| 149 | R→R | 7/9 | 2 | 8 | 49 (B2, r2) | 15 | 103 [-2,1] | 2 |
| 151 | R→L | 8/9 | 1 | 5 | 2 (transient/non-SCC, r7) | 7 | 32 [-1,0] | 2 |
| 161 | L→L | 4/9 | 5 | 23 | 51 (B2, r2) | 17 | 132 [-1,0] | 1 |
| 163 | L→L | 6/9 | 3 | 11 | 72 (B1, r2) | 38 | 207 [-1,0] | 2 |
| 177 | R→R | 6/9 | 3 | 26 | 20 (B2, r2) | 34 | 42 [-2,0] | 2 |
| 181 | R→L | 3/9 | 6 | 10 | 68 (B2, r2) | 7 | 32 [-1,0] | 1 |
| 191 | L→L | 5/10 | 5 | 2 | 183 (B1, r2) | 62 | 207 [-1,0] | 2 |
| 208 | R→L | 5/10 | 5 | 9 | 19 (B2, r2) | 33 | 7 [-1,0] | 1 |
| 228 | L→R | 8/10 | 2 | 11 | 16 (B2, r2) | 3 | 192 [-2,0] | 2 |
| 233 | R→R | 8/10 | 2 | 31 | 44 (transient/non-SCC, r3) | 46 | 223 [-2,1] | 3 |
| 235 | R→R | 9/10 | 1 | 18 | 5 (transient/non-SCC, r8) | 22 | 132 [-2,0] | 4 |
| 236 | R→L | 10/10 | 0 | 20 | 0 (transient/non-SCC, r66) | 20 | 132 [-1,0] | 18 |
| 241 | R→R | 7/10 | 3 | 4 | 129 (B5, r2) | 8 | 73 [-2,1] | 2 |
| 282 | L→L | 8/10 | 2 | 8 | 38 (B3, r4) | 1 | 32 [-1,0] | 2 |
| 297 | R→R | 7/10 | 3 | 15 | 102 (B2, r2) | 41 | 77 [-1,0] | 2 |
| 310 | R→R | 7/10 | 3 | 19 | 65 (B2, r2) | 46 | 223 [-2,1] | 2 |
| 324 | R→L | 4/10 | 6 | 51 | 183 (B1, r2) | 47 | 212 [0,0] | 2 |
| 335 | R→R | 7/10 | 3 | 10 | 17 (B2, r2) | 4 | 222 [-2,0] | 2 |
| 344 | L→R | 6/10 | 4 | 16 | 132 (transient/non-SCC, r2) | 47 | 253 [-2,1] | 2 |
| 352 | R→L | 7/10 | 3 | 11 | 11 (B1, r2) | 40 | 37 [0,0] | 2 |
| 367 | L→R | 6/10 | 4 | 11 | 32 (B5, r2) | 16 | 133 [-2,1] | 2 |
| 368 | R→R | 4/10 | 6 | 5 | 13 (B2, r2) | 21 | 102 [-2,0] | 2 |
| 385 | R→L | 8/10 | 2 | 27 | 50 (B2, r2) | 19 | 107 [-1,0] | 1 |
| 425 | R→R | 5/10 | 5 | 26 | 71 (B1, r2) | 37 | 218 [-3,1] | 1 |
| 442 | R→R | 5/11 | 6 | 21 | 110 (B2, r2) | 55 | 137 [-1,0] | 2 |
| 444 | R→L | 6/11 | 5 | 7 | 129 (B5, r2) | 35 | 57 [-1,0] | 1 |
| 456 | L→R | 7/11 | 4 | 5 | 20 (B2, r2) | 34 | 42 [-2,0] | 2 |
| 563 | R→L | 4/11 | 7 | 6 | 58 (transient/non-SCC, r2) | 21 | 87 [0,0] | 1 |
| 570 | L→R | 8/11 | 3 | 2 | 72 (B1, r2) | 38 | 248 [-3,1] | 1 |
| 652 | R→R | 6/12 | 6 | 8 | 21 (B2, r2) | 35 | 72 [-2,0] | 2 |
| 705 | L→R | 7/12 | 5 | 1 | 67 (B2, r2) | 6 | 13 [-2,1] | 2 |
| 761 | R→L | 9/12 | 3 | 8 | 60 (transient/non-SCC, r2) | 26 | 137 [0,0] | 1 |
| 763 | R→L | 10/12 | 2 | 9 | 51 (B2, r2) | 17 | 132 [-1,0] | 1 |
| 1095 | L→R | 9/12 | 3 | 4 | 50 (B2, r2) | 16 | 133 [-2,1] | 2 |
| 1347 | R→L | 5/12 | 7 | 27 | 69 (B2, r2) | 53 | 57 [-1,0] | 1 |
| 2248 | R→R | 8/14 | 6 | 17 | 20 (B2, r2) | 1 | 47 [-1,0] | 2 |
| 3873 | R→R | 8/14 | 6 | 30 | 64 (B2, r2) | 45 | 193 [-2,1] | 2 |
| 5579 | R→L | 6/15 | 9 | 0 | 189 (B1, r2) | 59 | 62 [0,0] | 2 |
| 8539 | R→R | 10/16 | 6 | 15 | 66 (B2, r2) | 47 | 253 [-2,1] | 2 |

Full machine-readable rows, including the complete active projection sets and end-state records, are in `ExactSeedCarry84.json`.
