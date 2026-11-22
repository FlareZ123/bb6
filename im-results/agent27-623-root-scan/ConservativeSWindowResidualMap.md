# Conservative S-window residual synchronization map

**Status:** exact finite computation on the scanned root orbit only. It is not an all-time invariant and does not prove BB(6).

## Setup

The scan starts from the repository's root orbit (D(0,7)) and examines target states (D(34),\ldots,D(10001)), for 9,968 windows. For each state:

- (S=a+d), and \(\ell\) is least with \((3^\ell-1)/2\ge S+3\);
- conservative buffer \(B=\max(34\ell+140,36\ell+88)\);
- (k\) is least with \(3^k>B\), and (j\) least with \(3^j>B^3\);
- the digit-pair word is at positions (k+2,\ldots,j-3);
- the 263-state reset DFA locates the first common reset, and the 211-state image-subset DFA is applied to the suffix after that reset.

The generator independently computes the high-level root orbit and all windows. The 211-state transition table is the one whose 1,899 transitions were reconstructed exactly from the 66-state paired-carry closure in [`NonSynchronizingSCCs.md`](NonSynchronizingSCCs.md).

## Main finite result

<badge color="success">Finite scan: 9,968 windows</badge>

The post-reset suffix rank distribution is:

| Image rank | Windows |
|---:|---:|
| 1 | 9,887 |
| 2 | 57 |
| 3 | 11 |
| 4 | 5 |
| 5 | 1 |
| 7 | 1 |
| 8 | 3 |
| 66 | 3 |

There are **81 nonsynchronizing suffixes**, and the last occurs at (D(5580)). Every one of the next **4,421** windows, (D(5581),\ldots,D(10001)), has rank one. In this finite run, the subset automaton reaches a singleton within at most **11 symbols after the first reset**.

The 81 exceptional indices are:

```
34, 35, 36, 37, 38, 39, 41, 42, 43, 44, 45, 46, 49, 51, 52,
56, 58, 63, 65, 67, 70, 73, 77, 78, 80, 81, 83, 84, 85, 89,
91, 93, 94, 95, 96, 97, 110, 111, 114, 118, 120, 121, 125,
134, 145, 150, 152, 162, 164, 178, 192, 209, 229, 234, 236,
237, 242, 283, 284, 298, 311, 325, 336, 345, 353, 368, 369,
386, 443, 445, 457, 564, 571, 653, 706, 762, 764, 1096, 2249,
3874, 5580
```

Their terminal subset states lie in only five of the ten recurrent nonsynchronizing SCCs from the companion decomposition, plus transient states:

| Terminal component | Exceptional windows |
|---|---:|
| B1 | 12 |
| B2 | 33 |
| B3 | 1 |
| B5 | 7 |
| B7 | 6 |
| Transient | 22 |

No scanned exceptional window ends in B4, B6, B8, B9, or B10. Of the 81 exceptions, 18 have singleton projection on the root's active branch; 63 do not. Thirteen are ambiguous on both L and R projections.

The first-reset end-position histogram is (3:2196,4:4210,5:2241,6:866,7:290,8:105,9:37,10:14,11:6,12:3).

## How close are the post-5580 cases?

For (D(5581),\ldots,D(10001)), the first position at which the post-reset subset becomes a singleton has this distribution:

| Symbols after reset | Windows |
|---:|---:|
| 2 | 695 |
| 3 | 2,056 |
| 4 | 1,076 |
| 5 | 373 |
| 6 | 143 |
| 7 | 54 |
| 8 | 16 |
| 9 | 3 |
| 10 | 2 |
| 11 | 3 |

The three depth-11 cases are (D(5586),D(6597),D(9475)). Their post-reset symbol-ID suffixes (encoding (3x+y)) are:

- (D(5586)): `0,4,0,6,2,1,3,4,2,1,0`
- (D(6597)): `0,3,5,7,4,8,0,5,8,1,6,5`
- (D(9475)): `1,0,8,4,8,1,0,6,2,0,3,5`

These are useful adversarial cases for any proposed short synchronizing-factor lemma. The B2 30-state component is the dominant obstruction in the longest paths.

## Phase coupling: important negative result

The finite phase calculations agree with the existing own-start diagnostic on **697 distinct target-own-start phase keys**. However, phase alone is insufficient: 72 of those keys occur with more than one terminal subset rank, and 535 phase keys appear on both sides of the (D(5580)/D(5581)) threshold.

Across the 9,968 source-to-target edges, the exact source-to-target phase and the target's own-start phase differ on 9,740 edges. The low/high window shift counts are ((0,0):9955,(0,1):8,(1,1):5), and the source transducer's digit output agrees with the target coordinates on all scanned positions.

Do not update the 211-state residual subset by appending only the high-extension symbol. The overlapping word is transformed by the source-to-target carry transducer; the full transducer output must be composed with the reset recognizer and residual-subset machine. The source-to-target carry and target-own-start carry are distinct state variables.

## Interpretation and next proof obligation

This finite run suggests a sharp transition: after (D(5580)), every scanned conservative S-window suffix synchronizes, and does so within 11 post-reset symbols. It is not yet a proof that this persists for all future root states. The 697 own-start phases do not by themselves determine the residual rank, so an all-time proof must retain more than the own-start phase—at minimum the exact source-to-target transducer state and the reset/subset residual.

The ten-SCC reduction in [`NonSynchronizingSCCs.md`](NonSynchronizingSCCs.md) makes the remaining obstruction concrete: prove that no future post-reset suffix can remain in B1/B2/B3/B5/B7 to the high boundary, with particular attention to the three depth-11 B2-heavy cases. The other five recurrent SCCs are absent from this finite root trace, but their absence is not yet proved globally.

## Reproduction

From the repository root:

```sh
node im-results/agent27-623-root-scan/analyze_conservative_s_window_residuals.js
```

The script writes [`ConservativeSWindowResidualMap.json`](ConservativeSWindowResidualMap.json), including all 81 exceptional windows and the post-5580 synchronization-depth histogram.
