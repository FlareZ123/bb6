# S-window post-reset synchronization diagnostic

## Finite-trace result

On the existing 9,968 S-window transitions in s_window_boundary_phases.js (D33→D10001), I ran the buffer-relative reset recognizer to its first output, then fed the remaining suffix into the 41-state paired-carry synchronizing-language DFA.

The 41-state DFA's acceptance agrees **exactly** with rank-1 of the 475-state paired-carry transformation monoid for all 9,968 suffixes: 9,884 accepted, 84 rejected, zero mismatches.

The suffix transformation rank distribution is:

| Rank | Count |
|---:|---:|
| 1 | 9,884 |
| 2 | 61 |
| 3 | 10 |
| 4 | 5 |
| 5 | 1 |
| 7 | 1 |
| 8 | 3 |
| 66 | 3 |

The three rank-66 cases are empty post-reset suffixes. Every nonempty suffix in this trace has rank at most 8. The 84 nonsynchronizing suffixes are sparse but not confined to the initial prefix; their source transition indices are 33, 34, 35, 36, 37, 38, 40, 41, 42, 43, 44, 45, 48, 50, 51, 55, 57, 62, 64, 66, 69, 72, 76, 77, 79, 80, 82, 83, 84, 88, 90, 92, 93, 94, 95, 96, 109, 110, 113, 117, 119, 120, 124, 133, 144, 149, 151, 161, 163, 177, 181, 191, 208, 228, 233, 235, 236, 241, 282, 297, 310, 324, 335, 344, 352, 367, 368, 385, 425, 442, 444, 456, 563, 570, 652, 705, 761, 763, 1095, 1347, 2248, 3873, 5579, 8539.

## Interpretation

The 41-state DFA is sufficient to decide whether a post-reset suffix synchronizes all 66 paired-carry states; the full 475-state monoid is unnecessary when only that yes/no property is needed. For the 84 rejected cases, the 211-state image-subset automaton bounds the remaining uncertainty set (size at most 8 for every nonempty suffix).

This is a finite-trace computational result, not an all-time invariant. In particular, the 84 exceptions persist at scattered indices, so they cannot be dismissed as a finite initial prefix. The next step is to compose the 41-state recognizer and 211-state uncertainty automaton with the exact S-window shift/high-extension phase.
