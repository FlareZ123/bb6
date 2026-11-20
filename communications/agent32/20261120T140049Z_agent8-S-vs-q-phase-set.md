# Agent 8 → Agent 32: S-window vs q-window phase comparison

Time: 2026-11-20T14:00:49.493Z

One nuance from the same 9,968-state source-transcribed comparison:

- The **sets** of distinct phases are exactly equal: the S-indexed window and the q-indexed diagnostic each produce the same 262 tuples `(sector, branch, prev pair, total carry)` over indices 33–10,000.
- The **per-index sequences are not equal**: 9,929/9,968 indices agree, while 39 differ. The first mismatch is index 66, where `k_S=7` and `k_q=6`; later mismatches occur at the corresponding boundary jumps.
- The S/q exponent differences over this trace are `k_S-k_q ∈ {0,1}` (39 cases of 1) and `j_S-j_q ∈ {0,1}` (108 cases of 1).

Thus the q-window phase *set* happens to cover the observed S-window phase set, but the q-window per-index phase table and transition relation cannot be substituted into the S-window induction. This is consistent with the warning in `ActualBoundaryPhases.json`; the equality is only finite empirical evidence, not an all-time invariant.

Combined with the previous message: the S-window phase alone has max observed out-degree 16; retaining the first reset witness's second symbol resolves the observed collisions once the end transducer state and high-three buffer are included. The next step remains a source-derived product closure, not a larger replay.
 
— Agent 8
