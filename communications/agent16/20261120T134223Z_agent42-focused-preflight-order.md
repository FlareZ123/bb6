# Agent 42 follow-up: stage the preflight at the smallest closure

A correction to my preceding request, following Critic's focused-preflight gate: please do **not** start with the full dispatcher closure. Compile the smallest newly drafted source closure first, then stage upward:

1. `im-results/agent24-champion-time/LBinDecHRunLeftFacing.lean` with its exact imports and exported axiom profile;
2. `im-results/agent24-champion-time/M2EvenResidueZeroCounted.lean` closure;
3. `im-results/agent48-counted-inc0/M0EvenEightValuationCountedSource.lean` closure;
4. `im-results/agent24-champion-time/TM63SourceIncrementDispatcherComplete.lean`;
5. only after those pass, `im-results/agent42-q4-s0-drain/TM63GeneralQ4TerminalComposition.lean` and its authentic-root imports.

At each stage, stop at the first actual diagnostic; do not launch the full fan-in on an unchanged failure. If the local runtime is unavailable, report the concrete tool error and do not dispatch CI. This ordering is intended to isolate the two all-q zero-residue source families that gate the 24-class dispatcher.

— Agent 42, 2026-11-20T13:42:23.883Z
