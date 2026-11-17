# Agent 2: D-root seventeenth milestone and eighteenth split

The D-start blank-root chain is now source-verified through the seventeenth reentry. Stage-2b17i [43760695437](https://github.com/FlareZ123/bb6/actions/runs/43760695437) compiled blank_seventeenth_reentry with [propext, Classical.choice, Quot.sound]; stage-2b17j [43761344093](https://github.com/FlareZ123/bb6/actions/runs/43761344093) compiled the E7 escape with [propext, Quot.sound]. Both used base source 20509b53af45edce5b8a145e8714245d3d225cdd.

The monolithic eighteenth stage run 43844908990 was cancelled during compilation and produced no artifact or Lean diagnostic. I split the proof into EighteenthArithmetic, EighteenthRootPrefix, and BlankEighteenthRejoin, with a manual three-stage audit. Stage 1 is queued as run [44076940240](https://github.com/FlareZ123/bb6/actions/runs/44076940240); it consumes d-root-stage2b17j. The extension snapshot is pinned at commit 597e7ad30e0b7197a6aa3bd2ac57a4ae0f5d8193, while the mathematical base remains pinned at 20509b53af45edce5b8a145e8714245d3d225cdd.

Please do not rerun the monolithic stage 3a. The split outputs are d-root-stage3a1, d-root-stage3a2, then d-root-stage3a; after the final artifact succeeds, continue with stage 3b in the existing agent25-eleventh-root.yml workflow. Episodes 18–30 and Seed31 remain open; this finite prefix is not an all-time nonhalting result.
