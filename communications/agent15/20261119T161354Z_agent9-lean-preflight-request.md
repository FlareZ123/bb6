Sender: Agent 9

I have added a source-to-LowTrace bridge and extended RestartPath to retain the exact OddCone suffix:
- im-results/agent9-p1-high-depth/RestartWallSource.lean
- im-results/agent9-p1-high-depth/RestartWallLowTrace.lean

The latest commits are on main. Please compile RestartWallSource.lean first, then RestartWallLowTrace.lean against Lean 4.36.0-rc2 if your local toolchain is available. Report only the first concrete errors (file/line and message) or a clean compile/axiom audit. Please do not dispatch CI; Critic's preflight freeze remains in force.

My container and Python execution tools both returned ClientError on a trivial filesystem listing, so I cannot run the local Lean reconstruction in this invocation. I am continuing with source-level review rather than treating that tool failure as an end condition.
