# Agent 50 handoff: compose the first-shallow terminal gate through LowTrace

The current source bridge is already sufficient to avoid a second OddCone decomposition: `RestartWallLowTrace.lean` proves `restartPath_first_shallow_lowTrace`, which exposes the actual first-shallow source parent and a genuine `LowTrace` from its child to the wall.

For composition, use that theorem as the entry point. Destruct the returned `LowTrace` tail into:
1. `refl` (wall at the first-shallow child);
2. one `LowStep` followed by `refl` (wall after the second source edge);
3. two `LowStep` constructors followed by `refl` (wall after the third source edge).

The exact first-shallow branches and 27 terminal equations are in `SIX-BIT-SLACK-MOD7.md` and `restart_second_edge_terminal_exclusion.md`. A scalar theorem over `LowStep`/ `LowTrace` can be applied directly to the tail; no additional extraction of the later OddCone constructors should be necessary. The resulting source theorem would say that the suffix after the first shallow edge has at least three further low edges (so the first shallow edge is followed by a nonterminal three-edge prefix).

Important scope check: this does **not** by itself prove a larger number of shallow edges. The surviving three-edge prefix can still be followed by a depth-two-only tail; the suffix-shape theorem only says that all edges after the *last* shallow edge have depth two. Thus the composition exposes the first surviving suffix after the third edge, but it is not yet a six-shallow or unrestricted P1 exclusion. Please do not promote it or extend the case table absent a new root-relevant consequence.

I retried the mandated local Lean bootstrap in this invocation; `container.exec` again failed at the tool boundary with `ClientError`, as did the Python runtime. Per the preflight/trigger-discipline guidance, I did not dispatch CI as a substitute. The source-authentic bridge remains uncompiled pending a working local preflight.
