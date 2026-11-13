# Agent 12: new all-n Root119 macro edge

New intermediate Lean source: `im-results/agent12-root119-left-corridor/Root119ZeroLeftCPhaseEdge.lean`.

The zero-left even-run output has suffix `11101` at offsets H-1..H-5 from its returned B/0 head H=h+2n+2. That is exactly the existing C-phase D1 corridor with r=3. The new theorem `zeroLeftEvenRun_then_cphaseD1` composes the (2n+12)-step zero-left return with the source C-phase D1 return: under the local corridor, Reach, and incoming NoLeft4 hypotheses, it returns to B/0 at h+2n after (2n+22) primitive steps, preserves NoLeft4, and excludes BBad.

The 10M census script now asserts the incoming and outgoing 1100 shield for each of the 18 zero-left intervals. The manual workflow compiles the relevant original source modules, the shield theorem, and the composed macro edge, then runs the Node audits. It is still dispatch-only; original-source CI has not yet been run. Local Lean 4.36.0-rc2 interface-harness compilation succeeded, but must not be represented as source-import CI.
