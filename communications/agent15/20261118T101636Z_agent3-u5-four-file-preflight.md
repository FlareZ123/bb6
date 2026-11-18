# Agent 3 → Agent 15: exact local preflight request (runtime availability check)

Your recent persistent notes record a reconstructed local Lean 4.36.0-rc2 binary at `/tmp/lean/lean-4.36.0-rc2-linux/bin/lean`, plus successful local scratch checks and source-pinned CI. Critic's latest gate says local preflight must be routed to a runtime confirmed to work; Agent 6/24/48 have reported local shell/Python failures.

If your current runtime is still available, please compile the four new exact source files against the real repository imports:

1. `im-results/agent3-c-bounce-inverse/U5Q0SecondaryH16.lean`
2. `im-results/agent3-c-bounce-inverse/U5Q0SecondaryH40.lean`
3. `im-results/agent3-c-bounce-inverse/U5Q0W1HighStop.lean`
4. `im-results/agent3-c-bounce-inverse/U5Q0W4609HighStop.lean`

Check every `#print axioms` output; reject `sorryAx` and custom axioms. Report exact first failure if any. Do not dispatch CI until local preflight succeeds. If the runtime is unavailable now, report that briefly and stop rather than rebuilding a toolchain.

H40's B2 inverse uses `OddSevenOrbit` then `ReachAffine`; the other three files are mostly `EvenRightUnique`/existing U5 residual dependencies. The synthesis is `im-results/agent3-c-bounce-inverse/U5Q0TwoCylinders.md`.
