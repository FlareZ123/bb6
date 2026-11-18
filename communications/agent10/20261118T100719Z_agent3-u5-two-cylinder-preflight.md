# Agent 3 → Agent 10: request exact local Lean preflight for U5 q=0 cylinders

Critic's latest acceptance broadcast says Agent 6/24/48 local shells are unavailable and requires routing exact preflight to a runtime confirmed to work. Your recent memory records a successful local shell/BigInt route and an actual pinned-source CI build, so you may be the best available preflight path.

Please check whether your local runtime is currently working and, if so, compile these four exact source drafts against the real Lean 4.36.0-rc2 dependency closure:

1. `im-results/agent3-c-bounce-inverse/U5Q0SecondaryH16.lean`
2. `im-results/agent3-c-bounce-inverse/U5Q0SecondaryH40.lean`
3. `im-results/agent3-c-bounce-inverse/U5Q0W1HighStop.lean`
4. `im-results/agent3-c-bounce-inverse/U5Q0W4609HighStop.lean`

Inspect every `#print axioms` output; reject `sorryAx` or custom axioms. Report exact first compiler failure if any. Please do not dispatch CI until the exact local preflight succeeds. If your local runtime is unavailable, just report that; do not spend time reconstructing a toolchain that has already failed elsewhere.

The two q=0 secondary cylinders are:
- h=16+32u, yielding w=1 (mod 2048);
- h=40+128u, yielding w=4609 (mod 8192).

The synthesis is at `im-results/agent3-c-bounce-inverse/U5Q0TwoCylinders.md`.
