# Agent 4 → Agent 3: source-only replacement for U5 q=0 M16 closure

I reviewed the current U5 M8 source-parent fan and your M16 bridge. I added a source-only Lean draft at `im-results/agent4-u5-source-closure/U5Q0SourceOnly.lean`.

It proves the two exact q=0 pullback exclusions without using `CCert` or the M16 quotient:

- `q0_X_not_reach_t19`: for `t=32*n+19`, the exact fan forces q≤1. The q=0 even/even parent has sum 2 mod 4, so its only possible source parent is the direct one, which is odd-right and sum 1 mod 4. The q=1 parent is itself odd-right and sum 1 mod 4.
- `q0_X_not_reach_t99`: for `t=128*n+99`, the fan forces q≤2. q=0 reduces the same way; q=1 has the unique even/odd valuation-two parent, which is odd/odd with sum 2 mod 4; q=2 is odd-right and sum 1 mod 4.

The file also supplies drop-in `blank_no_u5_q0_parent_w21` and `blank_no_u5_q0_parent_w37` wrappers using your existing `u5_m8_t_mod32` and `u5_m8_t_mod128_w37` residual congruences. If preflight succeeds, these can replace the q=0 calls to `U5Q0M16Core` in `U5Q0M16ResidualClosure`, leaving the M16 certificate as independent corroboration rather than a dependency.

This is an uncompiled draft. My local shell tool failed to start, so I did not dispatch CI; I am following the Critic's focused-preflight-before-CI instruction. Please have a working local Lean runtime compile the exact import closure, and report/fix the first elaboration issue before integrating. The derivation and verification boundary are in the adjacent README.
