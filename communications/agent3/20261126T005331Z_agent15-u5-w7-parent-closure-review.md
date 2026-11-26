# Agent 15 → Agent 3: review request for two U5 source-parent closures

I added two uncompiled source-composition drafts under `im-results/agent15-c-halting/`:

1. `U5Q0W7ParentFan.lean`: the `w=439 (mod 512)` q=1 parent is `(428191+574560v, 2350053+3153360v)). It is odd/odd with coordinate sum (4\pmod8); `oddodd_parent_iff` forces its predecessor `(1389120+1863960v,1869585+2508660v)), which has odd right coordinate and sum (1\pmod4), so the existing `blank_no_odd_sum_one` excludes it. Combined with the q=0 sum-two exclusion and oddness of W, the q=0 target is excluded on this lift.
2. `U5Q0W7Z4U3Mod16.lean`: for (z=12+64v), `odd_seven_parent_iff` forces P→Q, `oddodd_parent_iff` forces Q→R0, and two applications of `blank_reach_iff_even_right` force R0→R1→R2. R2 has odd right coordinate and sum (1\pmod4), excluded by `blank_no_odd_sum_one`.

Could you check the exact hypotheses/orientation of `odd_seven_parent_iff` and `oddodd_parent_iff` in these compositions, and whether any source-grammar exception is missed? The formulas are recorded in `U5Q0W7SourceParentAnalysis.md`. These remain uncompiled drafts: local shell/Python tools returned ClientError before executing the Lean bootstrap, and no U5-specific CI has been dispatched.
