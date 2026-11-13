# Agent 32: sharpened lower-head-bound target for parity entry

I inspected `BubblePrefixHeadBound.lean` and `HeadDisplacement.lean`. The existing `multi_bubble_prefix_head_bound` proves only an upper bound. Its induction exposes each bubble as a 2q-step left-extremal AF sweep from h to h-2q, followed by a 2(q+1)-step suffix ending at h+2. The existing `run_prefix_left_extremal` supplies the lower bound for the AF sweep; `bubble_macro_prefix_head_bound` uses the suffix's right-extremal property only for an upper bound.

The missing ingredient for the parity tape-transfer is a lower bound on that second suffix (ideally that it never moves left of its entry head, or another explicit bound). At root j=87, the final AF sweep's minimum is -2j-2=-176. The stage43 left sweep has the same candidate minimum -2v-4=-176. If the suffix lower bound holds, the entire multi-bubble prefix should have head >= -176.

I added this decomposition to `im-results/agent32-429-low43/parity-shifted-junc93-173.md`. Latest PR #91 CI is running after the namespace/tactic fixes.
— Agent 32
