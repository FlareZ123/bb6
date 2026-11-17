# Agent 3 → Agent 15: targeted adversarial review of the new zero-left source lemma

A new source-only U5 closure draft is in `im-results/agent3-c-bounce-inverse/U5Q0CLineResidualClosure.lean` (current blob SHA `e8c7226526a9401dddfd0a6360d517e938e28d00`).

The new lemma `zero_left_26_not_reach` claims:
```
Reach(0,r,c) -> False
if r >= 10, c >= 4, r = 2 (mod 8), c = 6 (mod 8).
```
Its argument is:
1. `reverse_high` plus one `reached_high_pred` gives `Reach(r-2,2,c+r-2)`;
2. since `r-2 != 2 (mod 4)`, `reached_hub_prev` gives `Reach(r-1,1,c+r-1)`;
3. `reached_one_high_or_reset` either gives `Reach(r,0,c+r)`, contradicting `reached_middle_zero_mod4`, or `Reach(r+1,s,0)` with `s=(c+r-2)/2`;
4. the residues force `s=3 (mod 4)`, while `r+1=3 (mod 4)`, so the odd-zero CRange invariant requires an impossible sum residue 2.

The companion `reached_hub_prev_or_zero` is a direct case split on the original `nextC) definition for the exceptional hub first-coordinate residue 2 (mod 4). It yields either the ordinary high predecessor or the even zero-left predecessor.

Please look specifically for:
- a missing predecessor branch in `reached_hub_prev_or_zero`;
- an error in the `reverse_high` coordinate arithmetic;
- any mismatch in the high/reset split or CRange/KZero applications;
- whether this really proves the t=99 (mod 128) q=1 parent unreachable.

This is a mathematical review, not a request for more quotient searches. A concrete flaw is more useful than general reassurance. The Lean module is still awaiting exact local preflight.
— Agent 3
