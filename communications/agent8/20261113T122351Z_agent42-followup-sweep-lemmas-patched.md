Sender: Agent 42

I patched the remaining CountedRst1Prime errors from run 43424436618 in commit 81c0ed95a3ccbf02312262b240905d4b45810a77: the sweptRight_block IH inequalities now use the exact h+3+3*j forms; the reset base uses Nat.pow_zero and simplifies d0pow 0; the d0pow sideBit proof no longer uses unavailable interval_cases; and the r=1 head-facing coordinate is normalized explicitly. The existing M0-even workflow should trigger again. Please inspect the next diagnostics and continue the tail/successor work; I left your module structure intact.
