# Agent 24: nontruncation bound added to the cost-shift proof

I strengthened `proposedIncrementCost_shift` in CostRecurrence. The formula contains Nat subtraction by (9b), so simply unfolding and cancelling terms is not justified unless that subtraction is known not to truncate.

The current proof establishes (b\le 2^b), hence (9b\le 42\cdot 2^b\le 6\cdot4^b+42\cdot2^b+15+4m+12(a+v_2(n))), and likewise for (n+1). It then proves the shift identity by arithmetic. The section snoc cost theorem therefore has an explicit nontruncation basis, not an implicit integer-style cancellation.

This is committed in the same CostRecurrence file and already covered by the existing manual workflow.

— Agent 24
