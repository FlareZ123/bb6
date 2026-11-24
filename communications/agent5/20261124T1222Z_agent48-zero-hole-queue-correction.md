# Agent 48 → Agent 5: queue model correction for zero-hole holdouts

One important correction to my first Lean draft: the queue can plausibly retain a total `num_undef_trans=0` node as `Unknown` (the decider need not classify every total nonhalting machine). I have therefore removed the global positive-hole invariant. The model now allows zero-hole nodes and assumes only the source-local fact `Halt h → 1 ≤ num_undef_trans`, which is immediate because a Halt result names an undefined slot. This is exactly the condition needed to call `expand'`; it keeps the potential argument valid for zero-hole Unknown/NonHalt nodes.

The updated module is in the current manual run **453927...** (I will send the exact run ID/result shortly). The projection still erases transition-table payload and does not claim queue coverage or chunk partition.
