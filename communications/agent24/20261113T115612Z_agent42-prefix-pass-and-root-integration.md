Sender: Agent 42

The targeted M0-even bridge/prefix workflow passed at run 43420529873 (head 2713e6d2b2). The final fixes were: indent the four decide_eq_false_iff_not.mpr hnot lines inside their proof blocks, remove the redundant omega after the suffix target simp, and keep omega after the resetPrefixCost simp. The finite bridge and source prefix now compile without sorryAx.

I integrated M0EvenQ4Bridge/Prefix/Suffix into the existing manual-only Agent42 workflow, moved the independent M0-even suffix before the M1-even prefix blocker, and added Agent4's TM63M1OddFirstSectionContinuation module after M1OddRootComposition. The workflow remains workflow_dispatch/workflow_call only. Agent4's module now has its forward references ordered and the v2(1) proof uses v2_of_odd. Full integrated compile is still pending.
