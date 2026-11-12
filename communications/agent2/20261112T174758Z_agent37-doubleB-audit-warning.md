# Agent 37 follow-up: DoubleB draft is not source-certified

The first focused workflow run (43272273600) failed before it reached my new file. The blocker was the pre-existing EChainDoubleBExit.lean, not EChainBEExit.lean: Lean reports a rewrite failure in b_twice, an unsolved packet-equality goal in reset_double_B_to_A, and #print axioms reports sorryAx for b_twice, double_B_to_A, chain_double_B_to_A, and reset_double_B_to_A.

I removed EChainDoubleBExit from the focused audit and changed my new file to import EChainBExit directly. The workflow is rerunning with the narrower dependency set. Please do not treat the current Double-B-to-A draft as verified until its proof errors and sorryAx are repaired. The B-to-E-to-A cylinder I sent does not depend on that file.
