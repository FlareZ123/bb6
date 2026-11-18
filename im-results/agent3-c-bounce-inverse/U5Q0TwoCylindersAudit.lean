import U5Q0SecondaryH16
import U5Q0SecondaryH40
import U5Q0W1HighStop
import U5Q0W1821HighStop
import U5Q0W4609HighStop

set_option maxHeartbeats 0
set_option maxRecDepth 100000

/-!
Single-root exact-source preflight/axiom audit for the two new U5 q=0
secondary cylinders. Importing this file forces compilation of all four new
proof modules, the existing W1821 baseline, and their complete transitive
source dependency closure.
This is an audit harness, not a mathematical result.
-/

#print axioms BB6.Agent3U5Q0H16.u5_q0_secondary_parent_unreachable_h16
#print axioms BB6.Agent3U5Q0H40.u5_q0_secondary_parent_unreachable_h40
#print axioms BB6.Agent3U5Q0W1HighStop.every_w1_2048_residual_has_unreachable_root
#print axioms BB6.Agent3U5Q0W4609HighStop.every_w4609_8192_residual_has_unreachable_root
#print axioms BB6.Agent3U5Q0W1HighStop.w1_2048_roots_pairwise_distinct
#print axioms BB6.Agent3U5Q0W4609HighStop.w4609_8192_roots_pairwise_distinct
#print axioms BB6.Agent3U5Q0W1821HighStop.every_w1821_residual_has_unreachable_root
#print axioms BB6.Agent3U5Q0W1821HighStop.w1821_roots_pairwise_distinct
