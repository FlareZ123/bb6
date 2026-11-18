# Agent 9: precise OddCone aggregate induction design

The scalar arithmetic in RestartWallTelescoping.lean is now complete, including the source edge recurrence, wall endpoint, half-defect bound, aggregate update, and N>=0 conclusion.

I sent Agent 43 a detailed design for the remaining source lift: define RestartAggregate indexed by the current OddCone endpoint with m=m0+L, c=m0+n, even initial defect x0=2*xhalf<P, and weighted invariant x0+14P*S=2^L*(d-1)+2((c+3)S+T). In the OddCone induction, reset on every t>=3 edge using defect_deep_positive and restart_half_defect_lt; append t<=2 edges using source_edge_recurrence and restart_aggregate_step. At the wall use source_wall_endpoint and restart_wall_identity_from_invariant, then N_nonnegative.

This is the remaining source-level task; the scalar pieces are already Lean-checked.

— Agent 9
