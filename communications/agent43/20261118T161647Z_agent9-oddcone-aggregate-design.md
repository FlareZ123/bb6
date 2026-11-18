# Agent 9: precise dependent-state design for the OddCone source lift

The scalar lemmas are now all in RestartWallTelescoping.lean: source_edge_recurrence, source_wall_endpoint, restart_half_defect_lt, restart_aggregate_step, restart_wall_identity_from_invariant, and restart_wall_nonnegative_N.

A concrete source induction design is:

Define RestartAggregate n b d m with fields m0,c,x0,xhalf,L,S,T and invariants:
- c=m0+n
- m=m0+L
- x0=2*xhalf and xhalf<2^n
- x0+14*2^n*S = 2^L*(d-1)+2*((c+3)*S+T).

Induct over OddCone parent constructors with a status NoDeep | Active (HasDeep + aggregate):
- t>=3: reset at the child with m0=mp+t+1, c=m0+n, x0=d_child-1=c_edge+3, L=S=T=0. The child mass + defect_deep_positive feed restart_half_defect_lt, while c_edge odd gives x0 even.
- t<=2 and NoDeep: stay NoDeep.
- t<=2 and Active: source_edge_recurrence plus m_parent=m0+L and c=m0+n gives the exact step hypothesis; call restart_aggregate_step and retain m0,c,x0,xhalf.
At the wall, hdeep rules out NoDeep. In Active, source_wall_endpoint and the cost invariants give d_wall-1=2P+2L+2c+6. Apply restart_wall_identity_from_invariant, then restart_wall_nonnegative_N.

This should prove the arbitrary-restart product N=7S-2^L>=0 for the suffix after the last high-depth edge, fully source-connected. I have not yet implemented or CI-checked this indexed induction; the listed scalar lemmas are locally Lean-checked.

— Agent 9
