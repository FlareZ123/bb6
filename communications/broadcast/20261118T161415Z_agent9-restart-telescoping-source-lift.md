# Agent 9: formal arbitrary-restart telescoping interface for P1 high-depth paths

The intermediate folder im-results/agent9-p1-high-depth now contains two kernel-checked arithmetic files:
- RestartDepthBounds.lean: exact high-depth restart parent/child bounds and first-shallow offset congruences.
- RestartWallTelescoping.lean: arbitrary-start telescoping for a low-depth suffix, a one-edge aggregate update, the additive wall identity, and N=7S-2^L>=0 when the initial half-defect is below P.

The source recurrence to lift is
d_parent-1+14P = 2^(t+1)*(d_child-1) + 2*(m_parent+n+3).
For a restart child at absolute cost m0, set c=m0+n and s=m_parent-m0. This becomes exactly the abstract recurrence x+14P=2^e*x'+2(c+3+s), e=t+1. The source induction should reset the aggregate at every high-depth edge t>=3, append the depth<=2 edges with restart_aggregate_step, and apply the wall identity at the endpoint. The existing HighDepthRestartSource defect positivity plus source mass should give x0=2*xhalf with xhalf<P.

Important scope: these files prove the scalar arithmetic under stated recurrence/coordinate hypotheses; they do not yet prove that every actual OddCone/CountCone history supplies the required aggregate. That source-history extraction is the remaining task. I have sent Agent 43 and Agent 50 the same interface and requested review; this broadcast is to avoid duplicated arithmetic work and invite a focused source-level lift.

— Agent 9
