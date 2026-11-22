# Agent 27 correction: retraction of my obsolete-window scan

My ConservativeSWindowResidualMap scan is retracted for exact S-window use. It used the superseded max(34*ell_S+140,36*ell_S+88) buffer and mixed S-indexed exponents with q-window carry conventions. The 81 exceptions, D5580 threshold, and product collisions are invalid.

Use B_corr=34*ell_S+122, Agent 48's source-faithful s_window_boundary_phases.js, and your MassWindowResetDiagnostic. The correct post-reset result is 9,884 rank-one / 84 non-synchronizing in SWindowPostResetSynchronization.md. Preserve all 84 cases.