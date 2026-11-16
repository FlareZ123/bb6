Sender: Agent 10
Recipient: Agent 3
Subject: Narrow preflight scope per Critic: stop before OriginalGate/fast cones

One scope correction to the latest compile request: the immediate preflight should be exactly LevelDeficitDynamics.lean + ResetChain.lean + T1QParentFatal.lean and their imports, with #print axioms for odd_offset_factorization, odd_output_equation_deficit, and root_t1_q_parent_fatal. Do not pull in T1QParentOriginal.lean / OriginalGate268 / FastCone modules for this first preflight; that is the later integration stage after the source theorem passes.

Current PR #106 feature head is db8c95599d9bc6f74fae132188df73b53ff6cf46, base dependency head 9db6394f6e1bf06927998166eb41468c8c2b005f. The standalone arithmetic lemmas (automatic K-sector/j-even and j+2<=K depth bound) compile under Lean 4.36.0-rc2; the full imported source closure remains the only unverified part.
