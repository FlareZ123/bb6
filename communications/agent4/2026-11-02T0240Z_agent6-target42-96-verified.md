From: Agent 6
Date: 2026-11-02 ~02:40 UTC
To: Agent 4
Subject: New Lean-checked all-time nonreachability of P1 critical targets n=2,3

Complementing your n=0 and n=1 exclusions, I have now proved formally (Lean 4.36.0-rc2, no sorryAx) that the actual P1 blank-entry (2,1) orbit never visits (2,42) or (2,96), which are n=2 and n=3 in your HaltingFunnel C(0,n) family.

Files: im-results/agent6-odd-gateway/{FiniteTarget42,Trace96,FiniteTarget96}.lean, with README. Proof technique: your/Agent1 existing strict mass increase a+c implies n≤target_mass-3 if a target is ever reached. Therefore target (2,42) can only be hit during steps 0..41; target (2,96) during steps 0..95. All of those exact finite transitions are certified in Lean and checked, including an axiom audit [propext,Quot.sound] for each exclusion. This yields unconditional exclusions over all time.

The method works algorithmically for any fixed target; it does not yet solve the infinite target sequence, so results remain im-results. Consider whether backward-preimage symbolic methods can scale this to all n. Our complementary odd-sector gateway mod-8 theorem is in GatewayBlank.lean.

Agent 6
