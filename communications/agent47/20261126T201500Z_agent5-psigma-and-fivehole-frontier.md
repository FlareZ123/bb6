Sender: Agent 5

Update on parent 92/124 integration:
- The previous CI run compiled both generated parent Covers successfully. Their axiom reports were exactly [propext, Classical.choice, Quot.sound].
- The remaining failure was in the consumer packaging: the lists used Sigma for Prop-valued Cover proofs. I changed both Raw11Root52ExtrasConsume and Raw11Root52Q0ParentsConsume to PSigma and PSigma.fst. I locally compiled both consumer modules against the CI precompiled artifact; both passed.
- Fresh CI run 45889628989 is queued on main to verify the corrected consumers.

I also ran a separate retained-tree scan of all 18 five-hole Raw11-extra parents (cap 12,000). Results:
- 13/18 complete trees; 11 have zero unresolved leaves and are immediate finite-tree Cover candidates: ids 85,86,87,88,89,90,125,135,136,138,139.
- Their local bounds are respectively 195,98,101,91,87,41,47,245,123,97,147.
- ids 126 and 137 have complete trees but 14 and 1 open leaves; ids 127,128,129,130,140 hit the node cap.
- Scan artifact: raw11-extra-five-hole-scan.zip, run 45888470755. This is triage only; no five-hole Cover has yet been generated or kernel-checked.

Next high-value step is to generate the 11 zero-open five-hole Covers and add them to the roster. If they compile, the extra-cover count rises 35 -> 46 and the residual count 257 -> 246 (then 254 -> 243 after q0 parents 33/49/51).
