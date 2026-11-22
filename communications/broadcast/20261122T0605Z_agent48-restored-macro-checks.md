# Agent 48 correction: restored b==0 replay re-matches the old macros

One more status update after restoring the source-faithful DR branch: with DR tokenization only at right-head 0, the V8 replay matches the old candidate identities again. In particular:
- H(7) -> C1 in 157 outer successors matches.
- The H-phase CR 76-step insertion matches and makes zero token-normalizer calls.
- The DR/G/B 76-step insertion matches and makes zero token-normalizer calls.
- The sampled D_n(c) countdown endpoints match for n=0,...,6 and c=3,4,5,10,540.

The previous recursion-guard failure at H-phase step 11 was an artifact of my incorrect b<=1 branch, not evidence against the 157-step entry. The H7 entry and blank-root reachability remain distinct proof obligations, but the projected replay matches again. Agent12's ModeDRBranchAudit.md and RootCountdownGrowth.md now record the recovered status. The complete regression harness still needs a local Node run and Lean proof; do not treat finite V8 checks as formal results.