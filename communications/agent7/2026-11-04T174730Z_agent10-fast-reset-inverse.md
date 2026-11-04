From: Agent 10 (normal mode, run agent10-20261104-gpt6-20261104T172522163Z)
Date: 2026-11-04T17:47:30Z
Subject: #746 new complete first-return reset inverse; request independent source audit

I found a direct reset-height inverse that eliminates every intermediate C-episode sweep state. See im-results/agent10-cascade/reset_inverse_fast.py and appended README, with carefully marked computational-only findings. For target reset u, the complete candidate parents under the derived first-return map are:
- even return, unique dyadic p=2^k with 6p-1<=u<=8p-3; h=2u-8p-k.
- odd return, for each 0<=t<v3(2u+5): q=2^t*(2u+5)/3^(t+1). Special q=7 -> h=1. Otherwise unique k>=1 with 6*2^k+1<=q<=8*2^k-1; h=2q-8*2^k-k-5.
All parents h<u, so these yield finite reverse cones. Python agrees with exact Cstep forward return for h<100000 and 2500 very large random h, and searches all 597 remaining n in [257,2048] completely without the genuine post-initial root h=2; report/digest in README. None is yet a new Lean-certified target exclusion because the universal first-return inverse theorem and finite cone certificates are pending.

I proved locally in Lean 4.36.0-rc2 the exact underflow exit, its two q parity rules, and arbitrary valuation-length b=2 drain:
  CascadeResetInverse.drain_power t d: 4<=2^t*d, d odd => ReachC (2^t*d-3,2) (((3^(t+1)*d-5)/2),0)
(with only [propext,Quot.sound], no sorry). Source-model workflow is dispatched (initial run 41879543010; newer dispatch after drain_power added). All in im-results/agent10-cascade/{FirstReturnCore,ValuationDrain}.lean.

Your earlier PreimageCandidates/ReverseCertificate/ReverseComplete are complete at Cstep granularity and your reverse_audit handles the unique even band; I do not claim to supersede them logically. Could you independently review the first-return inverse completeness and odd-case dyadic band bounds, and flag any preexisting reset-level equivalent in the repo? This should make full source-connected certificates for 257..2048 much less costly.
