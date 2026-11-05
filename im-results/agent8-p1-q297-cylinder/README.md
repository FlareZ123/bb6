# Authentic P1 inverse-cylinder candidate, q = 297 + 1024r

Agent 8, 2026-11-05. An exploratory symbolic inverse-graph construction for the authentic P1 two-feeder shadow recurrence gives an independently new candidate index family n = 4754 + 16384r. The 12-node L0 and 14-node L1 graphs have maximum inverse cost 10 and no state with 256 dividing its shadow counter, uniformly over every natural r, **conditional on Lean audit of the generated arithmetic and source proofs**.

## Mathematical method

The original-source two-feeder theorem rewrites reachability of the critical reset target at n=16q+2 into reachability of L0=(4u-4,4u+9) or L1=(6u-2,2u+5), where u+4q+3=7*2^(16q). The exact shadow recurrence is
(m,z) -> (m+t+1,z') when z=2^t*v and 2*z'+1=(16q+h)+m+t+v, with h=8 or 9.
Explicit parametric nodes and all successor cases are in Q297Arithmetic.lean; original-source lifting, even exits, exceptional exits and backwards blank disjointness are in the rest of the Q297* modules. The resulting target theorem is `BB6.Agent8Q297.critical_4754_mod16384_unreachable`, assuming its complete original-source audit succeeds.

This module family instantiates the previously source-certified Agent8 q29 mechanism, reusing Agent9's source projection, Agent1 and Agent4 inverse barriers, and Agent45's exact two-feeder theorem. Unlike q29, q297 does not lie in any of Agent45's 13 published period-256 arithmetic candidate residue classes; individual overlap with the full prior source-certified P1 corpus still needs review. The result, if checked, is an infinite necessary-critical-gate exclusion. It is not a P1 machine decision or BB(6) upper bound.

## Reproduction and limits

Manual-only source compilation workflow: `.github/workflows/agent8-p1-q297-all-source.yml`. It compiles unchanged original Agent1/4/9/45/47/50 dependencies, followed by all ten new modules; it prints final theorem axioms. Full Lean 4.36.0-rc2 checks are required before the candidate becomes an established theorem. Keep this investigation under im-results pending independent novelty and end-to-end review.
