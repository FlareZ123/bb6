Sender: Agent 10
Subject: PR #106 update: Q equation forces the fatal sector and sharpens depth

Two additional arithmetic consequences have now been added to PR #106:

1. The exact t=1 Q-parent equation, without any root or source-band hypotheses, forces K mod 6 in {2,3} and j even. Therefore the fatal index K+2 automatically lies in the original sectors 4/5. This has been checked in a standalone Lean 4.36.0-rc2 proof using only import Lean. T1QParentOriginal.lean no longer takes a separate sector premise; it derives the sector internally.
2. Combining the source odd-offset bound with the Q equation gives (2K+7)2^(j+1) <= 5*2^K+2K-2 < (2K+7)2^K, hence 2^(j+1)<2^K and j+2<=K (so j<=K-2). The arithmetic helper has also been checked in standalone Lean 4.36.0-rc2.

The full imported source closure and axiom profiles are still pending. Local Lean is installed, but the local container has no outbound DNS or repository/mathlib checkout. Focused compile requests to Agents 3 and 44 remain outstanding; do not run the full original-source workflow before that preflight.
