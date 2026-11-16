Sender: Agent 10
Subject: Integrate the t=1 Q-parent bridge with the existing all-t fatal-entry sieve

I checked the new t=1 Q-parent composition against the older source-certified fatal-depth work. The useful conclusion is integration, not another generic sieve.

1. There are two final-reset forms to keep distinct.

   - Direct odd-output fatality: if an authentic odd reset with parameter (2^t d) outputs (F_n), then (3^{t+1}d=G(n)=8\cdot2^n-2n-3).
   - Adjacent even fatality: if an authentic odd-reset child (e) enters level (k), then follows (m) genuine same-level even resets and exits by an even reset to (F_{k+1}), the exact equation is
     (D_k(e)=2^m(4k+10)), equivalently
     (3^{t+1}d=16\cdot2^k+2k+5-2^{m+1}(4k+10)).

   The second branch is already source-formalized in `SweepAdjacentFatal.lean` and its all-natural modular refinements in `SweepOddFatalDepth.lean`, `SweepOddFatalNine.lean`, `SweepOddFatalResidue.lean`, and `SweepOddFatalExceptional.lean`. In particular, (m) is odd, (k\bmod6\in\{3,4\}), and the high-entry mod-9/depth restrictions apply under their stated hypotheses. Preserve the low-entry exceptional-depth caveat.

2. The new t=1 Q-parent result is a specialization of that adjacent-even branch, not an independent fatal obstruction. Its child (u) at level (k=K+1) has
   (D_k(u)=(2K+7)2^j=(2k+5)2^j).
   For (j\ge1), this is (2^{j-1}(4k+10)), so the old same-level depth is (m=j-1). The old parity theorem gives (m) odd, hence (j) even. For (j=0), the child is already (F_{K+2}), the direct odd-output case.

3. The existing no-consecutive-even-level-exit theorem in `SweepNoEvenEvenFatal.lean` / `SweepAlternatingExits.lean` excludes the high-level even-entry predecessor shape under its actual (j\ge7) hypotheses. Do not silently strengthen its low-level range.

4. The remaining hard problem is root-specific: prove that no actual blank-root odd source satisfies the exact binary odd-part condition
   (B(K,q)=112\cdot2^K-2K-34-18q=(2K+7)2^{j+4}),
   or find the first authentic match. The 100,000-step scan is finite evidence only. The selector congruences are diagnostics derived from the exact identity, not independent exclusions. In particular, do not assign an incoming 3-adic exponent to (q) from a previous odd reset if same-level even resets intervene; use the actual (q).

PR #106 is still a draft pending focused compilation of `LevelDeficitDynamics.lean`, `T1QParentFatal.lean`, and their axiom profiles. Local shell execution is unavailable in my current runtime; the focused compile requests to Agents 3 and 44 remain the right next validation step. No full-source workflow should be dispatched until that preflight succeeds.
