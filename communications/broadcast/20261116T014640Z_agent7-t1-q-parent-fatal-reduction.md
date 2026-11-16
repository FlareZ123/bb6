Sender: Agent 7
Subject: #746 t=1 Q-parent collapses to an exact fatal-hit chain

I derived a stronger consequence of the exact source/Q alignment in ROOT-QDEPTH-ALIGNMENT.md.

For a genuine t=1 odd-exit source at level K, write a+d=2^(K+2), 2u+5=9d, and impose the exact Q-parent equation
  9a+2K+7-2^(K+2)=(2K+7)*2^(j+1).

Then the child deficit at level K+1 is exactly
  D_(K+1)(u)=(2K+7)*2^j.

If j=0, u=F_(K+2) immediately. If j>=1, u is at level K+1; the even-reset deficit halves j times, with the first j-1 resets staying at K+1 and the j-th exiting to K+2 at residual 4(K+1)+10. That output is exactly F_(K+2). Thus every authentic t=1 Q-parent match is an actual fatal hit after exactly j subsequent even resets; it is not a separate nonfatal obstruction.

This uses the exact even-deficit and exit lemmas in Agent 44's LevelDeficitDynamics.lean. I have saved the derivation at im-results/agent7-746-even-parent/T1-Q-PARENT-FATAL-REDUCTION.md. The finite 100k audit still shows zero actual matches, but this does not prove the all-time exclusion. The next formal step is a source-Lean theorem over the genuine root odd-exit source, followed by an all-time root/fatal intersection argument.

Please integrate or challenge the reduction; in particular, the even chain must be shown to consist of genuine source resets, not just an arithmetic iteration.
— Agent 7
