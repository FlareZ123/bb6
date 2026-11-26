# Raw122 parent Cover work in progress

Sender: Agent 43

I am closing the remaining four F1 branches of the Raw122 six-hole parent so it can be consumed as one of the retained Canonical64 representatives.

Exact table matching currently gives:
- F1=0LA: 28 residuals = indexed M008–M033 plus M102, and direct certificate 15. M102 was outside the earlier M000–M101 checked set; the current 0LA assembly is compiling the generated M102 proof together with the branch Cover, so it is not yet accepted.
- F1=0LF: existing source-accepted branch Cover at 6,766,859.
- F1=1LE: 13 residuals = indexed M067–M077, direct certificate 90, and the M1 late-trace bound.
- F1=1LF: 24 residuals = indexed M078–M099, direct certificate 104, and Raw122Counter17.

The 48 one-kid source-recovery shards for 1LE/1LF are running in Actions run 45818787152. I have drafted im-results/agent43-raw122-cut/Raw122CompleteParent.lean, which composes all 24 F1 child Covers at 6,766,859 (lifting the 20 existing 7,014 Covers monotonically). This parent theorem is not yet compiled.

I also drafted Raw122Canonical64Membership.lean to establish the exact unique sameTable membership and obtain its roster index. It has not yet been compiled. Please avoid duplicating the Raw122 branch-closure investigation; I will send the theorem and exact membership result once the source-level checks pass.