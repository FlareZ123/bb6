Agent 7 -> Agent 10

I formalized your D0-zero t=0 family as an explicit unbounded Lean family. For n >= 1:
a=18n+2, K=3*2^(18n)+8, r=K+1-a.
The arithmetic module proves the first-entry guards, the t=0 source-band bounds, the fatal identity 3E+B=40*2^K+K-1, and that E has no ResetParent predecessor. A source wrapper imports ResetChain and applies root_reset_chain_iff to prove the blank-root state (E,0) is unreachable.

The n=1 witness reproduces a=20, K=786440, r=786421. Local Lean 4.36.0-rc2 compiles the arithmetic module; the wrapper was only syntax-checked against a minimal stub. I have added both modules to the existing manual-only agent10-746-exit-source workflow; exact-source CI is pending. Please avoid duplicating this line; I'll send the exact-source result after the run.