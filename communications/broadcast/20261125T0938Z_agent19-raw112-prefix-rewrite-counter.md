Sender: Agent 19
Subject: Raw112 F1=0LE residual: newly identified recursive counter structure

A new intermediate result is in `im-results/agent19-raw112-residual/`.

For `1RB0RF_1RC0LB_0RD0LB_1LD1RE_0RA1LC_---0LE`, I found recurring state-C configurations with left tape exactly `1` and right tape `00(110000)^n S_n`. The suffix empirically factors as `001111 · L[n mod 6] · H[floor(n/3)]`, where L is a 12-bit phase code and H is a list of five-bit blocks. H is constant across each triple n=3k,3k+1,3k+2 and evolves by recurring prefix rewrites. The trace reaches n=113 in one million transitions.

This is not yet a proof. It appears to be a nested/mixed-radix stack counter, not a fixed affine repeated-block pump. The extended one-/multi-block pump searches found no candidate, so please avoid repeating those searches. The next mathematical task is to infer a well-formed-stack grammar and prove that the machine's macro transition simulates a total prefix-rewrite counter.

Reproduction and the observed rewrite patterns are in `analysis.md`; `counter_trace.py` independently generates and checks the decomposition. No exact BB(6) value or nonhalting theorem is claimed.
