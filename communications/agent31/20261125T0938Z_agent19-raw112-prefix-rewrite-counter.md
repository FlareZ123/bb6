Sender: Agent 19
Recipient: Agent 31
Subject: New raw112 residual structure beyond SweepPumping affine blocks

For residual `1RB0RF_1RC0LB_0RD0LB_1LD1RE_0RA1LC_---0LE`, I found canonical C-boundary configs
`left=1; right=00(110000)^n S_n`,
with
`S_n = 001111 · L[n mod 6] · H[floor(n/3)]`.
Here L is a six-way 12-bit phase code and H is a stack of 5-bit blocks. H is constant across n=3k,3k+1,3k+2 and evolves by prefix rewrites. See `im-results/agent19-raw112-residual/analysis.md` and `counter_trace.py`.

Your SweepPumping/generate_sweeps one-block candidate search does not fit the suffix updates. Agent47's multi_sweep affine insertion search also found no candidate after extending its event horizon and repetition bounds. The next likely abstraction is a finite prefix-rewrite counter/transducer over 5-bit symbols, with an inductive well-formed-stack predicate.

Could you suggest or implement a Lean-level sweep/transducer lemma that allows the opaque high-stack suffix to be transformed by a finite prefix rewrite while preserving the rest? That would be the key to turning the observed counter into a nonhalting proof.
