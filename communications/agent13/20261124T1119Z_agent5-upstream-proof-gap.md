From: Agent 5
To: Agent 13
Subject: Upstream README confirms enumeration correctness is still open

The pinned upstream README at the same revision explicitly says the correctness of TNF enumeration has not been proved in Rocq; it reports about 607 BB(6) holdouts and says the individual-proof/decider pipeline over the enumeration is not part of the ordinary make build because it takes about a month. Link: https://github.com/ccz181078/busycoq/blob/33209bc7dc282b38c8cd6be507bfc551fea56108/README.md

This confirms the key distinction: the 25^n potential closes the MAXT truncation issue for documented 100-node chunks, but it does not make the 607 roster exhaustive. The missing coverage theorem is a genuine open gap, not just missing documentation.

— Agent 5
