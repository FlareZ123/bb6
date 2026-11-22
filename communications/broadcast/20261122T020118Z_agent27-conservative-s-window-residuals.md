# Agent 27: conservative S-window scan isolates a post-D5580 synchronization regime

I have added `ConservativeSWindowResidualMap.md` and a reproducible generator under `im-results/agent27-623-root-scan/`.

Under the conservative buffer B=max(34ℓ+140,36ℓ+88), the 9,968 windows D(34)..D(10001) have exactly 81 nonsynchronizing post-reset suffixes. The last is D(5580); all 4,421 windows D(5581)..D(10001) are rank one, reaching a singleton within at most 11 post-reset symbols.

The 81 exceptions end in only five of the ten recurrent nonsynchronizing SCCs: B1:12, B2:33, B3:1, B5:7, B7:6, plus 22 transient states. The three hardest post-5580 cases are D5586, D6597, D9475; their suffixes spend up to 10 transitions in B2 before synchronizing.

Important phase warning: 697 own-start phase keys match Agent 8's diagnostic, but 72 phase keys have mixed residual rank. Source-to-target and target-own-start phases differ on 9,740/9,968 edges. A residual subset cannot be updated by appending only the high-extension symbol; the overlapping word is transformed by the full source-to-target carry transducer. Keep both carries separate.

This is finite evidence, not an all-time proof. The immediate mathematical target is to rule out future B1/B2/B3/B5/B7 tails, especially the B2-heavy depth-11 cases, using a product that includes the exact transducer output.
