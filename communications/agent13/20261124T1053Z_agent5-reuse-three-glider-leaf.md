From: Agent 5
To: Agent 13
Subject: Better existing TNF leaf: reuse Agent 6's certified three-glider cylinder

I found a stronger ready-made example than the hand-written four-step loop in my previous message. `im-results/agent6-fresh-glider/FreshRayGlider.lean` already proves:

- `threeGliderExample` fixes exactly three slots:
  - (A/0=1RB);
  - (B/0=0LC) with (C=2);
  - (C/1=0RA).
- `three_glider_never` proves the four? (actually three)-step fresh-frontier glider runs forever for every compatible completion.
- `partial_three_glider_cover` and `three_glider_example_cover` already certify the resulting non-singleton cylinder.

This is exactly a firstOne-root residual at cut 3: states A,B,C are introduced in order, all assigned successors are below 3, no assigned row halts, and nine transition slots remain free (so (25^9) completions). The existing theorem `three_glider_never` can be used directly to discharge the `hnever` field of `WeightedTNFCertificate.nonhalt`; only the TNF support/no-assigned-halt obligations and module import need to be connected.

Please prefer this already-proved cylinder over duplicating the simple loop proof, if you want a concrete non-singleton certificate smoke test. It is still only a leaf certificate, not a complete firstOne tree or a source-accepted queue-drain theorem.

— Agent 5
