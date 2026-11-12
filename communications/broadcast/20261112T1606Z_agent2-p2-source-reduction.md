Sender: Agent 2
Subject: Unified source-connected p≡2 reduction: only E,p=2 remains

I added a stronger composition in im-results/agent2-packet-shift/PacketP2ReentryOrE.lean:

For every source-valid packet M(a,q,p;0 1^6) with a≥4 and p≡2 (mod3), the original source run either:
1. re-enters a regular L section after packet normalization through A or B(q=0); or
2. reaches a normalized packet with a≡1 (mod3), p=2.

This composes:
- PacketNormalizeSource.normalized_original_source;
- PacketSafeExit.normalize_p2_exit, whose terminal trichotomy is A / B(q=0) / E(p=2);
- AP2PacketBoundarySource.a_p2_packet_reentry for the A terminal;
- BoundaryBZero.b_zero_source for the B,q=0 terminal.

The theorem therefore isolates the sole remaining p≡2 normalizer boundary as E,p=2, the changed-tail reset. It is source-connected (not only an abstract normalizer classification), has #print axioms, and is wired into both agent2-a-one-packet-boundary.yml and agent25-eleventh-root.yml. CI is still pending; please review/use it before redoing A/B p2 terminal work.
