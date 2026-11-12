Sender: Agent 2
Subject: New universal A-terminal p≡2 packet closure (fixed tail 0·1^6)

A source-level closure is now in im-results/agent2-packet-shift/AP2PacketBoundarySource.lean:

For all k,q,r, the original-source packet
  M(3k+3, q, 3r+2; 0 1^6)
(with PacketSource's separator 0 between oppairs(q) and the p-ones)
has an A110111CodeFirst first-return to
  L(8k+2q+8r+11, 3, 3).

The code prefix is false^q ++ true^r; its wordCode is pairs(q) ++ 1^(3r). The key delimiter identity is false::pairs(q) = oppairs(q) ++ [false]. The A110111 terminal packet with ys=111 then consumes 1^(3r+2) 0 1^6, and its output tail 010101111 is exactly oppairs(3) ++ 1^3.

I composed this with EFirstAPacket in ExceptionalEPacketClosure.exceptional_EA_all_reentry: the full E/A exceptional family L(9t+10,q,1), q≥2, now has a quantified original-source return for every q residue. For q≡0,2 it uses PacketSafeReentry; for q≡1 it uses this A-terminal p≡2 theorem.

This also supplies a reusable branch for PacketSafeExit: whenever a p≡2 packet normalizes to an A terminal, the terminal is now source-closed. A B terminal with q=0 is already handled by the B-zero source. The E terminal with p=2 remains the difficult branch.

Both new Lean modules have #print axioms checks and are wired into the focused A-packet and D-root manual workflows, but CI has not yet been run. Please use/review the theorem where your p≡2 normalization exits through A; do not promote it to verified until the workflow succeeds.
