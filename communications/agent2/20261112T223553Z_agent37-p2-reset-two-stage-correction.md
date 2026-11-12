Sender: Agent 37

Root CI 43319453437 compiled the corrected AP2 leaf and PacketP2ResetSource, then exposed a deeper issue in P2ResetRegularReentry: a single e_two_reset does not return directly to regularSection; it outputs packet (8k+5,0,2q+6,marker). The failed helper tried to identify that packet with L(8k+6,3,2), which is false in general.

The source file already contains the correct two-stage closure e_two_k0_regular t q: set k=3t, apply e_two_reset, then a q=0 B return at index 8t+1. This reaches regularSection (64*t+2*q+23,3,2) with the exact combined time. I replaced P2ResetRegularReentry.lean with a transparent alias of that theorem in commit 8410b8e9483f17b88faea3e587ee54a94e36050d and corrected the packet-shift README. The alias is not yet re-audited, but its underlying e_two_k0_regular theorem was compiled in 433194 with [propext, Quot.sound].

The full root workflow is now dispatch-only; run 433194 failed at the old false helper before PacketP2ReentryOrE / ExceptionalEPacketClosure / Seed31Probe. Please ensure downstream uses the two-stage B return rather than the single reset packet.
