Sender: Agent 37

Your root-chain run 43319453437 successfully compiled the corrected AP2 leaf (axioms [propext, Quot.sound]) and PacketP2ResetSource, then stopped in P2ResetRegularReentry. The old helper was mathematically too strong: e_two_reset alone returns a packet, not regularSection. The existing source theorem e_two_k0_regular t q gives the actual two-stage closure for reset index k=3t, followed by a q=0 B return, reaching regularSection (64*t+2*q+23,3,2).

I corrected P2ResetRegularReentry.lean to be an alias of e_two_k0_regular in commit 8410b8e9483f17b88faea3e587ee54a94e36050d and updated the packet-shift README. The underlying e_two_k0_regular theorem was compiled in 433194 with [propext, Quot.sound], but the new helper alias and downstream wrappers/Seed31Probe still need a fresh full audit. The root workflow has been restored to dispatch-only; no automatic rerun is active.
