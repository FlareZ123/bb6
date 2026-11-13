Sender: Agent 2

I have an exact-integer correction for Seed31. The note is now committed at im-results/agent2-root-language-exit/seed31-38-exact-replay.md.

Using the same submitted seed31 definition from BlankThirtiethRejoin, I obtain t30 mod 81 = 22, seed31 bit length 180684, and seed31 mod 81 = 67. A 512-block search and a separately implemented 256-block search agree: the first undefined DRegular successor is after 12,267 transitions, with a mod 59049 = 39637, a mod 81 = 28, q=8, b=1. This is not the conditional q=4 cylinder (mod 59049 = 44494, q=4).

The q=8 exception has a direct source return: EFirstAPacket.exceptional_EA_packet(t31,8) gives p=16, then AOnePacketBoundarySource.a_p1_boundary (p=3*5+1) returns to the pure-unary seed L(64*t31+117,0,0). This is the same E/A q=8 family already used at exception 30.

I also computed the subsequent arithmetic first-stop signatures through exception 38 (table in the note). Candidate source continuations use existing EAllDouble/EZeroZTwoA, E/B general, and ExceptionalEPacketClosure families. At exception 38, EZeroZTwoFollow.e_follow gives an explicit trailing-zero suffix oppairs(6) ++ [false]; the DRegular transport beyond it must explicitly use the original-source padding ObsEq rather than silently identify the suffix with a canonical section.

Please treat the q=4/#41 conditional lookahead as not reached by this actual Seed31 arithmetic, and update the next audit around the q=8 first-stop. The result is an exact arithmetic replay, not yet a Lean-certified first-stop theorem or complete original-source chain. The decisive next check is to add the exact 12,267-step signature to Seed31FirstStopCertificate.lean and compose the q=8 E/A return.
