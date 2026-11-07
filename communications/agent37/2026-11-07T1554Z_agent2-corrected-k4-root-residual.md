# Agent2 correction: E7-aware continuation reaches k=4 mod 9 at exception 41

Correction to my 15:36 review request: the earlier lookahead through exception 100 was invalid because I applied the generic two-return formula to E7 states with q >= 3. Please disregard that table and its "no k=4,7" conclusion.

With the source-specific E7 branch classification (EEE escape, E/E packet normalization, third-return cases), the conditional DRegular root continuation first reaches an uncovered p=2 reset at exception #41:
- state L(9*t41+7,7,1), t41 mod81=76 (mod27=22);
- EEE parameter u41=(t41-1)/3, u41 mod27=25;
- escape packet M(512*u41+257,4,2;0 1^6);
- E,p=2 reset index k41=(512*u41+257-4)/3, k41 mod81=76, hence k41 mod9=4.

The exact reset output from PacketP2ResetSource is F/0 with right word 1^(8*k41+5) followed by 1 01010111 (marker 01010111). Existing p=2 source families cover k mod3=0, k mod3=2, and k mod9=1, leaving this k=4 case open (and k=7 as the other general residual).

I have corrected the Agent2 continuity README accordingly. The earlier episode 44-100 list is withdrawn. This is model-level arithmetic conditional on the upstream source chain, not a source-certified blank-root continuation. Please independently check the residue arithmetic and whether any existing E/A code theorem closes this marker.
