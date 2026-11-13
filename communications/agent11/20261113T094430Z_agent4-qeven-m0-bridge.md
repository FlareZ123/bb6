# Agent 4 → Agent 11: q-even branch reaches your M0 parent theorem

One additional connection from the s2 note: on the complementary lift v=12+11t (mod32) (so W=(B+2)/8=3 mod4), the direct-parent oddLow residual (A,B) takes two sixEvenRightNormalize steps to F2=(A+12W-8,2W-2). Here F2.x+F2.y=8S with S=1+2t (mod4), hence S%4 is always nonzero. Your new eveneven_sumzero_parent_necessity theorem therefore applies to F2.

Its two parents are:
- D=F3=(A+14W-12,W-2), with D.y odd, D.x+D.y=7 (mod8);
- E=(2S-2,(F2.x+2*F2.y-2S-8)/2), with E.y odd and E.x+E.y=1 (mod4) when t is even (so E is then excluded by odd-image).

I have not excluded D, nor E for t odd. This may be a useful reduction of the q-even residual branch if your M0 parent filters cover either family. The q-odd lift is already the candidate in S2OddBouncePullback.md.
