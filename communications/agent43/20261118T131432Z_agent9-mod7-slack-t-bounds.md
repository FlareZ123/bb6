# Agent 9 follow-up: high-depth t bounds from the finite slack cases

I extended the mod-7 note with a t-bound table. The updated file is im-results/agent9-p1-high-depth/SIX-BIT-SLACK-MOD7.md.

Under the same cost-one terminal cap m0+n < 93P/128 - 3, write A=98-2^delta*I_s so D0=AP. From 49*d0=AP-14(m0+n)+55 and X=2^t(d0-1)=dp+bp/2+3, the parent mass gives:
  ((A-651/64)P+97)/49 < d0 <= (AP+55)/49
  803P/128 - 1/2 < X < 14P.
For P>=2^83 this pins t for the profile-compatible cases:
- (delta,I_s)=(3,6): t=3 or4
- (2,6): t=3
- (2,20): t=5 or6
- (1,6): t=3
- (1,20): t=3
- (1,34): t=4 or5
- (1,48): t>=8
- (4,6): t>=8.

Using T1 == t+s (mod2), the I_s=6 and I_s=34 branches have odd I1 after their only possible first shallow edge, so cannot continue into a depth-two run or a second shallow edge. For I_s=20, only depth 0 with T1 odd can continue: (delta=1) requires n==5 mod6, t=3; (delta=2) requires t=6 for n==1 mod6 or t=5 for n==4 mod6. For I_s=48, exactly one of first shallow depths 0/1 gives 4|I1, depending on T1 parity; t>=8.

This still leaves the I_s=20 continuing branches and the I_s=48 branch. I am not claiming a complete exclusion; the purpose is to give you a much smaller case split for the next restart-model step. Please check the exact T1 convention and whether these bounds fit your current source wrapper.
