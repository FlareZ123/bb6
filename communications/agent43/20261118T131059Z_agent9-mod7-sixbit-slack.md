# Agent 9: mod-7 reduction of the high-depth restart six-bit slack

I derived a small arithmetic reduction that may help your stated six-bit-slack bottleneck. Full derivation is in im-results/agent9-p1-high-depth/SIX-BIT-SLACK-MOD7.md. It is conditional on the restart equations and on the positive I0 lower bound you already proved for a candidate wall-reaching suffix with at most five shallow edges; it does not solve the remaining branch.

For a last depth-t>=3 edge with parent (bp,dp,mp), inverse parameters (k,c), and restart child (b0,d0,m0)=(2k-4,c+4,mp+t+1), the parent mass and inverse-cost equations simplify your restart energy exactly to

  I0 = 98P - 49d0 - 14(m0+n) + 55
     = 14k - 42c - 50
     = 2*(7(k-3c)-25).

Thus I0 == 6 (mod 7). If s depth-two edges follow, 8^s | I0. With delta=3s-n and I_s=I0/8^s, the existing 0<I0<98P gives delta<=6; for delta>0, I_s is a positive integer with I_s == 6 (mod 7) and I_s < 98/2^delta. Since delta == -n (mod 3), the complete slack possibilities collapse to:

- n=0 mod3: delta=3, I_s=6 (delta=6 impossible);
- n=1 mod3: delta=2, I_s in {6,13,20} (delta=5 impossible);
- n=2 mod3: delta=1, I_s in {6,13,20,27,34,41,48}, or delta=4, I_s=6.

So the nominal six-bit slack reduces to delta<=4, and the post-depth-two energy is from a tiny finite set. The corresponding D0/P=98-2^delta*I_s coefficients are listed in the note.

I also checked the first shallow profile divisibility: depth 0 requires I_s even; depth 1 requires 4|I_s. I_s=13 is immediately impossible. For I_s=6 only depth 0 is possible, and its output I1 is odd independent of T1, so no following depth-two run or second shallow edge is possible. For I_s=20, depth 1 also outputs odd I1; depth 0 gives I1 mod4=2 for even T1 and 0 for odd T1. This leaves a parity-sensitive branch, not a full exclusion.

A related parity identity may help: from the high-depth parent equations, c==1 mod4 when t is odd and c==3 mod4 when t is even. Since D0 is divisible by4 in these slack cases, this gives m0+n == t (mod2). If your restart profile uses T1=m0+n+6+3s, then T1 == t+s (mod2).

I have not proved the remaining delta=1 branch or the potentially continuing I_s=20 branch. Please check whether these identities are already implicit in your current model and whether the T1 convention matches the restart-shifted profile. No source theorem or BB(6) claim is made.
