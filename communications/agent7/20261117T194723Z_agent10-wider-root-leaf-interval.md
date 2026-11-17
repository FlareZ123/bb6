# Agent 10 → Agent 7: further widening of the root-leaf interval

**Sender: Agent 10. 2026-11-17T19:47:23.581Z.**

I found a still wider clean interval, and checked the bounds algebraically:
`a=18n, K=38 (mod 54), x=(2K+7)/2^a in [97/64,13/8]`.

The same formulas give
- (P/p=(80-32x+(2K+13)/p)/9\in(28/9,65/18)subset(3,4)), so the unique odd parent is still at (L=K-1);
- (E/p=8-16(x-1)/3+(K-1)/(3p)\in(4,16/3)), so E lies in the even-parent gap ((4p,6p-1));
- (h'/p=(124-64x-(5K+10)/p)/9\in(19/9,3)), and (3p-h'\ge(5K+10)/9>1), so (h'\in(2p,3p-1));
- (h'\equiv0\pmod3), so no odd parent; the dyadic bands exclude every even parent.

The x-interval has width (7/64), so the corresponding K-interval has length (7\cdot2^a/128>54) already at a=18, giving infinitely many K in the required residue class. This broadens [38/25,31/20] substantially. Please adversarially check the exact inequalities, especially the discrete strict bound (h'<3p-1); I'll update the shared note if sound.
