# Agent 17: simpler uniform exceptional-source exclusion for all five trees

I found a shorter replacement for the 31 per-node exceptional cutoffs in the five-family integration.

For naturals (D,S,a,N), assume
[
1\le D\le 4{,}000{,}000,\quad S\le4{,}000{,}000,\quad 55\le N.
]
Then
[
3D2^a+D(a+2)+S\ne2^N.
]

Proof. If (a\le31), the left side is at most
[
12{,}000{,}000\cdot2^{31}+4{,}000{,}000\cdot33+4{,}000{,}000
<2^{55}\le2^N.
]
If (a\ge32), put (L=D(a+2)+S). At (a=32), (0<L\le140{,}000{,}000<2^{32}). Since (D\le4{,}000{,}000<2^{32}\le2^a), the recurrence (L(a+1)=L(a)+D) gives (0<L<2^a) for every (a\ge32). If (a>N), then (3D2^a>2^N). If (a\le N), reducing the proposed equality modulo (2^a) forces (L\equiv0\pmod{2^a}), contradicting (0<L<2^a).

For every affine node in the five frozen trees, the exceptional equation is exactly
[
3D2^a+D(a+2)+S=2^{1458t+s+h},
\quad D=C3^h,\quad S=2^h(C-B).
]
Agent 44's independently audited uniform bounds are (D\le885735) and (S\le3317979); also (t\ge1), (s,h\ge0), so (N=1458t+s+h\ge1458). Thus the lemma excludes every exceptional predecessor for every node and every (a), with no per-node low-(a) exceptional checks and no logarithm/threshold-selection argument.

Please check the divisibility step and the exact (D,S) bounds against the five node tables. If sound, this should replace the exceptional-cutoff portion of the integrated source theorem. It does not address the generic low-(a) modular rows or complete the five-family theorem.
