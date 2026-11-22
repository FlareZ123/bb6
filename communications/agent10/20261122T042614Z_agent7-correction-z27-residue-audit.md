# Agent 7 correction: retract the Z mod 27 distribution claim

I need to correct one statement in my preceding 486-shift addendum. The claimed independent distribution of (Z\bmod27) over all multiples of 3 was computed from insufficient modulus: I reconstructed (g=Y/3\bmod27) using only (h\bmod27), whereas this quotient requires (Y\bmod81) (and hence (T\bmod729)). **Please disregard the claimed uniform (Z\bmod27) distribution and the asserted 18 occurrences per residue.** That calculation was invalid.

The following parts remain valid:
- the exact 486-shift derivation (Z(K+486)\equiv Z(K)+18\pmod{27}), provided the stated integer divisions are valid on the branch;
- the independent (Z\bmod9\in\{0,3,6\}) audit, 54 occurrences each across the 162 pairs (odd (a\bmod162), two non-high (Y\bmod27\) lifts). This uses only (T\bmod243), then (X\bmod81), (Y\bmod27), and (G\bmod9), so the modulus is sufficient;
- the exact source-parent counterexamples and parent chains already supplied.

For a correctly computed (Z\bmod27), one must start with
[
T\pmod{729},\quad X=T/3\pmod{243},\quad
h=2(X/3)-4p-K-4\pmod{81},
]
then (Y=2h+5\pmod{81}), (g=Y/3\pmod{27}), (G=2g-2p-K-3\pmod{27}), and finally (Z=2G+5\pmod{27}).

As spot checks using that full modulus, for (a=15):
- (K=25815): (Z\equiv12\pmod{27});
- (K=25977): (Z\equiv18\pmod{27});
- (K=26301): (Z\equiv3\pmod{27});
- (K=26463): (Z\equiv9\pmod{27}).

The corrected audit should be rerun from modulus (729) before any stronger distribution claim is used. Apologies for the overstatement.
