# Theorem A: Sheep odd-halting precursor backward sieve

**Analytical intermediate result.** The published Sheep accelerated map, initial integer 5, is defined on (n=2^a m) (odd (m)) by (f(n)=mathrm{HALT}) for (m=1), (f(n)=3cdot2^a+a+3) for (m=3), and (f(n)=2^a m+a+(m-1)/2) for (m\ge5). The machine-to-map Lean reduction is upstream: https://github.com/rwst/bbchallenge/blob/main/1RB1LA_0LC0RC_1LE1RD_1RE1RC_1LF0LA_---1LE/machine.lean .

For even (b\ge4), define (P_b=(2^{b+1}+1)/3). It is an odd direct predecessor of the halting power (2^b), since (f(P_b)=2^b).

**Theorem:** For even (b\ge6), every defined predecessor of (P_b) has valuation (a\in\{0,1,2,3\}), and exists uniquely at each valuation precisely under these conditions:

| a | b congruence | first b |
|---|---|---|
| 0 | b = 0 (mod 6) | 6 |
| 1 | b = 2 (mod 4) | 6 |
| 2 | b = 14 (mod 18) | 14 |
| 3 | b = 4 (mod 8) | 12 |

The unique input is (2^a(2P_b-2a+1)/(2^{a+1}+1)). Consequently every (P_b) with even (b\ge8) and (b\bmod72\in\{8,16,40,56,64\}) has **no incoming defined edge**. As (P_b>5), none of these infinitely many direct halt precursors can occur in the actual orbit from 5. Also (P_4=11) has no predecessor.

## Proof

For an input (2^a m) with odd (m\ge5), the equation (f(2^a m)=P_b) is equivalent to

[
2^{b+2}+5-6a=3(2^{a+1}+1)m. 	ag{A1}
]

Write (D=2^{a+1}+1). Therefore (2^{b+2}\equiv6a-5\pmod D). Since (2^{a+1}\equiv-1\pmod D), division of the exponent by (a+1) shows that **every** residue of a power of two modulo D is either (2^r) or (D-2^r), with (0\le r\le a).

For (a\ge5), induction gives (6a\le2^a) (base (a=5): (30\le32); doubling preserves the bound). The required residue (6a-5) is odd, greater than 1, and less than (2^a). It cannot equal (2^r), which is either 1 or even; it cannot equal (D-2^r\ge2^a+1). For (a=4), (D=33), and the full residue set is ({1,2,4,8,16,17,25,29,31,32}), excluding (6a-5=19). Thus (a\le3).

For each (a=0,1,2,3), (A1) is equivalent to (2^{b+2}\equiv6a-5\pmod {3D}). The moduli (3D) are respectively (9,15,27,51), with multiplicative orders of 2 equal to (6,4,18,8). Their required exponent residues (b+2) are respectively (2,0,16,6), giving the table. Conversely, these congruences yield integer quotients (m=(2P_b-2a+1)/D); (m) is odd, and the specified minimum b in each row gives (m\ge5). Hence the conditions are sufficient.

The special odd-part-3 branch would require (2^{b+1}=9\cdot2^a+3a+8). At (a=0) this is 17, not a power of two. For (a\ge1), induction yields (3a+8<7\cdot2^a), placing the right side strictly between consecutive powers (2^{a+3}) and (2^{a+4}). Hence the special branch cannot enter (P_b).

Among the nine residues b = 0 (mod 8) modulo 72, the first table row admits only 0,24,48; the third row only 32; the others none. The five complementary residues are 8,16,40,56,64. Any state without predecessors and different from initial 5 cannot occur later in the orbit. QED.

This is an all-time exclusion in the published accelerated map, **not** a proof of machine nonhalting. The global argument is written mathematics, not yet a Lean kernel certificate.
