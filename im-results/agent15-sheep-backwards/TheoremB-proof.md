# Proof of Q-family predecessor classification

For n=2^a*m with odd m>=5, f(n)=Q_b is equivalent to

    2^(b+3) + 1 - 10*a = 5*(2^(a+1)+1)*m.     (B1)

Write D=2^(a+1)+1. Equation B1 requires 2^(b+3) = 10*a-1 modulo D. As 2^(a+1)=-1 modulo D, every residue of a power of two is 2^r or D-2^r, 0<=r<=a.

For a>=6, elementary induction gives 10*a<=2^a. The residue 10*a-1 is odd, greater than one and less than 2^a. Neither possible form can equal it. At a=3 the residue is 29 modulo 17, namely 12, outside the power-of-two residue set {1,2,4,8,9,13,15,16}. At a=4 it is 39 modulo 33, namely 6, outside {1,2,4,8,16,17,25,29,31,32}. At a=0, normal f(n)=(3*m-1)/2 is congruent to 1 modulo 3, whereas Q_b is divisible by 3. Thus only a=1,2,5 remain.

At a=1,2,5, reduce B1 modulo 5D. The three moduli are 25,45,325; the multiplicative orders of 2 are 20,12,60; the only possible exponent residues of b+3 are respectively 14,6,10. This yields b=11 modulo 20, b=3 modulo 12, or b=7 modulo 60. The displayed quotient m is odd because numerator and denominator are odd, and m>=5 beginning at b=11,15,67 respectively; so all conditions are sufficient.

The special odd-part-3 branch requires 2^(b+2)=15*2^a+5*a+17. For a>=6, 5*a+17<2^a by induction, so the right side is strictly between powers 2^(a+3) and 2^(a+4). For a=0..5 the right side is 32,52,87,152,277,522; only 32 is a power of two, corresponding to b=3, outside the theorem. Hence no special predecessor exists.

Among the fifteen residue classes b=3 modulo 4 modulo 60, the union of permitted classes is {3,7,11,15,27,31,39,51}. The seven complementary classes are {19,23,35,43,47,55,59}. No valid incoming edge exists for any b in them. Since start 5 differs from Q_b, these states are unreachable from start 5 at every future iteration. QED.

The argument concerns the upstream accelerated map, not an independently proved Turing machine bridge.
