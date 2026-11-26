# Exponentially summable ideal inverse mass for #746

**Status (2026-11-26):** new paper-level bound for the ideal inverse tree used in FixedLevelAsymptotic.md, with arithmetic, deterministic-decoding, path-budget and automaton-majorant lemmas locally checked in Lean 4.36.0-rc2 (SeamMass.lean). The binary-prefix injection and resulting counting/tail theorem are proved below on paper. This is not a real-machine reachability decision or a global BB(6) bound.

## 1. Main theorem

Let W_A be the set of nonempty strict-band ideal inverse words from upper seam z=8 whose first edge is odd and cumulative valuation is A. Let N_A=|W_A| and B_A=floor(log2(3^A)). Then

    N_A <= S(B_A) <= (9/7)*(16/9)^B_A,

where S is the number of length-B binary prefixes from a three-state automaton defined below. Consequently

    c_inf = 1 + sum_{A>=1} (3/2)*N_A/3^A

is finite, and the coefficients c_g in FixedLevelAsymptotic.md converge exponentially to c_inf. More precisely, since cumulative level drop <= A,

    0 <= c_inf-c_g <= (27/14) * sum_{A>=g} (8/9)^floor(3A/2).

The exact automaton counts S yield much tighter computable upper tails than this simple geometric majorant. Enumeration through A=24 and exact automaton bounds through A=256, followed by the geometric tail, gives

    1.51902529 < c_inf < 1.551323.

The result removes the possibility that the fixed-gap linear coefficients grow without bound as the gap increases. It is not an interchange of the limits g->infinity and N->infinity; controlling the real near-seam corrections and rooted paths is still necessary.

## 2. Unique integer coding of ideal words

Normalize x=z/8. Start x_0=1. Each edge has

    x_i = (2^j_i/3^a_i) x_(i-1) - 1,
    j_i = a_i + delta_i + 1,

where a_i>=0 and delta_i>=0; all i>0 satisfy 1/2 < x_i < 1. The first edge has a_i>0. Write A_i=sum_{r<=i} a_r, p_i=3^A_i*x_i. Then

    p_0=1, A_0=0,
    p_i + 3^A_i = 2^j_i * p_(i-1).

Every p_i is a positive odd integer, since j_i>=1. After the first edge, p_i is a unit mod 3 (the recurrence multiplies the preceding unit by a power of two modulo 3). Therefore A_i is the exact ternary denominator exponent.

In the *forward* decoding direction, given (A_i,p_i), j_i=v2(p_i+3^A_i) is forced by oddness of p_(i-1). Also the band conditions give the strict inequalities

    2^j_i < 4*3^a_i,
    3*3^a_i < 2^(j_i+1).

For a fixed j, the ratio of upper to lower bounds on 3^a is 8/3<3, so at most one nonnegative integer a can satisfy these two inequalities. In particular j=2 would require 1<3^a<8/3, impossible; j=1 forces a=0. Hence the next state, valuation and level drop are all uniquely recoverable. Forward decoding stops when A=0; the only valid denominator-one state is p=1, the original seam. There are no intervening A=0 states in an odd-first word. Thus the terminal pair (A,p) identifies the entire word, including same-level even edges. The Lean lemmas admissible_of_band, exponent_unique, exponent_two_forbidden, edge_unique and path_unique prove these arithmetic facts for the integer model.

Since delta>=a+1 would imply 2^j>=4*4^a>=4*3^a, impossible, every edge has delta<=a. This establishes the cumulative drop bound. (The earlier opposite inequality A<=2*drop remains in force.)

## 3. Binary-prefix injection

Read a word in the forward decoding direction (from its terminal integer p back to the seam), and encode each j by j-1 zeros followed by a one. Concatenate these blocks. Its total bit length J=sum j satisfies 2^J>3^A: by induction along the forward decoding path, p<=2^J, and for a nonempty path p+3^A<=2^J from the first decoding equation and the bound on the remaining path. This is path_budget in SeamMass.lean. Thus each word in W_A has at least B_A bits.

For fixed A, the first B=B_A bits uniquely identify p. In fact, if two words from integer states at the same exponent A share B initial bits, their numerators agree mod 2^(B+1). Prove by induction on B:
- B=0: both are odd.
- If the first complete block is contained in these B bits, its length j is the position of the first one in both prefixes. The unique a determined by j gives equal next exponent A-a. Apply induction to the two remaining words with B-j bits. Multiplying their congruence by 2^j and subtracting the common 3^A gives the claimed congruence.
- If no one occurs in the B bits and B>0, both first exponents exceed B. Both numerators plus 3^A vanish mod 2^(B+1).

The induction applies when B does not exceed either remaining word length; an empty suffix is possible only at B=0. The admissible numerator interval (3^A/2,3^A) has length smaller than 2^(B+1), so congruence implies equality, then word uniqueness. No density or probabilistic independence assumption is used.

Because j=2 is impossible, the binary code consists of blocks 1 and 00...01 with at least two zeros in each longer block. Its prefixes are accepted by the following automaton:
- boundary state 0: one -> 0, zero -> 1;
- after exactly one zero, state 1: zero -> 2, one forbidden;
- after at least two zeros, state 2: zero -> 2, one -> 0.

Every state is a valid stopping state for a prefix. Starting counts f(0)=(1,1,1), the length-n extension count vector satisfies f(n+1)=(f0+f1,f2,f2+f0). Set S(n)=f0(n). The prefix injection proves N_A<=S(B_A).

## 4. Exponential mass bound and certified error formula

The positive recurrence matrix maps v=(9,7,12) to (16,12,21), componentwise <=(16/9)*v. The initial vector is <=v/7. Induction gives

    S(B) <= (9/7)*(16/9)^B.

The integer-scaled vector induction is kernel-checked as prefix_majorant. Since 2^B_A<=3^A and B_A>=floor(3A/2) (3^2>2^3),

    (3/2)*N_A/3^A <= (27/14)*(8/9)^B_A
                    <= (27/14)*(8/9)^floor(3A/2).

Writing r=8/9, the geometric sum for A>=2t is (1+r)r^(3t)/(1-r^3); for A>=2t+1 it is r^(3t+1)+(1+r)r^(3t+3)/(1-r^3). Every word omitted by the c_g cutoff has cumulative drop >=g, hence A>=g. This proves the announced exponential tail and effective approximability.

For tighter numerical upper bounds, enumerate the exact finite ideal tree restricted by total valuation A<=M. This enumerates complete same-level rays (finite because the rational numerator deficit doubles). Then sum the exact recurrence bounds S(B_A)/3^A for M<A<=L and the geometric bound for A>L. The supplied script uses only integer arithmetic and fractions. The values through A=24 are exact enumeration counts under the ideal grammar; the numerical enclosure is reproducible but not separately Lean certified.

## 5. Consequence for ongoing real inverse work

This is an entropy obstruction to explosive *weighted* ideal inverse mass: there are exponentially fewer distinct legal prefixes than the full binary residue space. The proof is independent of surviving gate index and does not need a gap bound. It does not directly control the real grammar at arbitrarily large gaps; in particular real near-boundary even cross-level transitions can have j=2, and the fixed-gap approximation is not uniform across all levels. The natural next step is to control these rare seam transitions and obtain a genuinely uniform growing-window estimate, or a root-specific invariant. No candidate representative is discharged by this theorem alone.
