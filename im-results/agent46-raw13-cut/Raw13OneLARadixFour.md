# Raw13 1093: E0=1LA, a radix-four counter and complete return argument

Status: mathematical derivation, machine-specific Lean formalization in progress. The target is the partial table
`1RB1LD1RC0RB1LA1RE1LF0LA1LA0RD1LC---`.
The hole is F1. This is the final difficult E0 sibling of the two-hole parent with E0 and F1 unspecified. No global BB(6) conclusion follows.

## Frames

Tape words are nearest-first on both sides, with the scanned cell at the start of the left word. Trailing zeros on either side may be suppressed. Let P(U) replace each bit a of U by 1a. Define F_b(L,U) as A with left word L and right word 01b P(U), and E_b(X,U) as E with left b11X and right P(U). B=1000, and enc writes each little-endian binary digit a as a000; enc_s denotes fixed width s.

The following local rules are exact, with positive costs and arbitrary tails:
* At A, 11L -> L with 01 prepended on the right (2 steps); BL -> L with 1111 prepended (4); 1001L -> 01L with 01 prepended (6).
* Starting from F_b(B^n 0L,U), the B sweeps followed by the B-state return reach E_b(0^(4n)1L,U).
* E_0(X,U) reaches F_1(X,U) in 3 steps.
* F_b(11L,U) reaches F_0(L,bU); F_b(1001L,U) reaches F_0(01L,bU).
* For n>0, F_b(B^n11L,U) reaches F_1(L,1^(2n-1)0bU); F_b(B^n1001L,U) reaches F_1(01L,1^(2n-1)0bU).

For E_1, scan U at active indices 0 and 2 modulo 3. Its operation I increments the binary integer formed by these active positions, clears every preceding skipped bit, and preserves the untouched suffix. Thus each triple is a radix-four digit with a skipped middle bit. On success E_1(X,U) reaches F_0(X,I(U)). The terminal scans with lengths 3h, 3h+1, 3h+2 and all active bits 1 have the following outputs, respectively:
* F_0(X,0^(3h)1), an even extension;
* F_0(1X,0^(3h)1), an odd overflow;
* F_0(1X,0^(3h+1)1), an odd overflow.

These formulas follow from the finite scans E_1(X,0V) -> F_0(X,1V); E_1(X,1a0V) -> E_0(1^6 X,V); E_1(X,1a1V) -> E_1(1^6 X,V). After the recursive call on V, consume three pairs 11 on the left, which prepend 000 (the first marker is zero). For the 1a0 case, E_0 returns with marker 1 and consuming three pairs prepends 001. The empty scan returns F_0(X,1); the singleton 1 scan reaches E_0(111X,empty), then consumes one pair; the two-bit scan reaches F_0(111X,1), then consumes one pair. All are finite transition identities on arbitrary X.

## Capacity lemma

For each phase p in {0,1,2}, C_p(U) is the little-endian integer of complemented bits after excluding positions congruent to p mod 3. C=C_1 is the ordinary increment capacity, and M=min_p C_p. I^d is successful (without overflow) exactly when d<=C, and then C(I^d(U))=C-d. For the two other phases,
4 C_p(I^d(U))+1 >= C_p(U).
Indeed for d>0 let i be the highest active position changed by monotone addition. The suffix after i stays unchanged and skipped positions before i are zero after addition. If the touched prefix has length one the inequality follows directly. Otherwise its last three positions contain a skipped zero (for length three or greater), which is active in the other phase. That zero has at most two active positions above it within the prefix. Consequently 4 times the new complemented prefix value plus 1 is at least the old prefix value; appending the unchanged higher suffix preserves the inequality. The prefix-length-two case, if needed, has a skipped zero as well. Prepending r bits multiplies the appropriate phase capacity by at least 2^floor(2r/3), plus nonnegative contributions from the prefix. Prepending a prefix ending in 00 gives each phase capacity at least 1.

## Left carry and drain

An ordinary left carry on enc_s(z) with z+1<2^s increments z, flips the marker b, and calls I exactly if b=1. This follows by sweeping B through the initial ones of z and applying the first two frame rules. Batch carries use floor((number+b)/2) increments of U, provided no overflow is requested. At the top of the fixed-width counter the same sweep applies to the suffix explicitly.

Write S(xs)=000 enc(xs), D(s,z,xs)=enc_s(z)100 enc(xs), J(s,z,xs)=enc_s(z)1 enc(xs). All finite nonempty bit strings below end in 1. For S(0^k1 ys):
* k=0: one carry across the first zero, the 1001 special rule, another zero carry, then a pair give F_0(S(ys), 1(1-b) I^b(U)).
* k>=1: the first zero takes two carries and leaves D(1,0,remaining). Each additional zero takes 2^s carries through the width-s counter and leaves D(s+1,0,remaining). Thus after k zeros the marker is b and 2^(k-1) right increments have occurred. Another 2^k-1 ordinary carries bring the low counter to its maximum and marker 1-b. The special B^k1001 rule, then a zero carry and a pair give F_0(S(ys), 0 I(1^(2k-1)0(1-b) I^(2^k-1+b)(U))).
The last I either acts inside the prepended prefix, or (only when b=0, k=1 mod 3) passes through the entire prefix of length 2k+1, divisible by 3, and performs one additional I on U. Thus at most 2^k ordinary increments on U are needed, and at least 2k+2 bits are prepended. For k=0, two bits are prepended.

If M(U)>=2^n-1 for n=length(xs), all steps are ordinary and the output after removing k+1 bits has M>=2^(n-k-1)-1. For k>=1, the original active capacity after d<=2^k increments is at least 2^(n-1)-1; every other capacity after the prepend of at least four bits is at least M(U)-1, using the factor-four lemma. For k=0,b=0, the prepend alone suffices. For k=0,b=1, the active capacity is at least M(U)-1, and the others after prepending two bits are at least (M(U)-1)/2. Inductively the drain ends with F_0(empty,U') (or the original marker if the bit string was already empty). All right operations preserve the final 1 and never decrease length.

## Root return

Consider roots F_0(empty,U), F_1(empty,U), and F_0(enc(1),U), where U ends in 1 and length(U)>=3. From a root, ordinary left carries increment its unbounded binary left counter, and every second carry invokes I. Pad the left encoding with sufficiently many zero digits before each finite batch. Let v be the initial active value. If length(U) is divisible by 3, the first overflow extends U by one bit and is even; the next is odd. Otherwise the first overflow is odd. At the odd overflow, the number of right increments used is d=2^N-v, where N=2h+1>=3 is the active length at this overflow. The right word is U0=0^(L-1)1, L=3h+1 or 3h+2. The left word is 1 enc(x), with x=2d, 2d-1, or 2d+1 respectively for the three root types. Note v>0 for an initial length congruent to 0 or 1, and v=0 is possible only when the initial length is congruent to 2. M(U0)>=2^(N-1)-1; C(U0)=2^(N-1)-1 for L=3h+1, and 2^N-1 for L=3h+2. On 0U0, C=2^N-1 and M>=2^(N-1)-1.

### Even x

Here x=2d. Let the binary word of x be 0^k1ys. Starting with J(0,0,bits(x)), successive zero stages take 2^s carries through the width-s counter and increase its width by one. After k stages the marker is 1, the low counter is zero, and 2^(k-1)-1 right increments have been used. Another 2^k-1 ordinary carries reach maximum low counter and marker 0, giving total 2^k-1 right increments. The B^k11 rule yields F_1(S(ys),1^(2k-1)00 I^(2^k-1)(U0)).

If k<=N-2, the first drain is safe. The remaining length is <=N-k. For k>=2, the prepend of >=3 bits scales each phase by at least four; the two nonactive capacities are thus at least M(U0)-1>=2^(N-k)-1, and the active capacity before prepending is >=2^(N-2), then scales by at least four. For k=1 the single increment changes just the first bit of U0, losing at most one in any phase; the three-bit prepend again gives the required budget. If k=N-1, the increments are still possible and the prefix ending 00 gives minimum capacity >=1, enough because the remaining length is <=1. If k=N and L=3h+2, the increments are possible and ys is empty. Apply the general drain to each nonempty ys.

The only remaining cases are x=2^s, with s=N and L=3h+1, or s=N+1 and L=3h+2 (the latter requires v=0). Here C(U0)=2^(s-1)-1. After the s zero stages the right capacity is exhausted, marker is 1, and the left word is J(s,0,[1]). One ordinary carry increments the low counter to 1 but invokes a second odd overflow, giving F_0(1 enc_s(1) 1 enc([1]),U0). Consume the initial pair: the result is F_0(0^(4s-1)11000,0U0). Set n=s-1. This is a width-n zero counter followed by 00011000. The first 2^n carries increment that suffix's initial zero, yielding a width-n zero counter followed by 10011000. Then 2^n-1 ordinary carries bring the counter to maximum with marker 1. Total right increments: 2^n-1, possible on 0U0. The B^n1001 special rule yields F_1(011000,1^(2n-1)01 I^(2^n-1)(0U0)). The zero carry and pair now return to F_0(enc(1),U'). The last I either acts in the prefix, or crosses it (n=1 mod 3). In the first exceptional case there is still positive capacity on 0U0. In the second it is exhausted, but 0U0 has length divisible by 3, as does the prefix, so the last I is an even extension with no extra left 1. Thus both exceptional cases return to an allowed root.

### Odd x

Write x=2y+1. Consume the initial 11, yielding F_0(S(bits(y)),0U0). If y=0 this is already a root. Otherwise y<=2^N-1 except possibly y=2^N when the starting root is F_0(enc(1),U), v=0, L=3h+2. In the ordinary case the bit length is <=N. The initial run k=0 is safe and prepends 11, so the budget for the remaining <=N-1 bits holds. For k>=1 the first run uses <=2^k<=2^(N-1) right increments; C(0U0)=2^N-1 suffices. After the prepend the two other phases have capacities >=M(0U0)-1, and the active phase has at least 2^(N-1)-1. These suffice for the remaining <=N-k-1 bits. Then apply the general drain. For y=2^N only the run k=N occurs. Its initial 2^N-1 increments exhaust the active capacity, and the last I acts either in the prefix or crosses it and makes an even extension (both lengths divisible by 3). The result is F_0(empty,U').

Hence every root returns after a positive finite number of assigned transitions to one of the same three root forms. The finite blank-start seed and the exact local frame transitions must be checked against the original table to turn this derivation into a machine certificate. In particular the argument does not use an assumed eventual periodicity or a sampled suffix guard.
