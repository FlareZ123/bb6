# F119 factorization-free affine inverse fan

Intermediate result, Agent 32, 2026-11-25. Literal RLE `1RB0RB_1LB0LC_1RD1LC_1RE0RA_0RF1RA_---1LB` (upstream #417). Use Agent40's established [two-tag arithmetic reduction](../agent40-f119-ternary/README.md); this note extends its inverse machinery rather than repeating the reduction. Original upstream import remains unverified in this invocation. No root decision.

## Uniform inverse fan

Before the first power of 3, the section has tag 1 and generic transition

    x = 3^t(3k+r), r∈{1,2}
    y = (3^(t+1)+1)k + r*3^t + t+r+2

with k≥1 if r=1 and k≥0 if r=2. Every such transition grows x. Parameterize a target family as

    y(e) = (3^(e+H)-B)/D, e≡a (mod P),

where D≡1 (mod 3), B≥0, P≥1, 3^P≡1 (mod D), and 3^(a+H)≡B (mod D). This includes all positive powers at the initial node D=1,B=H=a=0,P=1.

Write p=3^t, M=3p+1, C=B+D(rp+t+r+2). Integrality of the inverse requires precisely

    3^(e+H) ≡ C (mod DM).

The parent family is (3^(e+H')-B')/D' with

    D'=DM, H'=H+t+1, B'=3pB+Dp(3t+2r+6).

The positivity and k guards must still be imposed to turn this arithmetic family into a valid edge; the program intentionally overapproximates by retaining all congruence-compatible nodes. D'≡1 mod3.

Modulo M the powers of 3 are precisely the distinct signed powers ±3^j for 0≤j≤t, since 3^(t+1)=-1. Thus their exact period is 2(t+1). Reduce C modulo M to rp+K_r where

    K_r=B+D(t+r+2)-(Dr-r)/3.

Here K2=K1+(2D+1)/3. For t≥2, 1<K1≤K2<2p/3+1 excludes both residues from the signed powers: rp+K_r lies strictly between p and 2p+1 for r=1, or between 2p+1 and 3p+1-p/3 for r=2. No signed power lies in either interval. K1>1 follows from B≥0,D≥1,t≥2. K2 increases by D when t increases by one, so if 3(K2-1)<2p and 4p>3D, both inequalities persist at all later t. Hence every target family has a finite computable valuation fan uniformly for all exponents e, with no factoring.

## Exact exponent lifting without factoring DM

First solve the signed-power congruence modulo M, then intersect its unique exponent residue with e≡a mod P using generalized CRT. If compatible this gives e=a1+P1 k. Let g=gcd(D,M), L=lcm(D,M)=DM/g, A=3^(a1+H) mod DM, J=3^P1 mod DM. Then C-A and J-1 are divisible by L, say C-A=Lδ and J=1+Lj. Since g divides L, L² is divisible by DM. Therefore

    A J^k ≡ C (mod DM) iff A j k ≡ δ (mod g).

Solve the linear congruence by one gcd and modular inversion. Its solution is empty or one progression. This is exact for k≥0, which covers all nonnegative e in the CRT class with canonical 0≤a1<P1. The new period is P1*g/gcd(Aj,g). Neither factorization of M or D nor a discrete logarithm on DM is needed. The key binomial lifting and cancellation are kernel-checked in LinearLift.lean (Lean 4.36.0-rc2, only propext, Classical.choice, Quot.sound). The F119 specialization is a paper derivation and executable arithmetic, not an upstream-source-connected Lean proof.

## Second-parent restriction (before the first power)

Agent40's first-power parent list gives two families D=10,H=2,B=33 or39, with e=3 or0 mod4 respectively. Both parent values are odd, so any generic parent must have odd t. All t≥5 are excluded by the cutoff above; t=3 is excluded because the four residues 35,69,41,75 are absent from ±{1,3,9,27} modulo82. At t=1 the exact next fan is:

| D | B | H | exponent residue mod20 |
|---|---|---|---|
| 100 | 627 | 4 | 19 |
| 100 | 687 | 4 | 3 |
| 100 | 681 | 4 | 0 |
| 100 | 741 | 4 | 8 |

The root x=4 is neither a power nor one of the first parents (which are odd). Thus the first power, if reached, has exponent in {0,3,8,19} mod20. If that first power is terminal, its exponent is in {0,3,39,48} mod60. This additional restriction does NOT apply to a terminal power reached after an earlier nonterminal power. No such later-power case has been excluded.

## Computational exploration and limitation

Run `python inverse_fan.py 8`. Observed congruence fan sizes at depths 1–8: 2,4,7,25,139,783,4568,27527. No necessary root hit before depth 8 (depths 0–7 checked). The sum of progression densities at depths 1–5 is 0.5,0.2,0.15667,0.12086,0.09886, counting overlaps. This is not a proof that the infinite fan closes. The rapid growth means a root-reaching or root-excluding invariant is needed rather than indefinitely increasing depth. The linear-lifting method is suitable for other exponential inverse problems independently of F119's unresolved outcome.
