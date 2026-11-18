# Rho-20 phase: eight of nine K-lifts modulo 486 are root-excluded

**Status:** exact paper-level arithmetic over the original-source ResetParent grammar. The first-reset inverse equivalence and blank-root ResetChain equivalence are source-certified in the existing Agent 10 workflow, but the new valuation-two/three lemmas below have not been formalized or Lean-compiled. This refines the sole phase left by the eight-of-nine table; it does not decide the final lift, machine #746, or BB(6).

## Setup

Let a>=18 be even, K>=266, K≡2 mod6, and
\[
x=\frac{2K+7}{2^a}\in\left[\frac{97}{64},\frac{13}{8}\right],
\qquad \rho=K+6a\equiv20\pmod{54}.
\]
Put
\[
p=2^K,\quad c=2K+7,\quad r=K+4-a,\quad
B=c2^r,\quad
D=\frac{B-16p+2K+1}{3},\quad
E=8p+K-D,\quad X=2E+5.
\]
These are the exact t=0, q=0 candidate parameters of [the eight-of-nine phase analysis](T0-EIGHT-OF-NINE-PHASES-ROOT-EXCLUSION.md). In particular, its modular table gives
\[
X\equiv0\pmod9,
\]
and its interval calculation gives
\[
\frac{14}{3}<\frac Ep<\frac{16}{3},
\qquad 4p<E<6p-1.
\tag{1}
\]
A direct rearrangement of the definitions gives
\[
3X+2B=80p+2K+13.
\tag{2}
\]
It also gives
\[
\frac Xp=\frac{80-32x}{3}+\frac{2K+13}{3p}.
\tag{3}
\]
The interval and K>=266 imply
\[
\frac{28}{3}<\frac Xp<\frac{65}{6}.
\tag{4}
\]

## First lift: v3(X)=2 is parentless

Fix a and let K'=K+54. Since 2^54≡1 mod81,
\[
2^{K'}\equiv2^K\pmod{81},
\qquad
2^{r+54}\equiv2^r\pmod{81}.
\]
Also c'=2K'+7=c+108≡c+27 mod81, so
\[
B(K')\equiv B(K)+27\cdot2^r\pmod{81}.
\]
Both K and a are even, hence r is even and 2^r≡1 mod3. Therefore
\[
2B(K')\equiv2B(K)+54\pmod{81}.
\]
Applying (2) at K' and K gives
\[
3X(K')\equiv3X(K)+108-54
\equiv3X(K)+54\pmod{81},
\]
hence
\[
\boxed{X(K+54)\equiv X(K)+18\pmod{27}.}
\tag{5}
\]
The three lifts K,K+54,K+108 of a fixed residue modulo 54 therefore give X residues 0,9,18 modulo 27 in some order, since rho=20 gives X≡0 mod9. Exactly two lifts have v3(X)=2; the unique remaining lift has 27|X.

If v3(X)=2, any odd ResetParent of E must satisfy X=3^(t+1)d with d odd, so t=1 and d=X/9. Its source-band coordinate is
\[
P=2^td=\frac{2X}{9}.
\]
By (4),
\[
\frac{56}{27}<\frac Pp<\frac{65}{27},
\qquad 2p<P<3p.
\tag{6}
\]
An odd parent at source level L requires
\[
6\cdot2^L+1\le P\le8\cdot2^L-1.
\tag{7}
\]
For L<=K-2 the upper endpoint is at most 2p-1; for L>=K-1 the lower endpoint is at least 3p+1. Thus E has no odd parent. By (1), it also has no even parent: even-parent target bands are [6*2^L-1,8*2^L-3], with levels L<=K-1 ending at most 4p-3 and levels L>=K starting at least 6p-1. Hence E is parentless whenever v3(X)=2.

## Second lift: v3(X)=3 also has a parentless predecessor

Now suppose v3(X)=3. Any odd parent of E must have t=2 and d=X/27, so its source-band coordinate is
\[
P=2^td=\frac{4X}{27}.
\]
Equation (4) gives
\[
\frac{112}{81}<\frac Pp<\frac{130}{81}<2.
\tag{8}
\]
The only possible odd source band is therefore L=K-2, whose interval is [3p/2+1,2p-1]. If P is below that band, E has no odd parent and is already parentless by (1). Suppose instead that P lies in this band.

Define
\[
\Delta=P-\frac32p.
\]
Using (3), an exact simplification gives
\[
\boxed{
\Delta=\frac{p(397-256x)}{162}
       +\frac{4(2K+13)}{81}.
}
\tag{9}
\]
Write
\[
N=397\cdot2^a-256(2K+7).
\]
Since a>=18, 397*2^a and 512K are divisible by 512, while 1792≡256 mod512. Hence
\[
N\equiv256\pmod{512},
\]
so N is nonzero and |N|>=256. Also 2^a<2K+7 by the x interval.

If N<0, (9) gives
\[
\Delta\le-\frac{128p}{81\cdot2^a}
              +\frac{4(2K+13)}{81}<0,
\]
because 32p>(2K+7)(2K+13) for K>=266. This contradicts P>=3p/2+1. Therefore N>0. Then (9) gives
\[
\Delta\ge\frac{128p}{81(2K+7)}>\frac K2,
\]
where the last inequality follows, for K>=266, from 256*2^K>81K(2K+7). Thus
\[
P>\frac32p+\frac K2.
\tag{10}
\]

The unique odd parent is at L=K-2 and has height
\[
h=2P-8\cdot2^{K-2}-(K-2)-5
 =2P-2p-K-3
 =p+2\Delta-K-3.
\]
By (10), h>p-3. By (8), P/p<130/81, so h/p<260/81-2=98/81. Since 98/81<3/2 and K>=266, h<98p/81<3p/2-1. Consequently
\[
\boxed{p-3<h<\frac32p-1.}
\tag{11}
\]
No even-parent target band intersects (11): levels L<=K-3 end at p-3, while levels L>=K-2 start at 3p/2-1.

There is no odd parent of h either. Since P=4d, p≡1 mod3 and K≡2 mod3,
\[
h=8d-2p-K-3\equiv2d+2\pmod3.
\]
Here 3 does not divide d because v3(X)=3, so h≡1 or 0 mod3. Every odd-parent target u must satisfy 2u+5≡0 mod3, hence u≡2 mod3. Thus h has no odd parent.

So when P is in its only possible band, E has exactly one odd parent h and h is parentless. When P is outside the band, E itself is parentless. In either case, E is outside the genuine blank-root ResetChain.

## Third lift: the unique surviving class has 81|X

For the unique K class modulo 162 with 27|X, consider K'=K+162. The modular identity
\[
2^{162}\equiv1\pmod{243}
\]
and c'=c+324≡c+81 mod243 give
\[
B(K')\equiv B(K)+81\cdot2^r\pmod{243}.
\]
Again r is even, so 2^r≡1 mod3 and 2B(K')≡2B(K)+162 mod243. The term 2K increases by 324≡81 mod243. Applying (2),
\[
3X(K')\equiv3X(K)+81-162
\equiv3X(K)+162\pmod{243},
\]
which yields
\[
\boxed{X(K+162)\equiv X(K)+54\pmod{81}.}
\tag{12}
\]
The three lifts K,K+162,K+324 of the surviving class modulo 162 therefore give X residues 0,27,54 modulo 81 in some order. Exactly two have v3(X)=3 and are excluded by the preceding argument; the unique remaining lift has 81|X and incoming odd valuation t>=3.

## Combined residue-class scope

For each even a>=18, the admissible K interval has width
\[
\frac{7\cdot2^a}{128}>486.
\]
It contains an integer in every residue class modulo 486. The nine K classes modulo 54 compatible with K≡2 mod6 each have nine lifts modulo 486.

- The eight non-rho-20 phases are excluded by the existing eight-of-nine theorem: 8*9=72 classes.
- In the rho-20 phase, (5)-(7) exclude six of its nine lifts with v3(X)=2.
- The remaining three lifts are refined by (12); two have v3(X)=3 and are excluded by the second-valuation argument.

Therefore **80 of the 81 candidate K-residue classes modulo 486 are root-excluded** for every even a>=18. This counts arithmetic parameter classes in one structured t=0, q=0 candidate family. It is not a density statement about machines, halting histories, or the full BB(6) table space.

The unique remaining lift is characterized by
\[
81\mid X=2E+5,
\]
so its incoming odd-parent valuation is at least t=3. This note does not resolve that lift. The K≡3 mod6 sector, nonzero same-level reset depths q>0, other fatal branches, and other #746 roots also remain open.

## Exact regression witnesses

For a=18, the rho-20 interval contains K=198686,198740,198794, the three lifts modulo 162. Exact BigInt arithmetic gives
\[
X\bmod27=18,9,0,
\qquad v_3(X)=2,2,3.
\]
The remaining v3=3 class has lifts K=198794,198956,199118 modulo 486, with
\[
X\bmod81=54,27,0,
\qquad v_3(X)=3,3,4.
\]
At K=198794, P=4X/27 lies in the L=K-2 band and its parent h satisfies h/p=1.107699... and h mod3=0; at K=210944, v3(X)=3 but P/p=1.407365..., so no odd source band exists. These are finite sanity checks; the inequalities and modular lifts above supply the infinite statements.

## Next mathematical target

Analyze the unique rho-20 lift with 81|X, combining the next 3-adic digit of X/81 with the exact dyadic source-band condition for valuation t>=3. Avoid another finite forward-orbit scan: the remaining obstruction is the interaction between the unique higher 3-adic lift and the odd-parent dyadic band.
