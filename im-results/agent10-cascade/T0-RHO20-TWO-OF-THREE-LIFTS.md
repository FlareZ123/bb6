# Rho-20 phase: two of three K-lifts have a parentless entry

**Status:** exact paper-level arithmetic over the original-source ResetParent grammar. The first-reset inverse equivalence and blank-root ResetChain equivalence are source-certified in the existing Agent 10 workflow, but the new valuation-two lemma below has not been formalized or Lean-compiled. This refines the sole phase left by the eight-of-nine table; it does not decide the final lift, machine #746, or BB(6).

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
A direct rearrangement of the definitions gives the useful identity
\[
3X+2B=80p+2K+13.
\tag{2}
\]

## The rho-20 lift cycle modulo 27

Fix a, and let K'=K+54. Since 2^54≡1 mod81,
\[
2^{K'}\equiv2^K\pmod{81},
\qquad
2^{r+54}\equiv2^r\pmod{81}.
\]
Also c'=2K'+7=c+108≡c+27 mod81, so
\[
B(K')=c'2^{r+54}
\equiv B(K)+27\cdot2^r\pmod{81}.
\]
Both K and a are even, hence r=K+4-a is even and 2^r≡1 mod3. Therefore
\[
2B(K')\equiv2B(K)+54\pmod{81}.
\]
Applying (2) at K' and K, the 80p term is unchanged modulo 81 and 2K increases by 108. Consequently
\[
3X(K')\equiv3X(K)+108-54
\equiv3X(K)+54\pmod{81},
\]
which is equivalent to
\[
\boxed{X(K+54)\equiv X(K)+18\pmod{27}.}
\tag{3}
\]
The same relation applies a second time. Thus the three lifts K,K+54,K+108 of a fixed residue modulo 54 produce
\[
X(K),\quad X(K)+18,\quad X(K)+36
\pmod{27}.
\]
Because X(K)≡0 mod9, these three residues are exactly 0,9,18 in some order. Exactly one lift has 27|X; the other two have
\[
\boxed{v_3(X)=2.}
\tag{4}
\]

For each fixed even a>=18, the admissible real interval for K has width
\[
\frac{7\cdot2^a}{128}>162.
\]
It therefore contains an integer in every residue class modulo 162. In particular, all three lifts of the rho-20 class occur in the candidate interval, and exactly two of them satisfy (4).

## A valuation-two candidate has no odd parent

Suppose v3(X)=2. Any odd ResetParent of E must satisfy
\[
X=3^{t+1}d,\qquad d\text{ odd},
\]
so necessarily t=1 and d=X/9. The odd-parent source-band coordinate is
\[
P=2^td=\frac{2X}{9}.
\tag{5}
\]
From the exact expression for E/p,
\[
\frac Xp
=\frac{80-32x}{3}+\frac{2K+13}{3p}.
\]
The interval for x gives
\[
\frac{28}{3}<\frac Xp<\frac{21}{2}+\frac13
=\frac{65}{6},
\]
where the upper estimate uses 2K+13<p, valid for K>=266. Combining with (5),
\[
\boxed{\frac{56}{27}<\frac Pp<\frac{65}{27},}
\qquad
\boxed{2p<P<3p.}
\tag{6}
\]
But an odd ResetParent at source level L requires
\[
6\cdot2^L+1\le P\le8\cdot2^L-1.
\tag{7}
\]
If L<=K-2, the upper endpoint in (7) is at most 2p-1. If L>=K-1, its lower endpoint is at least 3p+1. Both contradict (6). Hence E has no odd parent.

## There is no even parent either

The even arm of ResetParent requires
\[
6\cdot2^L-1\le E\le8\cdot2^L-3.
\]
By (1), if L<=K-1, the upper endpoint is at most 4p-3<E. If L>=K, the lower endpoint is at least 6p-1>E. Thus E has no even parent.

So E is parentless in the exact two-arm ResetParent relation. By the source-certified theorem root_reset_chain_iff in [ResetChain.lean](ResetChain.lean), it cannot lie on a finite reset-parent chain from blank-root height 2:
\[
\boxed{\neg\operatorname{ResetChain}(2,E).}
\]

## Combined residue-class scope

For each even a>=18, the nine classes modulo 54 compatible with K≡2 mod6 each have three lifts modulo 162.

- The eight non-rho-20 classes are excluded by the existing eight-of-nine phase theorem, giving 24 excluded lifts.
- In the rho-20 class, (3)–(7) exclude two of its three lifts, giving two more.

Therefore **26 of the 27 candidate K-residue classes modulo 162 are root-excluded** for every even a>=18. This is a count of arithmetic parameter classes in one structured t=0, q=0 candidate family. It is not a density statement about machines, halting histories, or the full BB(6) table space.

The unique remaining lift is characterized by 27|X=2E+5, so its incoming odd-parent valuation is at least t=2. This note does not resolve that lift. The K≡3 mod6 sector, nonzero same-level reset depths q>0, other fatal branches, and other #746 roots also remain open.

## Exact regression witness

For a=18, the rho-20 interval contains K=198686,198740,198794, the three lifts modulo 162. Exact BigInt arithmetic gives
\[
X\bmod27=18,9,0,
\qquad
v_3(X)=2,2,3,
\]
respectively. This checks the lift-cycle formula on one concrete interval; the proof above supplies the infinite statement.

## Next mathematical target

Analyze the unique rho-20 lift with 27|X, combining the next 3-adic digit of X/27 with the exact dyadic source-band condition for valuation t>=2. Avoid another finite forward-orbit scan: the remaining obstruction is the interaction between the unique higher 3-adic lift and the odd-parent dyadic band.
