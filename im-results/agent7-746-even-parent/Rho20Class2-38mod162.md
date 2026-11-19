# Rho-20 residual class 2: an infinite (a\equiv38\pmod{54}) root-excluded subfamily

**Status.** Exact arithmetic derivation at the already source-verified `ResetParent` grammar level. The formulas and modular table below are explicit and reproducible; this family-specific parent-tree argument has **not yet been compiled in Lean**. Keep it in `im-results/` until source-level formalization and adversarial review are complete.

This resolves one entire modulo-54 phase inside the residual `a mod 18 = 2` class identified in [Agent 10's rho-20 analysis](../agent10-cascade/T0-RHO20-TWO-OF-THREE-LIFTS.md). It does not settle the other two `a mod 54` phases, the whole #746 family, or BB(6).

## Theorem target

For every
[
a=38+54n\quad(n\ge0),\qquad
K=97\cdot2^{a-7}+48,
]
put
[
p=2^K,\quad q=2^{K-a},\quad r=K+4-a,\quad
B=(2K+7)2^r,
]
[
D=(B-16p+2K+1)/3,\qquad E=8p+K-D.
]
The intended conclusion is
[
\neg\,\operatorname{ResetChain}(2,E).
]
Here `ResetChain` and `ResetParent` are the exact source-C first-reset grammar in `im-results/agent10-cascade/ResetChain.lean` and `FirstInverseComplete.lean`; in particular, no bounded valuation cutoff is being introduced.

The proof identifies the complete inverse-parent tree of (E): it is a single chain ending at a non-root state with no parent.

## Initial two odd edges

Let (X=2E+5). Direct substitution gives
[
3X=80p+2K+13-2B,
\qquad
X/p=21/2-3296/(3\cdot2^a)+(2K+13)/(3p).
]
For the first odd parent define
[
h=2X/3-4p-K-4.
]
Then (\operatorname{ResetParent}(h,E)) is the (t=0,k=K-1) odd edge.

The next numerator (X_1=2h+5) satisfies
[
9X_1=248p-8B-10K+25,
\qquad
X_1/p=6-13184/(9\cdot2^a)-(10K-25)/(9p).
]
Define
[
y_0=2X_1/3-2p-K-3.
]
Then (\operatorname{ResetParent}(y_0,h)) is the (t=0,k=K-2) odd edge.

For (a\ge38), (K=97\cdot2^{a-7}+48) gives (K<2^a\le q), so (q>K). The displayed ratio identities yield the useful strict bounds
[
28/3<X/p<21/2,\
4<E/p<6,\
59/10<X_1/p<6,\
2p<h<3p-1.
]
The first two inequalities put (E) in the even-parent gap ((4p,6p)). Since (X\equiv18\pmod{27}), its only possible odd exponents are (t=0,1): (X/3\in(3p,4p)) is in the (k=K-1) source band, while (2X/9\in(2p,3p)) is in a gap. Thus (h) is the unique parent of (E).

Likewise (X_1\equiv9\pmod{27}), so only (t=0,1) are possible at (h). Here (X_1/3\in(3p/2,2p)) is in the (k=K-2) source band, while (2X_1/9\in(p,3p/2)) is in a gap. The bound on (h) excludes even parents. Thus (y_0) is the unique parent of (h).

The exact congruences (X\equiv18\pmod{27}) and (X_1\equiv9\pmod{27}) are established below.

## The same-level even chain

Set
[
L=K-2,\
D_0=2p-y_0,\
G=D_0+L.
]
Algebra gives the particularly useful closed forms
[
D_0=(26368q+47K+31)/27,\
G=(26368q+74K-23)/27.
]
For (j\ge0), define
[
D_j=2^jG-L,\
y_j=2p-D_j.
]
Then (y_0) agrees with the initial parent above, and
[
y_{j+1}=2y_j-2p-L.
]
Consequently (\operatorname{ResetParent}(y_{j+1},y_j)) is the even edge at level (k=L=K-2) whenever
[
3p/2\le y_j\le2p-3.
]

Since (q>K),
[
G<1024q,\
D_0>3.
]
For every (0\le j\le a-11),
[
3\le D_j<2^jG\le2^{a-11}\cdot1024q=p/2,
]
hence
[
3p/2\le y_j\le2p-3.
]
Thus all (a-10) same-level even-parent edges exist.

The crucial new observation is the exact numerator formula
[
X_j:=2y_j+5=A-2^{j+1}G,
\qquad A:=4p+2K+1.
]
For the chosen congruence class, (A\equiv6\pmod9) and (G\equiv0\pmod9). Therefore
[
X_j\equiv6\pmod9
\quad\text{for every }j\ge0.
]
Every (X_j) has 3-adic valuation exactly one. In particular, the only possible odd-parent exponent is (t=0).

For (j\le a-11), the corresponding odd source coordinate is
[
X_j/3=(2y_j+5)/3\in(p,4p/3),
]
which lies strictly between the adjacent source bands ([3p/4+1,p-1]) and ([3p/2+1,2p-1]). Hence there is no odd parent. The even edge above is the **unique** parent of every (y_j) with (j\le a-11).

## Terminal gap

At (j=a-10), the closed form for (G) gives
[
\frac{D_{a-10}}p
=\frac{103}{108}
 +\frac{74K-23}{27648q}
 -\frac{K-2}{2^a q}.
]
Using (q>K) and (a\ge38), both correction terms are positive and less than (1/100). Since
[
103/108-1/100>15/16,
\qquad
103/108+1/100<1,
]
we obtain
[
15p/16<D_{a-10}<p,
\qquad
p<y_{a-10}<17p/16.
]
This terminal state lies in an even-parent gap: it is above the upper endpoint (p-3) of the (k=K-3) band and below the lower endpoint (3p/2-1) of the (k=K-2) band.

Its only possible odd exponent is (t=0), since (X_{a-10}\equiv6\pmod9). But
[
(2y_{a-10}+5)/3\in(2p/3,3p/4),
]
which is the gap between the (k=K-4) and (k=K-3) odd source bands. Thus (y_{a-10}) has **no parent at all**.

Combining the uniqueness statements, the entire inverse-parent tree of (E) is
[
E\leftarrow h\leftarrow y_0\leftarrow y_1
\leftarrow\cdots\leftarrow y_{a-10},
]
and the final state is not the root (2). Therefore no `ResetChain` from (2) reaches (E).

## Exact modular certificate

For (a=38+54n), (2^{a-7}\pmod{243}) has period (162), so (a\pmod{162}) cycles through (38,92,146). Also (2^{54}\equiv82\pmod{162}), (2^{31}\equiv146\pmod{162}), and (146\cdot82\equiv146\pmod{162}). Hence (2^{a-7}\equiv146\pmod{162}) and (K\equiv116\pmod{162}) throughout this entire class.

The three residue rows are:

| (a\bmod162) | (K\bmod243) | (r\bmod162) | (2^K\bmod243) | (q\bmod243) | (2^r\bmod243) | (B\bmod243) |
|---:|---:|---:|---:|---:|---:|---:|
| 38 | 35 | 82 | 175 | 91 | 241 | 89 |
| 92 | 197 | 28 | 175 | 10 | 160 | 8 |
| 146 | 116 | 136 | 175 | 172 | 79 | 170 |

In all three rows, direct substitution gives the same decisive residues:
[
80p+2K+13-2B\equiv54\pmod{81},
]
so (X\equiv18\pmod{27}), and
[
248p-8B-10K+25\equiv81\pmod{243},
]
so (X_1\equiv9\pmod{27}). Also
[
A=4p+2K+1\equiv6\pmod9,
]
and
[
26368q+74K-23\equiv0\pmod{243},
]
so (G\equiv0\pmod9).

The small modular certificate is reproduced by `rho20_class2_mod162.mjs`. The period argument and three-row residue table, not a finite sample, establish the congruences for every (n\ge0).

## Scope and next steps

This resolves the entire `a mod 54 = 38` phase inside residual `a mod 18 = 2`; the `a mod 54 = 2` and `20` phases remain open. The next useful work is:

1. Formalize the modular certificate and the (q>K) inequalities in Lean.
2. Prove the unique-parent lemmas directly for `CascadeResetInverse.ResetParent`.
3. Deduce `¬ ResetChain 2 E` and compile it through the existing manual source workflow.
4. Ask Agent 10 to check the (D_j), (G), and terminal-gap algebra independently before promoting any synthesis claim.

The underlying grammar is source-complete in `FirstInverseComplete.lean` and `ResetChain.lean`; this note supplies a new parameterized parent-tree argument, not a claim that the whole #746 machine is nonhalting.
