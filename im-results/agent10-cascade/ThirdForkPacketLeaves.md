# Uniform linear family of parentless third-valuation feeders on every surviving #746 gate ray

**Status (23 November 2026): paper-level all-index composition.** This combines the original-source exact ResetParent grammar, the already source-checked [unique 3-adic Hensel depth residue](../agent7-fatal-density/RayDepthResidue.lean), and the source-checked [third-valuation parent-gap theorem](RayTThreeGap.lean). The new modulo-243 packet counting and full geometry conjunction have **not** been kernel-compiled together. It is an exact mathematical statement about the genuine first-reset **inverse graph**, not an actual blank-root reachability or nonhalting claim.

## Theorem

Fix any candidate index \(n\ge257\) with \(n\bmod6\in\{4,5\}\). Define

\[
p=2^n,\quad c=2n+3,\quad a=\lfloor\log_2c\rfloor,\quad
J=n-a,\quad u_j=4p+n-1-c2^j.
\]

The ray begins at the authentic possible fatal height \(u_0=4p-n-4\). Put

\[
B=\left\lfloor\frac{J-13}{162}\right\rfloor.
\]

In **every** complete 162-index packet \(b\in\{0,\ldots,B-1\}\), the 81 even indices

\[
j\in\{162b,\ 162b+2,\ \ldots,\ 162b+160\}
\]

contain **exactly three** values for which \(81\mid X_j:=2u_j+5\). Their quotient residues \(d_j=X_j/81\bmod3\) are precisely \(0,1,2\), once each.

Each of the three carries a distinct **genuine odd first-reset source predecessor with valuation \(t=3\)**:

\[
d_j=X_j/81,\qquad
h_j=16d_j-p-n-2,\qquad
\mathrm{ResetParent}(h_j,u_j).
\]

Every such \(h_j\) lies in the strict gap \(p/2<h_j<3p/4\), where no even parent exists. In each packet **two** of the three satisfy \(h_j\bmod3\ne2\), making any odd parent impossible as well. These two source heights are **parentless** in the complete, untruncated ResetParent grammar, and all such heights are pairwise distinct between packets.

**Consequently, every eligible gate ray contains at least**

\[
\boxed{2\left\lfloor
\frac{n-\lfloor\log_2(2n+3)\rfloor-13}{162}
\right\rfloor}
\]

**distinct genuine third-valuation feeders that themselves have no source predecessor.** This is a uniform \(\Omega(n)\) inverse-graph pruning count. The third feeder in each packet is *not* certified to be rooted or unrooted by this residue argument.

## Proof 1: the exact three-quotient permutation

The source-certified theorem
[`depthResidue_iff`](../agent7-fatal-density/RayDepthResidue.lean)
says that for every surviving \(n\) there is exactly one ray residue
\(j_0=\mathrm{depthResidue}(n,3)\in[0,54)\) such that

\[
3^4=81\mid\mathrm{signedZ}(n,j_0).
\]

The physical ray numerator equals signedZ on the admissible prefix.
Since \(2^{54}\equiv82=1+81\pmod{243}\) and
\(2^{108}\equiv163=1+162\pmod{243}\), and since

\[
X_j=8p+2n+3-2c\,2^j,
\]

we have the exact congruence

\[
X_{j_0+54t}\equiv
X_{j_0}-81t(2c\,2^{j_0})
\pmod{243},\qquad t=0,1,2.
\]

The coefficient \(2c\,2^{j_0}\) is nonzero modulo three because
\(n\bmod6\in\{4,5\}\) implies \(3\nmid c\).
Since \(81\mid X_{j_0}\), dividing the three congruences by 81 modulo
three gives an affine permutation of \(0,1,2\) for the quotient \(X/81\bmod3\).
The exact residue characterization also rules out all other even indices
in the 162-index block. Because \(2^{162}\equiv1\pmod{243}\),
the same three-quotient permutation repeats in every complete block.

## Proof 2: genuine original-source predecessors and a strict parentless gap

Every index in these complete packets satisfies

\[
0\le j\le162B-2\le J-15.
\]

The dyadic definition of \(a\) gives \(c2^J<2p\), hence
\(c2^j<p/4096\). The exact numerator obeys

\[
8p-p/2048<X_j<8p+2n+3.
\]

For \(81\mid X_j\), the quotient \(d_j=X_j/81\) is positive and odd,
and the source odd-band inequalities at level \(k=n-3\) follow:

\[
6\cdot 2^{n-3}+1\le8d_j\le8\cdot2^{n-3}-1.
\]

The bound \(n\ge257\) makes the additive \(O(n)\) terms strictly
smaller than the positive dyadic margins in these inequalities.
The source-output equation is \(2u_j+5=3^4d_j\), and
the source-height equation is

\[
2(8d_j)=8\cdot2^{n-3}+h_j+(n-3)+5
\]

by definition of \(h_j=16d_j-p-n-2\). The same lower bound proves
\(h_j\ge0\). This is **exactly** the original source-certified
odd ResetParent grammar at valuation \(t=3\), with no truncation to
a preferred valuation.

The same equations force \(p/2<h_j<3p/4\). This gap lies strictly
between adjacent even-parent bands. The original-source result
[`ray_tthree_parent_gap`](RayTThreeGap.lean) already proves that
physical gap when the high-margin source assumptions hold; those
assumptions follow from \(j\le J-15\) and \(n\ge257\).
Therefore **no even source parent** can enter \(h_j\).

Any odd parent of \(h_j\) must satisfy \(3\mid2h_j+5\), or equivalently
\(h_j\bmod3=2\).
The certified source-sector lemma
[`pow_sector_mod_three`](../agent7-fatal-density/RayDepthHensel.lean)
gives \(p\equiv n\pmod3\); since
\(h_j=16d_j-p-n-2\), reduction yields

\[
h_j\equiv\begin{cases}
d_j-1 & n\equiv4\pmod6,\\
d_j   & n\equiv5\pmod6
\end{cases}
\pmod3.
\]

In the first sector only \(d_j\equiv0\) could permit an odd parent;
in the second sector only \(d_j\equiv2\) could. Thus **two of the three**
quotient residue classes in *each* packet have no odd parent either:
these two \(h_j\) are source-parentless (and hence blank-root excluded).
The existing source-checked
[`ray_tthree_parent_dead`](RayTThreeGap.lean)
already verifies the weaker blank-root conclusion for a given \(h_j\).

Finally, the map \(j\mapsto X_j\) is strictly decreasing, so the
\(d_j\) and hence the \(h_j\) are pairwise distinct across all packets.

## Reproduction, scope, and exact remaining Lean edge

The dependency-free
[`third_fork_packet_leaves.mjs`](third_fork_packet_leaves.mjs)
checks every candidate index in each complete packet using BigInt,
including the source band and reset equations, gap inequalities,
residues, and uniqueness. The same exact-integer logic was independently
evaluated in the available JavaScript runtime:

| n | J | complete 162-index packets | distinct certified parentless t=3 feeders |
|---:|---:|---:|---:|
| 257 | 248 | 1 | 2 |
| 262 | 253 | 1 | 2 |
| 263 | 254 | 1 | 2 |
| 1000 | 990 | 6 | 12 |
| 10000 | 9986 | 61 | 122 |

A direct source-checked all-index Lean integration would compose
[`depthResidue_iff`](../agent7-fatal-density/RayDepthResidue.lean),
[`signedZ_shift_digit_mod`](../agent7-fatal-density/RayDepthHensel.lean)
at \(k=3\), and
[`ray_tthree_parent_gap`](RayTThreeGap.lean) with the physical
\(j\le J-15\) bound. The three-class quotient permutation and
full packet count remain paper-proved pending that composition.
No individual parentless synthetic feeder decides the source root
reachability of its corresponding ray vertex \(u_j\).

This result is complementary to the
[uniform logarithmic fan-in at one ray vertex](EveryGateRayFanin.md):
the latter constructs many distinct **incoming** inverse edges at a
single vertex, while the present theorem certifies linearly many
**terminal, unreachable** odd side branches across the entire ray.
