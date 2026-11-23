# Exact word count for the #623 full-rectangle synchronization language

**Status:** unconditional finite-word combinatorial theorem, derived from the established exact four-residue criterion. It counts **all digit-pair words**, not authentic #623 orbit windows. No machine or BB(6) decision follows.

## Theorem

Let \(n\ge4\) and \(M=3^n\). A length-\(n\) word of ternary digit pairs \(w=((x_i,y_i))_{0\le i<n}\) defines

\[
X=\sum_{i=0}^{n-1}x_i3^i,\qquad Y=\sum_{i=0}^{n-1}y_i3^i.
\]

Among the \(M^2=3^{2n}\) possible words, exactly

\[
\boxed{M^2-30M+291}
\]

synchronize **both** the complete left and right input carry rectangles in the source-defined #623 transducers. Equivalently, the exact uniform-word probability is

\[
1-\frac{30}{3^n}+\frac{291}{3^{2n}}\qquad(n\ge4).
\]

At shorter lengths, the exact counts are \(0\) for \(n=2\) and \(195\) for \(n=3\); the displayed polynomial does not apply there.

## Proof: four forbidden modular strips

By [ExactSynchronizationCriterion.md](ExactSynchronizationCriterion.md), put \(N=M/3\), \(U=Y\), \(V=X+Y\pmod M\). This coordinate change is unimodular modulo \(M\), so the \(M^2\) digit-pair words correspond bijectively to \((U,V)\in(\mathbb Z/M)^2\). The four **bad** events are:

- \(A\): \([V-4U]_M\in\{-2,-1,0,1,2,3\}\pmod M\) (6 residues);
- \(C\): \([4V-U]_M\in\{-7,-6,-5,-4,-3,-2,-1,0,1\}\pmod M\) (9 residues);
- \(E\): \([U]_N\in\{-1,0\}\pmod N\) (2 residues, each with 3 lifts);
- \(F\): \([V]_N\in\{-2,-1,0\}\pmod N\) (3 residues, each with 3 lifts).

All occurrences of signed small residues mean their classes modulo the indicated modulus. For \(n\ge4\), \(N\ge27\), so the small residue sets do not self-overlap.

We count intersections:

| Intersection | Cardinality |
| --- | ---: |
| \(A,C,E,F\) individually | \(6M,9M,6M,9M\) |
| \(A\cap C\) | 54 |
| \(A\cap E\) | 36 |
| \(A\cap F\) | 54 |
| \(C\cap E\) | 54 |
| \(C\cap F\) | 81 |
| \(E\cap F\) | 54 |
| \(A\cap C\cap E\) | 12 |
| \(A\cap C\cap F\) | 12 |
| \(A\cap E\cap F\) | 15 |
| \(C\cap E\cap F\) | 15 |
| \(A\cap C\cap E\cap F\) | 12 |

The single-event counts are immediate. All six pair counts except \(A\cap C\) follow by solving a linear congruence in one variable: the coefficients \(1,4,-1,-4\) are units modulo \(M\). For \(A\cap C\), choose signed values \(a\in[-2,3]\), \(c\in[-7,1]\). Since
\[
c-4a\equiv15U\pmod M,
\]
there are three solutions \(U\) if and only if \(a\equiv c\pmod3\); each \(a\)-residue class modulo 3 occurs twice and each \(c\)-class occurs three times. Thus \(3(2\cdot3\cdot3)=54\).

For the triples and quadruple, write \(U=tN+e\) when \(E\) holds, with \(t\in\mathbb Z/3\) and \(e\in\{0,-1\}\), and write \(V=t'N+f\) when \(F\) holds, with \(f\in\{0,-1,-2\}\).

* \(A\cap C\cap E\): using \(c-4a\equiv15U\), the signed difference \(c-4a\in[-19,9]\) must equal \(15e\), since \(M\ge81\). Exactly four pairs \((a,c)\) work:
  \[
  (-1,-4),(0,0),(2,-7),(3,-3).
  \]
  Each has three lifts \(t\), hence 12 solutions.
* \(A\cap C\cap F\): similarly \(4c-a\equiv15V\pmod M\), with \(4c-a\in[-31,6]\), forces \(4c-a=15f\). The same four pairs work (with \(f=-1,0,-2,-1\) respectively), each with three lifts; total 12.
* \(A\cap E\cap F\): the signed low piece \(f-4e\) ranges from \(-2\) to 4, while \(a\in[-2,3]\). Hence \(a=f-4e\) and \(t'\equiv t\pmod3\). Precisely five of the six \((e,f)\) pairs work (all except \((-1,0)\)); each has three lifts: 15.
* \(C\cap E\cap F\): likewise \(c=4f-e\) and \(t'\equiv t\pmod3\). Exactly five of six \((e,f)\) pairs work (all except \((0,-2)\)), giving 15.
* The four \((a,c)\) pairs above all satisfy both \(E\) and \(F\) when the two dangerous constraints hold. Equivalently, among the six low pairs \((e,f)\), the four meeting both signed ranges are \((0,0),(0,-1),(-1,-1),(-1,-2)\). Therefore the fourfold intersection has size \(4\cdot3=12\).

Inclusion–exclusion now gives
\[
\begin{split}
|\mathrm{Bad}|&=(30M)-(54+36+54+54+81+54)\\
 &\quad +(12+12+15+15)-12\\
 &=30M-291.
\end{split}
\]
Subtracting from \(M^2\) completes the proof.

All arithmetic is with exact integer congruences; there is no asymptotic or independence assumption.

## Infinite-word classification and exact first-synchronization time

Let \((U,V)\in\mathbb Z_3^2\) be the two 3-adic integers whose least-significant-first digits encode an **infinite** ternary pair word. Let \(\nu_3(z)\in\mathbb N\cup\{\infty\}\), with \(\nu_3(0)=\infty\). Define the four (possibly infinite) contact orders
\[
h_A=\max_{a=-2,\ldots,3}\nu_3(V-4U-a),\qquad
h_C=\max_{c=-7,\ldots,1}\nu_3(4V-U-c),
\]
\[
h_E=\max_{e\in\{-1,0\}}\nu_3(U-e),\qquad
h_F=\max_{f\in\{-2,-1,0\}}\nu_3(V-f).
\]

**Exact stopping-time theorem.** The first prefix synchronizing both full rectangles has length
\[
\boxed{\tau(U,V)=\max(3,\;h_A+1,\;h_C+1,\;h_E+2,\;h_F+2)}
\tag{9}
\]
where \(\infty+k=\infty\). In particular, a given infinite word **never** synchronizes if and only if at least one of these equations holds in \(\mathbb Z_3\):
\[
V-4U\in\{-2,-1,0,1,2,3\},
\quad 4V-U\in\{-7,-6,-5,-4,-3,-2,-1,0,1\},
\]
\[
U\in\{-1,0\},\qquad V\in\{-2,-1,0\}.
\tag{10}
\]
Thus the exceptional infinite non-synchronizing language is **exactly a union of 20 affine 3-adic lines** in \(\mathbb Z_3^2\), not an unspecified fractal attractor.

*Proof.* For each \(n\ge3\), failure of one of the four inequalities of the exact synchronization criterion is equivalent to one of
\[
h_A\ge n,\quad h_C\ge n,\quad h_E\ge n-1,\quad h_F\ge n-1.
\]
For example, \(V-4U\bmod3^n\) lies in the six forbidden residues if and only if \(V-4U\) equals one of those six integers modulo \(3^n\); that is \(h_A\ge n\). The other three statements are identical, observing the \(3^{n-1}\) scale for \(U,V\). Therefore the first \(n\ge3\) at which all four failure inequalities are false is exactly (9). If \(h_A=\infty\), one of the six differences vanishes in \(\mathbb Z_3\), and analogously for the other contact orders. Conversely, if all contact orders are finite, choosing \(n\) larger than their four thresholds forces synchronization. No mixing or statistical assumptions are needed. Each of the 20 lines has a coefficient of one coordinate that is a 3-adic unit; each is a one-dimensional affine copy of \(\mathbb Z_3\), hence the exceptional set has 2D Haar measure zero and 3-adic Hausdorff dimension one under the usual max ultrametric.

**Exact uniform stopping-time law.** Under independent, uniformly distributed ternary digit pairs, the count of words whose *first* synchronization occurs at length \(n\) is

\[
\begin{array}{c|c}
n & \text{number among }9^n\text{ words}\\\hline
n=3&195\\
n=4&2667\\
n\ge5&60\cdot3^n-2328.
\end{array}
\]
Indeed, once synchronized, a word stays synchronized under any further digit pair; hence the number of first-hit words at length \(n\) is \(G_n-9G_{n-1}\), with \(G_3=195\) and \(G_n=9^n-30\cdot3^n+291\) for \(n\ge4\).

The tail distribution is exact:
\[
\Pr[\tau>3]=534/729,\qquad
\Pr[\tau>n]=\frac{30}{3^n}-\frac{291}{9^n}\quad(n\ge4).
\]
The expected first synchronization length is consequently the rational
\[
\boxed{\mathbb E[\tau]=3+\frac{534}{729}
+\sum_{n=4}^{\infty}\left(\frac{30}{3^n}-\frac{291}{9^n}\right)
=\frac{8239}{1944}\approx4.23817.}
\]

The finite authentic #623 first-hit histogram in the repository (3:2642, 4:4042, 5:2093, 6:782, 7:268, 8:96, 9:27, 10:9, 11:7, 12:2) is strikingly close to the uniform-word distribution: out of 9968 windows the uniform expectations for lengths 3,4,5,6 are about 2666.34, 4051.92, 2068.25, 776.75. This is **not** a valid independence test or a theorem about authentic orbit dynamics. Instead it explains why the observed finite synchronization histogram alone is weak evidence for an all-time invariant: a generic long digit word is already overwhelmingly likely to synchronize.

The genuine-root proof obligation now has a precise geometric form: show that every *finite moving S-window* of its signed \((U,V)\) coordinates stays separated from these twenty affine 3-adic danger lines at the window's scale, **with the exact low-boundary carry and phase shift**. Formula (9) does not give this separation automatically.

## Reproducer and significance

[count_sync_words.js](count_sync_words.js) independently enumerates all \(M^2\) pairs and prints the intersection table and predicted count for \(n=2,\ldots,7\). It uses ordinary integer arithmetic only (largest \(M=2187\)); the theorem above holds for **every** \(n\ge4\) and does not depend on this finite check.

At \(n=12\), the bad fraction among arbitrary words is exactly \(15942939/282429536481\approx5.645\cdot10^{-5}\). Thus a short finite prefix in which all authentic windows synchronize is not by itself strong evidence for a **universal** orbit invariant: generic words synchronize overwhelmingly often at moderate length. Conversely, the count does not imply authentic root failure at any future time, because authentic windows are highly dependent and constrained by the source dynamics. Proving or refuting the all-time authentic-root synchronization claim still requires a source-derived compatibility invariant (or a genuine counterexample), as explained in [SynchronizationPropagationObstruction.md](SynchronizationPropagationObstruction.md) and [TerminalSynchronizationBridge.md](TerminalSynchronizationBridge.md).

This is an intermediate arithmetic result for the synchronization method, not a frontier-closing BB(6) theorem; retain it in \`im-results/\`.