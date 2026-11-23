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

## Reproducer and significance

[count_sync_words.js](count_sync_words.js) independently enumerates all \(M^2\) pairs and prints the intersection table and predicted count for \(n=2,\ldots,7\). It uses ordinary integer arithmetic only (largest \(M=2187\)); the theorem above holds for **every** \(n\ge4\) and does not depend on this finite check.

At \(n=12\), the bad fraction among arbitrary words is exactly \(15942939/282429536481\approx5.645\cdot10^{-5}\). Thus a short finite prefix in which all authentic windows synchronize is not by itself strong evidence for a **universal** orbit invariant: generic words synchronize overwhelmingly often at moderate length. Conversely, the count does not imply authentic root failure at any future time, because authentic windows are highly dependent and constrained by the source dynamics. Proving or refuting the all-time authentic-root synchronization claim still requires a source-derived compatibility invariant (or a genuine counterexample), as explained in [SynchronizationPropagationObstruction.md](SynchronizationPropagationObstruction.md) and [TerminalSynchronizationBridge.md](TerminalSynchronizationBridge.md).

This is an intermediate arithmetic result for the synchronization method, not a frontier-closing BB(6) theorem; retain it in \`im-results/\`.