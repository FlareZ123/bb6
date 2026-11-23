# Two-residue + two-boundary-carry propagation law for #623 synchronization

**Status:** exact block-level algebra. This compresses one-window carry propagation from a transducer state to two modular residues plus two small boundary perturbations.

Let a length-n pair word have M=3^n and word values X,Y. Define

\[A=X-3Y,\qquad B=3Y,\qquad C=4A+5B=4X+3Y,\qquad D=3A+4B=3(X+Y).\]

For a concrete entering transducer state, only two combinations of its previous digit/carry data affect the output block modulo M.

## Left branch

Put

\[\delta_a=a_0-y_{-1},\qquad \delta_b=y_{-1}+b_0.\]

Telescoping the digit/carry recurrence gives the output block values

\[X'\equiv A+\delta_a\pmod M,\qquad Y'\equiv B+\delta_b\pmod M.\]

Consequently the four synchronization forms of the output word are

\[A'\equiv A-3B+\delta_a-3\delta_b,\]
\[B'\equiv 3B+3\delta_b,\]
\[C'\equiv 4A+3B+4\delta_a+3\delta_b,\]
\[D'\equiv 3A+3B+3\delta_a+3\delta_b\pmod M.\]

For the full L rectangle, \(\delta_a\in[-4,2]\) and \(\delta_b\in[-2,4]\). A concrete authentic boundary phase supplies one exact pair.

## Right branch

Put

\[\delta_a=a_0-x_{-1}-y_{-1},\qquad \delta_b=x_{-1}+y_{-1}+b_0.\]

Then

\[X'\equiv -C+\delta_a\pmod M,\qquad Y'\equiv D+\delta_b\pmod M.\]

Hence

\[A'\equiv -13A-17B+\delta_a-3\delta_b,\]
\[B'\equiv 9A+12B+3\delta_b,\]
\[C'\equiv -7A-8B+4\delta_a+3\delta_b,\]
\[D'\equiv -3A-3B+3\delta_a+3\delta_b\pmod M.\]

For the full R rectangle, \(\delta_a\in[-8,1]\) and \(\delta_b\in[-2,6]\).

## Compression consequence

For a fixed window modulus, **one-step synchronization propagation needs no 70-state DFA and no full previous-pair/carry tuple**. It is exactly determined by

\[(A\bmod M,\;B\bmod M,\;\delta_a,\;\delta_b)\]

plus the L/R branch. The target word synchronizes precisely when the four displayed target residues lie in the four intervals of ExactSynchronizationCriterion.md.

This does not by itself prove forward invariance: SynchronizationPropagationObstruction.md gives concrete choices of \((A,B,\delta_a,\delta_b)\) for which a synchronizing source maps to a nonsynchronizing target. The gain is that the missing authentic compatibility relation has now been reduced to **two small boundary integers**, rather than a 495-state carry rectangle or a 70-state image automaton.

When k or j changes between consecutive S-windows, one additionally needs the one low/high extension digit already isolated by the maintained S-window boundary analysis. On stretches with fixed window indices, the formulas above are the complete block propagation law.
