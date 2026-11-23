# Two-dimensional synchronization-residue cocycle for machine #623

**Status:** exact algebraic normal form. This is an intermediate reduction of the all-time 3-adic proof obligation.

Let the signed target coordinates used by the #623 S-window be X,Y and define

\[A=X-3Y,\qquad B=3Y.\]

The four scalar forms in the exact full-rectangle synchronization criterion are not independent. Indeed

\[4X+3Y=4A+5B,\]

\[3(X+Y)=3A+4B.\]

So synchronization of a length-n word is completely determined by shifted residues of

\[A,\quad B,\quad 4A+5B,\quad 3A+4B.\]

For the canonical #623 coordinates X=2g-gamma and Y=6q,

\[A=2(g-9q)-\gamma,\qquad B=18q,\]

and equivalently, with p=g+3q,

\[4A+5B=2(4p-3q)-4\gamma,\]

\[3A+4B=6p-3\gamma.\]

Thus the four synchronization tests are exactly: the far terminal residual, the q-scale, the near terminal residual, and the p-scale.

## Exact affine cocycle

Write the branch coordinate update in the maintained form

Left:
\[X'=X-3Y+C,\qquad Y'=3Y+F.\]

Right:
\[X'=-4X-3Y+C,\qquad Y'=3X+3Y+F.\]

where C,F are the exact sector/drain corrections.

In the independent pair (A,B), the left update is

\[\boxed{A'=A-3B+C-3F,\qquad B'=3B+3F.}\]

Its linear matrix is

\[L=\begin{pmatrix}1&-3\\0&3\end{pmatrix},\qquad\det L=3.\]

The right update is

\[\boxed{A'=-13A-17B+C-3F,\qquad B'=9A+12B+3F.}\]

with

\[R=\begin{pmatrix}-13&-17\\9&12\end{pmatrix},\qquad\det R=-3.\]

The other two synchronization forms update without introducing new state:

Left:
\[4A'+5B'=4A+3B+4C+3F,\]
\[3A'+4B'=3A+3B+3C+3F.\]

Right:
\[4A'+5B'=-7A-8B+4C+3F,\]
\[3A'+4B'=-3A-3B+3C+3F.\]

## 3-adic significance

Both branch matrices have determinant of 3-adic valuation exactly one. Therefore every macro step contracts one lattice direction by one ternary digit in the determinant sense. The all-time synchronization problem is an affine 3-adic avoidance problem for this two-dimensional cocycle, with corrections C,F of logarithmic digit depth.

This is more economical than carrying the 70-state synchronization DFA: the DFA is a finite presentation of boundary quotient ambiguity, while the actual root dynamics live in the two integer coordinates A,B.

Combined with TerminalSynchronizationBridge.md, an all-time proof that the authentic S-window residues of A, B, 4A+5B and 3A+4B stay inside the four synchronization intervals would exclude every terminal successor after the small-depth prefix.
## Window-boundary caveat

The pair (A,B) above is a **global-coordinate cocycle**. For a window beginning at ternary position s, the synchronization DFA sees the digit blocks of X and Y, not naively `floor(A/3^s)` and `floor(B/3^s)`. The exact conversion has finite low-boundary carries: see `WindowQuotientInterface.md`. Consequently an all-time induction must retain those low carries (or an equivalent compatible phase relation) together with the global (A,B) cocycle.

This caveat does not weaken the terminal bridge: a globally small dangerous form |A|<3^s or |4A+5B|<3^s forces synchronization failure regardless of the low carry.
