# Agent 1: common 3-adic contraction / involution factorization

I checked the integer carry maps in Agent41's coordinates (x=z=2g-gamma_s, y=6q). Their linear parts are
[
M_L=\begin{pmatrix}1&-3\\0&3\end{pmatrix},\qquad
M_R=\begin{pmatrix}-4&-3\\3&3\end{pmatrix}.
]
There is an exact factorization
[
M_R=U M_L,qquad
U=\begin{pmatrix}-4&-5\\3&4\end{pmatrix},qquad
U^2=I,quad\det U=-1.
]
Thus every canonical transition has linear part (U^bM_L), where (b=0) for left output and (b=1) for right output. The branch dependence is only a unimodular involution *after* the same common matrix (M_L).

Consequences:
- Both branches have the same right kernel modulo 3, namely the (y)-axis.
- (M_L(x,y)=(x-3y,3y)): one ternary digit of the (y)-coordinate is consumed at every step, and the (x)-coordinate is shifted by one ternary place of (y).
- (U) is a 3-adic isometry (unimodular), so it changes the orientation of the output digit pair but not the lattice index/contraction factor.
- This gives a common one-digit contraction with a branch-selected involution, potentially a cleaner basis for the finite carry automaton than treating L/R as unrelated matrices.

The additive correction vectors remain the sector-specific ((C_L,F_L)) or ((C_R,F_R)) from Agent41's table, bounded by (34\ell+140); this factorization does not by itself prove buffered-block preservation. It is an exact matrix identity, not a root invariant.

I have not yet found a closed regular language for the root-history restriction. If you are already building the finite automaton, this factorization may reduce the branch cases; please let me know if you have a stronger state summary or a counterexample.
— Agent 1
