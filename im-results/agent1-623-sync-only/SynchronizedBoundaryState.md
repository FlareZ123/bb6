# Closed form of the synchronized boundary state for machine #623

**Status:** exact consequence of the full-rectangle synchronization theorem.

Let a length-n pair word (n>=2) have word values X,Y and M=3^n, with last digit pair (x_last,y_last). Assume the corresponding full rectangle synchronizes.

From the telescoped carry formulas in ExactSynchronizationCriterion.md, the common value may be evaluated at boundary perturbation 0 because the quotient is constant across the entire perturbation interval.

## Left branch

The unique final left state has previous pair (x_last,y_last) and carries

\[a_L=y_{\rm last}+\left\lfloor\frac{X-3Y}{M}\right\rfloor,\]

\[b_L=-y_{\rm last}+\left\lfloor\frac{3Y}{M}\right\rfloor.\]

Because Y=Y_low+y_last M/3 with 0<=Y_low<M/3,

\[\left\lfloor\frac{3Y}{M}\right\rfloor=y_{\rm last},\]

so in fact

\[\boxed{b_L=0.}\]

The first synchronization inequality forces the remaining carry to lie in

\[\boxed{a_L\in\{-1,0\}.}\]

This matches the exact singleton states of the 355-state image construction.

## Right branch

The unique final right state has previous pair (x_last,y_last) and carries

\[a_R=x_{\rm last}+y_{\rm last}+\left\lfloor\frac{-(4X+3Y)}{M}\right\rfloor,\]

\[b_R=-(x_{\rm last}+y_{\rm last})+\left\lfloor\frac{3(X+Y)}{M}\right\rfloor.\]

Writing X=X_low+x_last M/3 and Y=Y_low+y_last M/3 gives

\[b_R=\left\lfloor\frac{3(X_{\rm low}+Y_{\rm low})}{M}\right\rfloor\in\{0,1\}.\]

The right dangerous-residue synchronization inequality similarly gives

\[\boxed{a_R\in\{-3,-2,-1\}.}\]

Hence a synchronized word lands in a boundary state of the restricted form

\[L:(x,y,a,0),\quad a\in\{-1,0\},\]

\[R:(x,y,a,b),\quad a\in\{-3,-2,-1\},\ b\in\{0,1\}.\]

The joint L/R constraints cut the naive 2*3*2*9 possibilities down to the 66 singleton-pair states seen in the exact image automaton, but the carries themselves are computable directly from four integer quotients.

## Why this matters

The post-reset 66-state closure is therefore a derived finite presentation, not fundamental proof state. An all-time proof can carry the scalar residues/quotients and reconstruct the synchronized phase analytically whenever needed. This removes another layer of finite-state bookkeeping from the #623 induction problem.
