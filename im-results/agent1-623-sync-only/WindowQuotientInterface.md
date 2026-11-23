# Exact window-quotient interface for the #623 synchronization residues

**Status:** exact arithmetic interface. This corrects an easy ambiguity between a digit block of a linear form and the same linear form applied to digit blocks.

Let a window begin at ternary position s, put P=3^s, and let its length be n with M=3^n. For global signed coordinates X,Y write Euclidean decompositions

\[X=P Q_X+r_X,\qquad Y=P Q_Y+r_Y,\qquad 0\le r_X,r_Y<P.\]

The window values are

\[X_w=[Q_X]_M,\qquad Y_w=[Q_Y]_M.\]

Therefore the four exact synchronization residues are

\[Q_X-3Q_Y,\qquad 3Q_Y,\qquad 4Q_X+3Q_Y,\qquad 3(Q_X+Q_Y)\pmod M.\]

They are **not**, in general, obtained by simply dividing the four global linear forms by P and taking a residue: low digits contribute a finite boundary carry.

## Boundary-carry identities

Define the global forms

\[A=X-3Y,\quad B=3Y,\quad C=4X+3Y,\quad D=3(X+Y).\]

Then

\[A=P(Q_X-3Q_Y)+(r_X-3r_Y),\qquad -3P<r_X-3r_Y<P,\]

\[B=P(3Q_Y)+3r_Y,\qquad 0\le3r_Y<3P,\]

\[C=P(4Q_X+3Q_Y)+(4r_X+3r_Y),\qquad 0\le4r_X+3r_Y<7P,\]

\[D=P\,3(Q_X+Q_Y)+3(r_X+r_Y),\qquad 0\le3(r_X+r_Y)<6P.\]

Hence, if c_A,c_B,c_C,c_D are the quotient carries of the displayed low remainders, then

\[c_A\in\{-3,-2,-1,0\},\quad c_B\in\{0,1,2\},\quad c_C\in\{0,1,2,3,4,5,6\},\quad c_D\in\{0,1,2,3,4,5\},\]

and

\[Q_X-3Q_Y=\left\lfloor\frac{A}{P}\right\rfloor-c_A,\]

\[3Q_Y=\left\lfloor\frac{B}{P}\right\rfloor-c_B,\]

\[4Q_X+3Q_Y=\left\lfloor\frac{C}{P}\right\rfloor-c_C,\]

\[3(Q_X+Q_Y)=\left\lfloor\frac{D}{P}\right\rfloor-c_D.\]

Thus the exact all-time synchronization proof state can be viewed as two global integer coordinates (for example A and B, since C=4A+5B and D=3A+4B) **plus finite low-boundary carry information**. The carry cannot be discarded: SynchronizationPropagationObstruction.md gives explicit 3-symbol failures of a carry-free propagation claim.

## Relation to the terminal bridge

The terminal-to-synchronization-failure implication does not need to know these carries individually. If |A|<P, the first identity forces Q_X-3Q_Y into {-1,0,1,2,3}, outside the left safe interval. If |C|<P, the third identity forces 4Q_X+3Q_Y into {-7,...,0}, outside the right safe interval. This is why TerminalSynchronizationBridge.md is robust even though a general forward induction needs the boundary-carry state.
