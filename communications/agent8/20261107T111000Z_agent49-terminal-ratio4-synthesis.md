# Agent 49: new terminal ratio-4 separation from bridge + joint mass

A further synthesis seems stronger than the separate terminal balance intervals.

Let G_R=dd-4*aa-cR and G_L=aa-4*dd-cL for a terminal drain output D(aa,dd), with cR in {1,2} and cL in {5,9}. The no-successor power-gap lemma plus a mass bound 2*(aa+dd)+5<3^K gives
  |dd-aa| <= K+4.
The root-ray bridge gives G_R≈L_R and G_L≈L_L. Subtracting cancels the output coordinates:
  G_R-G_L = 5*(dd-aa)+(cL-cR),
  L_R-L_L = 5*(4*y-x)       (far-left),
  L_R-L_L = 5*(4*x-y)       (near-left).
Since |cL-cR|<=8, the two bridge errors add, yielding necessary ratio-4 bounds:
- odd far-left: |4*y-x| <= K+5*n+29;
- even far-left: |4*y-x| <= K+5*n+20;
- odd near-left: |4*x-y| <= K+5*n+12;
- even near-left: |4*x-y| <= K+8*n+17.

Here K is chosen from the joint-mass envelope for the corresponding final drain. The even-near composite evaluator+drain mass is bounded by y+2*x+5+3*n.

Finite scan of the first 10,000 blank-root states (9,991 final drains) gives only one state satisfying the combined necessary ratio-4 bound: index 13, right-even D(122,438), with |4*x-y|=50 and bound 64. Its output has a successor, so it is not a terminal witness. Index 16, far-left-odd has gap 64 versus bound 62 and is already excluded. There are no later candidates in the scanned prefix. After index 17, the minimum margins by branch are 1,163 (right-odd), 443 (right-even), 382 (far-left-odd), and 2,643 (far-left-even).

This is finite evidence, not a global orbit proof. The algebraic cancellation is attractive because it removes aa,dd and reduces terminality to a single predecessor ratio-4 separation. I recommend formalizing the generic output-balance lemma and the four branch-specific bounds, then investigating an invariant that keeps the blank-root orbit outside these logarithmic ratio-4 windows.
