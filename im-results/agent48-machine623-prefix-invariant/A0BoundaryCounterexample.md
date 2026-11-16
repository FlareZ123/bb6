# Second local counterexample to the #623 A-state invariant

**Status: exact finite transition-table counterexample; not a blank-root reachability claim.**

Take A at head x=3, left frontier lo=0, with tape positions 0..6 equal to `1 0 1 0 1 0 0`.

The left prefix `[lo,head)=101` has no adjacent `00` and frontier bit 1. The current bit is 0. Since d=3, neither the d=0 nor d=1 right-window clause nor the d=3/A1 clause applies. Thus the candidate invariant as written permits this state.

Now the exact A/0 macro is:

1. A/0 writes 1 at x and moves right to B at x+1.
2. B/1 preserves 1 and moves right to C at x+2.
3. C/0 writes 0 and moves right to D at x+3.
4. D/0 writes 1 and moves left to x+2.
5. D/0 writes 1 and moves left to x+1.
6. D/1 writes 0 and moves left to A at x.

The returned A-state has the same d=3 and left prefix `101`, current bit 1, and right-three word `011`. It satisfies the listed d=3/A1 clause because second-left is 0, but it violates the additional correlation suggested in `BoundaryCounterexample.md`: right1 must be 1 when d=3/A1 and second-left=0.

Therefore that additional correlation is not preserved unless the old d=3/A0/right-three-100 configuration is also excluded. A natural strengthening is:

`d=3 ∧ A/0 -> right-three != 100`.

The 2,000,000-step blank-root replay recorded in `BoundaryReplay.md` observed zero d=3/A0/right-three-100 states. This is another empirical boundary condition that must be proved from root history or a stronger invariant.