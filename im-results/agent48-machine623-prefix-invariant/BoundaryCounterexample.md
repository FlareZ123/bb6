# Local counterexample to the current #623 A-state macro invariant

**Status: exact finite transition-table counterexample; not a root-reachability claim.**

The candidate invariant in `im-results/agent24-machine623-macro-invariant.md` is not inductive as currently stated. Consider an A-state with head x=3, left frontier lo=0, and tape bits:

- positions 0..6: `1 0 1 1 0 0 0`
- left prefix `[lo,head) = 1 0 1` has no adjacent `00`, and the frontier bit is 1;
- d=3, A reads 1, and the second-left bit at x-2=1 is 0.

This satisfies every listed clause of the candidate invariant: d>0 prefix/no-00/frontier-one; the d=3 A/1 second-left-zero clause; and the d=0/d=1 clauses are inapplicable.

But the exact A/1 macro is:

1. A/1 at x=3 writes 0 and moves left to E at x=2.
2. E/1 writes 1 and moves left to C at x=1.
3. C/0 writes 0 and moves right to D at x=2.
4. D/1 writes 0 and moves left to A at x=1.

The returned A-state has d=1, current bit 0, and right-three word at positions 2,3,4 equal to `000`. This violates the candidate d=1 A/0 boundary clause.

Therefore the stated invariant does not by itself prove macro preservation. A necessary extra correlation for this case is: at d=3/A1 with second-left bit 0 (the no-00 prefix forces left1=1), the old right1 bit must be 1; otherwise the return creates the forbidden d=1/A0/000 state. This condition may well hold on the actual blank-root orbit, but it must be included and proved from a stronger invariant or a preceding macro condition.

This does not undermine the empirical observations; it identifies a missing inductive clause in the current proof plan.