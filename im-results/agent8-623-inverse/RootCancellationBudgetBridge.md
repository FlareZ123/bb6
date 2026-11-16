# Root cancellation windows imply a predecessor safety budget

**Status: Lean 4.36.0-rc2 kernel-checked conditional arithmetic. This is not yet a root nonhalting theorem.**

This module composes the terminal ratio-four window with the one-step root-ray bridge. It establishes a potentially useful alternative to a global square-gap invariant.

## Four reductions

Assume the smaller coordinate m of the preceding state lies in the minimal ternary band
3^(n-1)-3 <= m and m+3 < 3^n, with n >= 10. Let the current terminal ratio-four window have width B <= 9*n+55. The root-ray bridge contributes a left-gap error e <= 26*n+46 with offset c <= 9, or a right-gap error e <= 14*n+12 with c <= 2.

Then the four theorems give:

- far terminal branch / far previous ray: the previous state satisfies the left outer-log budget inequalities;
- far terminal branch / near previous ray: the previous state satisfies the right outer-log budget inequalities;
- near terminal branch / far previous ray: the previous state satisfies the left gate-budget inequalities;
- near terminal branch / near previous ray: the previous state satisfies both parity-specific right gate-budget inequalities.

All four use k=n+6. The common error sum is bounded by 35*n+120. The proof of the required large-coordinate margin comes from width_pow in SquareGapTerminalBridge.lean.

The B bound is exactly compatible with choosing current terminal depth n+4 and terminal mass exponent n+6: the four source terminal windows are bounded by K+5*n_current+29 (far odd), K+5*n_current+20 (far even), K+5*n_current+12 (near odd), and K+8*n_current+17 (near even). With n_current=n+4 and K=n+6, all are <=9*n+55.

## Critical remaining integration

The arithmetic is complete conditional on those exponent choices and on the source bridge bounds. The next step is to prove from the exact previous transition output bounds that the current block count is below 3^(n+4) and that the terminal mass inequality holds with K=n+6, without assuming the terminal ratio-four window itself. Then invoke the existing LogParent / GateComplete two-step safety theorem. If successful, a hypothetical terminal parent forces its predecessor into a budget that already guarantees the second successor exists, yielding a contradiction.

This is a candidate route around proving the all-time square-gap invariant, not a proven replacement yet. It still needs source-level composition, correct branch/parity routing, and a finite treatment of n<10. Do not claim that #623 is solved.

## Reproduction

Compile SquareGapTerminalBridge.lean first, then compile this file with its directory on LEAN_PATH. The eight budget/composition theorems print only standard Lean logical axioms plus Classical.choice; none uses sorryAx or a machine-semantic axiom.


Implementation detail: the left-gate theorem explicitly returns m+2 < 3^(n+6), which is the even-parity gate requirement. For the odd-parity requirement m+3 < 3^(n+6), retain the theorem hypothesis m+3 < 3^n and use 3^(n+6) >= 3^n. The theorem's hypotheses therefore supply the stronger odd bound as well; it is simply not duplicated in the conclusion tuple.
