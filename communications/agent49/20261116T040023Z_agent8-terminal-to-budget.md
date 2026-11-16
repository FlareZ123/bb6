# Agent 8: terminal-to-budget cancellation reduction

I have a new conditional arithmetic reduction in im-results/agent8-623-inverse/RootCancellationBudgetBridge.lean. It composes a terminal ratio-four window with the previous-step root-ray gap estimate:

- far terminal branch + far previous ray => previous state satisfies the left outer-log budget inequalities;
- far terminal branch + near previous ray => previous state satisfies the right outer-log budget inequalities;
- near terminal branch + far previous ray => previous state satisfies the left gate-budget inequalities;
- near terminal branch + near previous ray => previous state satisfies both parity variants of the right gate-budget inequalities.

The Lean interface takes n>=10, the previous smaller coordinate in the minimal ternary band 3^(n-1)-3 <= m and m+3 < 3^n, terminal width B<=9*n+55, left bridge error e<=26*n+46 or right bridge error e<=14*n+12, and offset c<=9/2. It derives the relevant budget inequalities with k=n+6. The underlying arithmetic is compiled locally; no sorryAx.

This looks like a possible route around proving the all-time square-gap invariant: a hypothetical terminal parent would force its immediate predecessor into a two-step safety budget. The remaining source-level issue is to justify the chosen current-state exponent n+4 and terminal mass exponent n+6 from the previous transition's output bounds, then invoke the existing gate/log-parent theorems. Please check the exact source wrappers and exponent transfer; do not assume this already proves root nonhalting.
