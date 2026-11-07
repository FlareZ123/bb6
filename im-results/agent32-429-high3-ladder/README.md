# Exact raw-time composition of consecutive high-3 J branches

## Result

This module composes the source-checked one-branch theorem
`BB429JFirstBranch.j_first_branch` through any finite run of consecutive
high-3 branches, where the branch condition is (w \ge 2u+3).

For the recursive functions in `High3Ladder.lean`:

- `branchU u k` is the final J parameter (u_k);
- `branchShift u k` is the total rightward head displacement;
- `branchCostSum u k` is the exact number of primitive transitions.

The kernel-checked theorem `j_high3_ladder` states that, from any translated
J-family configuration `shiftConfig d (jConfig u w)`, if
`branchShift u k ≤ w`, the original machine executes exactly
`branchCostSum u k` steps and reaches

`shiftConfig (d + branchShift u k) (jConfig (branchU u k) (w - branchShift u k))`.

The closed parameter formulas are also proved:

[
u_k = 2^k(u+3)-3,
]

[
\operatorname{shift}_k + 3k = 2(u+3)(2^k-1).
]

The primitive cost remains represented by the exact recursive sum of the
one-branch costs (4u_i^2+10u_i+27). No unproved closed form for that sum is
claimed.

## Proof dependencies and scope

The proof uses:

1. the existing source-checked primitive branch theorem
   `BB429JFirstBranch.j_first_branch`;
2. a new translation-commutation theorem for the repository's actual
   `BB6Coverage.run` semantics;
3. induction over the number of consecutive high-3 branches.

No simulator, axiom, or `sorry` is used in the new theorem. The file prints
its theorem dependencies with `#print axioms` for CI auditing.

This result compresses repeated high-3 segments of the authentic #429 J orbit
into one exact raw-time macro. It does not decide whether the blank-start
machine eventually reaches the fatal branch, and it does not close the other
J branches.
