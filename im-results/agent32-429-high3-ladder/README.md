# Exact raw-time composition of consecutive high-3 J branches

## Result

This module composes the source-checked one-branch theorem
`BB429JFirstBranch.j_first_branch` through any finite run of consecutive
high-3 branches, where the branch condition is `w ≥ 2*u+3`.

For the recursive functions in `High3Ladder.lean`:

- `branchU(u,k)` is the final J parameter;
- `branchShift(u,k)` is the total rightward head displacement;
- `branchCostSum(u,k)` is the exact number of primitive transitions.

The kernel-checked theorem `j_high3_ladder` states that, from any translated
J-family configuration `shiftConfig d (jConfig u w)`, if
`branchShift(u,k) ≤ w`, the original machine executes exactly
`branchCostSum(u,k)` steps and reaches

```
shiftConfig (d + branchShift(u,k))
  (jConfig (branchU(u,k)) (w - branchShift(u,k)))
```

The closed parameter formulas are proved:

- `branchU(u,k) = 2^k*(u+3)-3`
- `branchShift(u,k) + 3*k = 2*(u+3)*(2^k-1)`

The exact primitive cost also has a scaled closed form. With `a = u+3`,

```
3 * branchCostSum(u,k)
  = 4*a^2*(4^k-1) - 42*a*(2^k-1) + 99*k
```

This identity avoids division by three while giving an exact arithmetic
expression for the total raw transition count.

## Proof dependencies and scope

The proof uses:

1. the existing source-checked primitive branch theorem
   `BB429JFirstBranch.j_first_branch`;
2. a new translation-commutation theorem for the repository's actual
   `BB6Coverage.run` semantics;
3. induction over the number of consecutive high-3 branches;
4. a kernel-checked geometric-sum identity for the exact primitive cost.

The module prints theorem dependencies with `#print axioms`; CI rejects
`sorryAx`. The expanded source module compiled successfully in
[CI run 42399927193](https://github.com/FlareZ123/bb6/actions/runs/42399927193).
The result is conditional on a J-family raw configuration. The
separate raw-to-Cryptids encoding bridge and authentic blank-root connection
remain open. This theorem does not decide whether the blank-start machine
reaches the fatal branch or close the other J branches.
