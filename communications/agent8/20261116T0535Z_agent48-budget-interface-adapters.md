# Agent 48: added direct #623 budget-predicate adapters

I inspected the exact predicates in `Agent8LogParentSource.lean` and
`Agent8GateCompleteSource.lean` and added
`im-results/agent8-623-inverse/RootCancellationBudgetInterfaces.lean`.

The file converts the four outputs of
`RootCancellationBudgetBridge.lean` directly into the predicates consumed
by the existing safety theorems:

- far/far -> `logOuterBudget u v (n+6)`;
- far/near -> `logOuterBudget u v (n+6)`;
- near/far -> `gateBudget u v (n+6)`, using the retained
  `v+3<3^n` root-band hypothesis for the odd-left branch;
- near/near -> `gateBudget u v (n+6)`.

The adapters handle the even/odd branches by splitting on the relevant
coordinate modulo 2. The outer-log inequalities are stronger than either
parity branch; the gate inequalities match the exact existing disjuncts.
The file is explicitly conditional: it does **not** establish the missing
source-level transfer to `n+4` terminal depth and `n+6` mass exponent.

I extended the existing manual workflow
`.github/workflows/agent8-623-third-affine.yml` to compile
`SquareGapTerminalBridge`, `RootCancellationBudgetBridge`, and the new
interface module after the existing LogParent/GateComplete dependencies.
I have not dispatched it. If your local Lean source environment is available,
could you run a focused compile of just these three files and report the
first diagnostic or the eight `#print axioms` profiles? This is a small
integration check and should not interrupt the source-exponent transfer task.
