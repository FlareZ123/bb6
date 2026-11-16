# Root cancellation windows imply a predecessor budget—but not a contradiction

**Status:** conditional arithmetic with a decisive state-indexing obstruction. The Lean arithmetic in `RootCancellationBudgetBridge.lean` remains useful, but its former proposed composition with the existing two-step safety theorems was one transition out of alignment. This route does not currently avoid the root-history problem.

## 1. What the arithmetic establishes

Assume the smaller coordinate (m) of a preceding state lies in the minimal ternary band
[
3^{n-1}-3\le m,\qquad m+3<3^n,\qquad n\ge10.
]
Assume the current state's terminal ratio-four window has width (B\le9n+55), and the previous-step root-ray bridge has either left-gap error (e\le26n+46), offset (c\le9), or right-gap error (e\le14n+12), offset (c\le2).

The four Lean reductions in `RootCancellationBudgetBridge.lean` are valid conditional arithmetic:

- far terminal / far previous ray gives `logOuterBudget` on the preceding state;
- far terminal / near previous ray gives `logOuterBudget` on the preceding state;
- near terminal / far previous ray gives `gateBudget` on the preceding state;
- near terminal / near previous ray gives `gateBudget` on the preceding state.

The common exponent is (k=n+6), and the error sum is bounded by (35n+120). The proof of the large-coordinate margin uses the separately proved `width_pow` inequality in `SquareGapTerminalBridge.lean`.

These are arithmetic implications only. They do not by themselves imply that the preceding state survives for three transitions.

## 2. Exact state alignment

Write the hypothetical terminal chain as
[
q\longrightarrow p\longrightarrow h\longrightarrow\mathrm{halt},
]
where `highLevelNext q = some p`, `highLevelNext p = some h`, and `highLevelNext h = none`.

The terminal-ratio source theorem applied to (p\to h\to\mathrm{halt}) places the ratio-four window on (p). The root-ray bridge applied to (q\to p), combined with that window, places the cancellation budget on (q).

The existing safety consumers do not contradict this chain:

- `LogParentSource.two_step_terminal_excludes_log` requires the budgeted state (q) to have a successful successor (p) whose own successor halts. Here (p) has the successful successor (h).
- `GateCompleteSource.gate_budget_two_step` guarantees that the successor (p) of a budgeted (q) has a successor. Here that successor is exactly (h), so the guarantee is satisfied.

Therefore the previous claim that the budget on (q) contradicts the terminal event is false. Applying the exponent-transfer theorem to (p\to h\to\mathrm{halt}) supplies the terminal branch budgets at (p), but the current cancellation adapter still returns a safety budget at (q). It does not repair this one-edge offset.

## 3. Concrete synthetic obstruction

Agent 48 supplied `im-results/agent48-623-budget-composition/Counterexample.lean`, with the exact source-shaped chain
[
D(260178,20001)\to D(240172,60031)\to D(180132,180131)\to\mathrm{halt}.
]
Its first state satisfies `logOuterBudget 260178 20001 16`; the middle state satisfies the odd far-left terminal-ratio window, and all three transitions are stated against the pinned accelerated source. Thus a general theorem saying that this predecessor budget alone forces a third successful transition cannot hold.

**Validation status:** the diagnostic Lean file is a proof draft pending a focused compile and transitive axiom audit. Do not report it as kernel-checked until that preflight succeeds.

## 4. A genuine-root exclusion already drafted

Agent 48's `im-results/agent48-623-budget-composition/RootExclusion.lean` uses exact blank-root checkpoints
[
\begin{aligned}
run(39)&=D(79788,133932),\\
run(40)&=D(54138,239399),\\
run(41)&=D(185262,162438)
\end{aligned}
]
and the source theorem `next_strict_mass` to show that three specified synthetic predecessors are not on the genuine blank-root orbit. Their masses lie in the strict mass gaps around these consecutive checkpoints, or match the step-40 mass with different coordinates.

This is a useful root-history exclusion mechanism, but it currently covers only three concrete states. It is not a uniform exclusion of the four budget strips, nor a proof of nonhalting. Its Lean file also awaits focused compilation and axiom inspection.

## 5. Correct next obligations

The cancellation arithmetic should be retained, but it is not a replacement for root-history control. A valid continuation must do at least one of the following:

1. Prove that every blank-root state in the four resulting predecessor-budget strips is unreachable, using a genuinely root-specific invariant (mass gaps, branch history, or a stronger arithmetic restriction).
2. Find a different source bridge that puts a forbidden budget on (p) itself, with the exact state indices checked against the safety theorem's hypotheses.
3. Prove a suitable root-specific old-ray distance bound on the terminal parent (p), so that the already checked square-gap-to-terminal-window arithmetic can be used.

Do not try to derive generic three-step survival from `logOuterBudget` or `gateBudget` alone: the synthetic chain above is a counterexample to that strategy. The finite small-depth case (n<10) also remains open, but it is not the present logical blocker.

## Reproduction and evidence boundary

Compile `SquareGapTerminalBridge.lean` before `RootCancellationBudgetBridge.lean`; the latter is a self-contained arithmetic composition. The source-dependent exponent-transfer, interface, counterexample, and root-exclusion modules must be compiled with their actual pinned-source dependencies. Inspect `#print axioms` for the exported declarations and reject any transitive `sorryAx`.

All of this belongs in `im-results/`. No BB(6) value, #623 blank-root halting decision, or universal six-state upper bound has been established by this route.
