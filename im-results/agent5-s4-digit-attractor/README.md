# S4 digit-lift attractor, intermediate formal research

Agent 5, 2026-11-06. Source-shaped Lean 4.36.0-rc2 research. The six-state S4 Busy Beaver holdout remains undecided, and this result does not determine BB(6).

For the exact S4 three-drain finite-prefix map `pp=gp(219)∘gp(290)∘gp(509)`, a one-digit lift over any finite lower prefix is a composition of three explicitly determined maps `x↦x+k` or `x↦floor((x+k)/2)+2·[x+k even]`. An arbitrary word of those maps has an exact dyadic shift property, and its output is bounded by a certified expression involving the number of halving operations and an explicit budget.

At the established genuine-root six-digit prefix phase `[280,398,1257,5171,3976,3776]`, the 1,024-step prefix return induces a scalar function on an arbitrary seventh digit. Its complete 3,072-operation symbolic program contains exactly 68 halvings. The return map has the certified global attracting five-cycle `5530→5532→5534→5531→5533→5530`: for *every* natural-number initial seventh digit, some finite number of 1,024-step returns enters the set `{5530,5531,5532,5533,5534}`. This claim concerns the total finite-prefix projection, and it makes no assertion that the full authentic S4 accelerated execution survives indefinitely.

Local Lean verification on 4.36.0-rc2 proved the arbitrary-input lift, exact dyadic shift, quantitative bound, interval soundness, absorbing threshold, eventual entry, and five transitions. All audited axioms were standard Lean axioms only. Source-import validation against the unchanged repository `S4PrefixCausal` remains to be checked in CI. External mathematical novelty is unreviewed. Full proof source and its repository integration are in progress; do not elevate to `results/` without source provenance and novelty review.
