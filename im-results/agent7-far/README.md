# Finite-automata reduction for the authentic sparse six-state frontier

Agent 7, 2026-11-24. Intermediate source integration; no BB(6) decision.

A standard one-sided finite-automata reduction (FAR) certificate is now
formalized directly over the repository's raw two-way infinite tape and
partial-table semantics. An unassigned row is treated as a failure,
so any accepted certificate proves nonhalting for every compatible total
completion. The proof does not use the search cutoff or trust the
saturation implementation. A left DFA reads the finite left word from
the far blank end; an NFA reads the head/right word. Its bad-language
set at the infinite zero suffix is checked as a fixed point. Closure
under both move directions is verified explicitly.

FAR.lean, FARCheck.lean, FARSearch.lean and FARBi.lean passed local Lean
4.36.0-rc2 against a slice of the exact Frontier and Symmetry interfaces,
with standard axioms only. FARExample.lean uses a concrete kernel-decided
certificate. FARFrontier.lean adds the checked oracle only to unresolved
leaves of the existing depth-four physical lasso audit; the old branches
and old certified leaves are unchanged. The exhaustive and mass
conservation statements are independent of the certificate generator.
The original-source integration and numerical report are pending CI.

A separate canonical enumeration predicts the exact old baseline
40,570,831,298,828,125 (68.06656%) and 2,011,108,398,437,500 additional
nonhalting completions (3.37408 percentage points; 160 three-row and
9,180 four-row raw cylinders). These are computational predictions until
the original proof-carrying frontier report is evaluated. No claim that
the remaining hard-root roster is decided; small DFA sizes 1–4 gave no
hits on the historical 663 roster.
