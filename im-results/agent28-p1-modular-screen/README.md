# Modular carry extinction and critical-reset margin screen

## Stronger result (2026-11-24)

For a full carry parameter Q, every reachable carry c at layer m satisfies
`2^m*(c+m)+Q+1 ≤ 2^m*(Q+2)` when m≤Q+1, and
`Q+1 ≤ 2^m*c` for m>0. Thus an empty layer K with
`3≤L`, `K≤Q+1`, and `2^(K-1)*L≤Q+1` implies the full `MarginSafe Q L 0 [1] K []` certificate. No giant full-P layer needs to be enumerated.

For Q=7*2^n-(n+3), a residue certificate at r modulo 2^(k+1), k+1≤n, transports to full extinction at k+1: the full carry and positive modular carry have opposite residues, and each integral half-step preserves the relation modulo the next smaller power of two. This gives the symbolic `margin_of_modular_certificate` theorem in CarryProjection.lean. CarryBudget.lean, CarryProjection.lean and BudgetCore.lean were locally compiled in Lean 4.36.0-rc2 against exact copies of relevant carry definitions and composition theorems; axiom audits contain only standard Lean axioms. Original imports still require CI.

For 14≤n≤10000, even n, the existing 587 modular certificates meet the sufficient margin budget for 4987 indices. The bitset coverage and generic witness extraction were locally kernel-checked against the independently generated 587-entry certificate list and exact screen definitions. n=34 fails the sufficient budget but has a directly kernel-checked margin at K=30 (Margin34.lean). BudgetCoverage.lean composes the old certificate validity proofs; SourceBudgetScreen.lean targets Agent43's original critical-reset reachability theorem. Together these target exclusion of all 4988 even indices except 30,286,350,1614,2990,3342. The original-source integrated theorem is pending, and this finite gate screen is not a proof of P1 nonhalting or BB(6).

## Existing right-five screen

BitCarry uses natural-number bitsets of possible carries. A layer is the even-bit compression of S OR (S shifted left C). Proven broadword compression preserves every required bit. Carry bounds prevent finite-width loss; emptiness needs only one-way soundness. The generator proposes 587 residue certificates in 39 batches (longest trace 3501 steps at n=7970); the batches and original aggregate coverage were locally kernel-checked on Lean 4.36.0-rc2. SourceFiniteScreen.lean transports the result to original CountCone right-five exclusion. The six exceptional indices require full-P tests coordinated with Agent43.

## Reproduction

Use Lean 4.36.0-rc2. Generate certificate files with generate.py in a temporary directory inside the source tree, add it to LEAN_PATH, compile BitCarry, CertCore, generated Cert0 through Cert38, and ModScreen. With the original Agent43 MarginCert dependency chain compiled, compile CarryBudget, CarryProjection, BudgetCore, Margin34, BudgetCoverage and SourceBudgetScreen. The existing manual workflow agent43-p1-wall-telescoping.yml can run target budget-blank. No native_decide or generated axioms are used.
