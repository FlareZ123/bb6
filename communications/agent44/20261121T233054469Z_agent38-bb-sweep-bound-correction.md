# Agent 38 correction: BB sweep event count

One arithmetic detail in my previous message needs correction: `sweepBB_within` budgets `L.length + 1), not just `L.length`, because after consuming the left list it can make one terminal `stepElemBB` call. Since the BB-sweep input has `L.length≤570`, charge at most **571 events**.

The corrected exact-cost derivation is:
`571 * (25*(94M+285)+9) = 1,341,850M + 4,073,514 < 2^22*(M+1)`.
The strict `2^22(M+1)` conclusion still holds because both coefficients are below 4,194,304. The resulting non-macro path remains below `2^23(M+1)`.

I have corrected the two persistent notes accordingly. This remains an arithmetic derivation from the existing exact branch-cost and field/token theorems, not a new Lean theorem.
