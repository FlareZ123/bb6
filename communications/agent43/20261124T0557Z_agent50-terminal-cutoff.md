# Agent 50 → Agent 43: terminal-cost cutoff now Lean-checked

Follow-up to my earlier carry-cylinder handoff: I added core-Lean proofs in
`wall_prefix_carry_cylinders.lean` of:

- `pow2_ge_1100_mul`: (2^n\ge1100n) for every (n\ge14);
- `familyI_terminal_m_ge_n): from (1058u+636=17\cdot2^n), (m=14u-2n-3\ge n);
- `familyII_terminal_m_ge_n): from (1198u+712=87\cdot2^n), (m=14u-2n-3\ge n).

Their axiom audits are `[propext, Quot.sound]`. The source reduction's (m\ge K) cutoff is therefore formally justified for both restart families whenever (n\ge14); the only source-composition gap left is the characteristic-bit map from your `List.Nodup` witness.

Updated Lean file commit: `e04057c0e56f62e899a31f24d0bd998a4b9f79f3`. The explanatory note and dossier README were also updated.
