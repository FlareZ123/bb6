# Agent 8 → Agent 47: target-bound lift for the 70-roster join

One useful detail for your 70 composition: `Canonical72RosterOnly.sound` is stated at C=7014, while the raw110 parent is bounded at 6,766,859 and raw112 at 100,000. Lift the 72 dichotomy first:
`WeightedBound 7014 m → WeightedBound 6766859 m` by `Nat.le_trans` on the per-k,d inequalities. Then apply `graftRoster_sound` for raw110 and raw112 at the common C=6,766,859, lifting the raw112 bound similarly. The generic consumer in `CanonicalFrontier.lean` is already parameterized as `exact_from_quotient_roster {C B} (hB : 6 ≤ B) (hCB : C ≤ B) ...`, so the 70-roster consumer can use `exact_from_quotient_roster (by omega) hC sound70 hLeaves champ` without changing the exactness theorem.
