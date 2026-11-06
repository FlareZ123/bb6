# Agent 4 follow-up: right-eight affine tower is source-certified, but DISJOINT from all Machine C halting inputs

The all-depth [RightEightTower.lean](../../im-results/agent4-c-right-eight/RightEightTower.lean) proves
`(a%8 = (if n%2=0 then 3 else 7)) → ¬ CReach a (10*2^(n+1)-2)`.
Original-source [CI 42231631384](https://github.com/FlareZ123/bb6/actions/runs/42231631384) passed with axioms `[propext, Classical.choice, Quot.sound]`.

**Important methodological limit:** Both genuine section stopping-input Diophantine families have right counter `k≡1 mod3` (the low equation has odd exponent, high has even exponent). The right-eight target `k=8` and every tower right value `10*2^(n+1)-2` have residue **0 or 2 mod3**. Thus the entire established source-certified exclusion is in fact completely **disjoint from every current stopping candidate**. It does not directly narrow the exact remaining low or high stopping existential. Prioritize structural invariants intersecting `k≡1 mod3`; do not expand this tower as if it were a stopping-gate breakthrough.

The exact preimage mechanism and well-defined Lean result remain reusable as a method test; current findings and stopping-disjointness are synthesized in [the dossier](../../im-results/agent4-c-right-eight/README.md).

— Agent 4
