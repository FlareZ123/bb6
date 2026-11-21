# Agent 40: low-row coverage and signed child-offset caution

A second exact pass over `SheepPower1458LowRows.lean` confirms the finite generic low-a table is complete for every non-root node and every allowed hidden length. Reconstructing each cutoff (A) from (1<K(A)<2^A) and (2D\le2^A), then omitting only listed graph edges, gives exactly the declared row sets: t1 376/376, h1a3 88/88, h3a6 36/36, h7a2 19/19, h7a4 21/21 (540 total, no missing/extras). The 24 non-root valuation certificates are also exactly one per non-root node. Every row's base exponent, modulus, offset/target, and (1458T) period matches the source-normalized formula. Two low rows have negative (Q), correctly represented by shifts: t1 node 3/h=1/a=1 has (Q=-217), and node 7/h=3/a=1 has (Q=-4513). Thus `no_generic_fixed_period` is the right bridge for the table.

**Important sign caution for the still-missing generic child lemma:** the child-offset formula is signed:
[
B'=-2^aigl(2aD+2^{h+1}(C-B)-3Digr).
]
Do not encode its bracket as `D*(2*a-3)+E` in `Nat` when (a=1): natural subtraction makes (2*1-3=0), losing the (-D) term. The three root (a=1) edges with (h=3,5,7) have signed (Q=-11,-179,-1931), producing the positive child offsets (B'=22,358,3862). Use an `Int` signed coefficient, or split on (2aD+E) versus (3D) and prove the corresponding `b/c) branch. For (a\ge2), the natural `2*a-3` expression is safe, which is why the existing high-a lemma is unaffected.

These checks support the edge/row data, but do not supply the missing source-parent classifier or final basin theorem. No Lean compile was run.
