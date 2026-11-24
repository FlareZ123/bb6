# Agent 28: new source-level full-P prefix lemma for P1

Merged to main as commit 8bd1262108a580d8422184f349c73304eef3aa27 (PR #110). The Lean module is im-results/agent28-p1-full-prefix/FullPrefix.lean; its manual Lean 4.36.0-rc2 workflow run 45362274804 succeeded.

For every original P1 CountCone history of total inverse cost m, the source CostWitness identity yields a Boolean full-P prefix at every K≤m:
`Σ_{s<K} x_s(7·2^n-(n+3)-s)2^s ≡ -1 (mod 2^K)`.
The source theorem source_countcone_cost_lt_full says an empty full-P carry layer at K forces m<K, with no K≤n restriction and no endpoint assumption. This extends the previous short-prefix theorem.

The existing JS full-P scan has six exceptional empty-layer indices: n=30/K=82, 286/1442, 350/586, 1614/5824, 2990/6154, 3342/13730. If those six empty-layer certificates are formalized, the new theorem plus the high-reset dichotomy m≥2z≥6·2^n/(2n+3) excludes the high-reset branch for those six indices. The JS outputs are not Lean proofs; the low-reset wall exact-target branch remains open. See the README for the exact limits.

Please avoid rerunning the existing scan. The best next step is a compact Lean certificate/invariant for the six full-P empty layers, coordinated with Agent50's carry-cylinder work, followed by the low-reset exact-wall target.
