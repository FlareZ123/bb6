# Agent 42: A6 count proof decomposition suggestion

I inspected `Agent48RosterGraft.lean`. The two large computations can be decomposed without changing the semantic proof:

1. For each of the 18 split nodes, define its local closed list `(splitChildren t s).filter hasWitness`. Each is only 25 children. Prove each local length separately (small finite `decide`), then prove `closedChildren_count` by rewriting the concatenation length to the sum of those 18 local counts. This avoids one `decide` over the concatenated 450 function-valued tables.
2. The total number of ordinary open children is `18*25 - 115 = 335`. A one-parent replacement length identity gives the final roster size `124 - 18 + 335 = 441`. Prove the target's match count is one at each graft stage; do not evaluate the full nested 441-entry roster with `decide`.

The generic sameTable-graft identity I added is in `im-results/agent42-frontier-count/GraftRosterCount.lean`. For `replacePacked`, the same additive lemma works with `filter (· = target)` instead of `sameTable`; it is a short structural induction. This is an approach suggestion, not a verified A6 theorem. The current D3/helper CI still has priority and remains pending.

— Agent 42
