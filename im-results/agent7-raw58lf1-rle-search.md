# Raw58 LF1 leaf 1181: exact finite-prefix pump

**Current result:** the authentic partial-table blank orbit enters a uniformly repeatable 1,226-transition leftward pump at step 11,883. Entry, arbitrary-tail pump and growth lemmas were kernel-checked locally with Lean 4.36.0-rc2 against copied exact repository zipper definitions; original-source dependency and child-consumer acceptance remain pending. This replaces the expensive RLE candidate as the active proof route.

## Exact claim

Table: `1RB1LF_1RC0LB_0RD1RA_1LD1RE_---0RA_1LB0RF` (E0 is the only hole). In the repository's zipper convention, with B state and an empty left stack (including the scanned blank), let P be the 46-bit right prefix and W the eight-bit inserted word in [Raw58LF11181.lean](agent4-raw58/Raw58LF11181.lean). T is the exact finite right tail at entry. Define family(k) = B([], P W^k T).

- Exact blank entry: run0(table,11883,blank) = family(0).
- For every list R, run0(table,1226,B([],P R)) = B([],P W R).
- Substituting R=W^k T gives family(k) → family(k+1) at cost 1226 for every natural k.

Consequently arbitrarily long live prefixes exist, and the repository's existing never_of_growth theorem lifts the recurrence to NeverHalts for every compatible completion. No undefined transition is queried in the symbolic pump. The source module exports pump, entry, growth and never. The first three were locally checked using the exact copied run0, step0, move0, rep definitions and table representation; their reported axiom sets were [propext]. Local Lean archive extraction now succeeds (608393796 bytes concatenated). The full original-source checkout is unavailable in this container (GitHub DNS resolution failed); the final imported never bridge and consumer have not been compiled locally.

## Integration and evidence

Source commit ea69cc18b266584bac506485e9e67adac0daa85d introduces the compact module; 6abfe4254d9be9f60650a1f12abf4e53f40ba916 maps 1181 to BB6Coverage.Agent7LF11181 in more.json and removes its expensive automaton assignment. The next existing LF1 audit must verify exact table equality, compile the module against original dependencies, and check the exported never theorem's axioms.

The former symmetric RLE tuple (20,8,16) on each stack gave 16776 joint configurations, reduced to 6908 by incidence quotient. Run 45743299006, both attempts, failed during Raw58LF1Automata compilation with runner shutdown/exit 143; the second attempt stopped on 26 Nov at 03:08:02Z. No mathematical counterexample or Lean diagnostic was reported. Preserve this candidate as historical computational evidence; do not rerun the large certificate for 1181.

No complete LF1 child or Raw58 parent Cover or global maximality theorem follows from this isolated leaf without the remaining source acceptance and composition.
