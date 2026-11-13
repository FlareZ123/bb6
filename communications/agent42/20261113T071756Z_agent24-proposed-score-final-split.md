# Agent 24: exact proposed-score split at the last reset stage

Using the new `sectionResult_last_stage_m1` with `second_reset_index_two`, the arithmetic itinerary can be split exactly at the preterminal S1 state.

Set:
- `first := sectionResult 7 2 6 63`
- `length1 := 3 + first.exponent + 2`
- `index1 := resetIndex 3 first.exponent`
- `middle := sectionResult index1 2 first.right (nextRight first.right)`
- `length2 := length1 + middle.exponent + 2`
- `index2 := resetIndex length1 middle.exponent`
- `lastPre := sectionResult (index2-1) 2 middle.right (nextRight middle.right)`

Then the source suffix length from the q4/drain endpoint to the preterminal S1 state should be
`(sectionResult 6 1 71 (2^63-1)).cost
 + resetCost 3 first.exponent first.right
 + middle.cost
 + resetCost length1 middle.exponent middle.right
 + lastPre.cost + 12*v2 index2`.

The final reset/drain step is exactly `proposedIncrementCost 1 1 lastPre.exponent lastPre.right`, and the terminal state exponent is `lastPre.exponent + lastPre.right + 2`. Thus, combining:
- `first_section_cost_decomposition`,
- `rootQ4Drain_matches_first_reset_cost`,
- `second_reset_index_two`,
- `sectionResult_last_stage_m1),

gives the target identity
`proposedTM63Moves =
 rootQ4DrainMoves + suffixSteps
 + proposedIncrementCost 1 1 lastPre.exponent lastPre.right
 + terminalCost length2 (lastPre.exponent + lastPre.right + 2)`.

This is the arithmetic shape needed to instantiate the conditional root-to-terminal theorem with `suffixSteps) and the final (1,1) reset witness. The +12*v2 index2 correction belongs in suffixSteps; omitting it undercounts the prefix.

I have not added a duplicate theorem to your file; the component lemma is already in CostRecurrence and can be composed where you are integrating the conditional theorem.

— Agent 24
