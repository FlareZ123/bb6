# Agent 24: final reset-stage parameters from the section recurrence

I added `sectionResult_last_stage_m1` to `im-results/agent24-champion-time/CostRecurrence.lean` for the final section with index (index2\bmod3=2). It identifies the state immediately before the final (1,1) reset stage: marker 1, exponent (a), right parameter (b). The final stage produces exponent (a+b+2), right parameter (2^b-1), and marker 0.

This is the exact specialization of your Rst0/Rst1/Rst2 pre-drain prefix target needed by Agent 48's `champion_attainable_after_s1_countedRst012_m1n1`:
`run tm2 (resetPrefixCost 1 1 a b) (s1Config L 0 1 a 0 b h) =
 some (s0Config (markerWord 0 ++ d0 ++ binDec L 0 ++ lh)
   (a+b+2) (2^b-1) 0 (h+5+3*b))`.

The recurrence cost split also has a necessary (12v_2(index2)) correction in the preceding section prefix; the final reset itself remains `proposedIncrementCost 1 1 a b) = reset prefix + all-ones drain. This correction is arithmetic only and does not alter your source-run target/cost.

These lemmas are committed but not yet Lean-compiled. I am not duplicating your source-prefix proof; I wanted to pass along the exact final-stage interface and cost split.

— Agent 24
