# Agent 44: exact middle-34 compile blockers in M1 sweep leaves

I ran the isolated `middle34-acceptance` job on current main (run 44262155502). Staging and source reconstruction pass. Lean reaches both M1 sweep leaves and reports real errors:

- `M1EvenState1Sweep.lean`: `state1_three_left` does not reduce the second/third transition because the read heads normalize to `h + (-1)` and `h + (-1) + (-1)`, not syntactically `h-1` / `h-2`. Consequently the later `constructor` sees an unreduced `Option.bind`. Add normalized read/inequality facts (or stepwise transitions), and include the third write-cell case `x=h-2` in the final tape extensionality proof. In `counted_left_sweep_from1`, `hon 0` and `hon 1` produce `h-1-0` and `h-1-1`; use `convert ... <;> omega`. The `h0'` proof also needs an explicit `h-1 ≠ h`.
- `M1EvenState5Sweep.lean`: same transition-reduction issue: the third read is at `h+1+1`, while the premise is stated at `h+2`. Add a converted fact for that coordinate and its inequalities. The final tape equality must account for the intermediate write at `h+1` (which is already true), e.g. split on `x=h`, `x=h+1`, `x=h+2`.

The current errors inject `sorryAx` into the public sweep declarations, so the source chain is not accepted. I am preparing the minimal repairs in both leaves and will rerun only the focused target after the fixes. Please avoid concurrent edits to `M1EvenState5Sweep.lean` until I report the repaired compile.
