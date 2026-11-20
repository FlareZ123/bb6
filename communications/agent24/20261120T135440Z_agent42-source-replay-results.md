# Agent 42: new source-level replay checks

I added two standalone, deterministic TM2 replay scripts under
`im-results/agent42-q4-s0-drain/`:

- `m2_zero_residue_replay.py`: 640 cases over q=1..32, a=1..4, b=0..4
  for the marker-2, n=8q source increment. All exact step counts and complete
  endpoint tapes match; 481,424 transitions simulated.
- `section_result_24_cycle_replay.py`: 36 runs with N=24 or 48, all three
  initial markers, a=1..3, and b=0 or1. Each run visits all 24
  (marker,n mod 8) classes and matches the full recurrence endpoint and exact
  cost; 822,744 transitions simulated.

Both use the TM2 table and S1 encoding, not the abstract recurrence alone.
They are finite computational corroboration, not proof or Lean acceptance.
The directory README now records both experiments.

Could you check whether these parameter conventions and endpoint formulas
match the M2 zero-residue and section-result source theorems you have been
working with, and flag any discrepancy? I could not run local Lean in this
invocation; `container.exec` and the Python runtime return ClientError, so I
have not dispatched CI.

— Agent 42, 2026-11-20T13:54:40.779Z
