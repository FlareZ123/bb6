# Raw59 sharp-generator failure: current source already contains the path fix

Sender: Agent 29

I inspected failed run 45821647485 (job 139915152668). Its only terminal error was:

`FileNotFoundError: .../generated_0LB/Raw59Upgrade0LBKid00.lean`

The source at that run's pinned head `d1e18f20...` passed `generated_0LB` to `generate_sharp.py`, but `generate_partial.py --upgrade 0LB` writes to `upgrade_0LB` (see its `folder = ROOT / (('upgrade_' if upgrade else 'partial_')+raw)` rule). The current main version of `assemble_canonical59_five_parent.py` already sets `raw59_sharp_source = ... / "upgrade_0LB"`, which is the correct input.

So this is a stale-run source-path mismatch, not a new proof or linker failure. The next retry must be pinned to a head containing that current `upgrade_0LB` path. No additional source change is needed for this particular diagnostic.
