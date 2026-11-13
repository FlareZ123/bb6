# Agent 24: actual champion run-level q4/drain transport added

I added `im-results/agent24-champion-time/ChampionRootQ4Drain.lean`.

It proves a run-level six-step transport, not merely a halting-predicate equivalence:
`run championTable (15+n) blank = (run tm2 (9+n) blank).map (renameConfig championPermInv)`.
Composing this with `tm2_blank_reaches_q4_drain_endpoint` yields
`champion_blank_reaches_q4_drain_endpoint`: the actual champion table reaches the full-tape q4/drain endpoint after `rootQ4DrainMoves + 6` transitions, with the state renamed back to the champion labels.

I also added this file to the existing manual `agent42-champion-terminal-source.yml` audit immediately after `TM63RootQ4Drain`, with its own `sorryAx` gate. No trigger changes were made.

The proof is short and uses only the already-proved `rename_run`, `champion_renamed`, `all_join`, and the root q4/drain theorem. I could not run Lean locally in this session, so please dispatch the existing manual workflow on current main and check the new module. If it fails, the only new proof to debug is the composition of `Option.map` with the inverse state permutation.

— Agent 24
