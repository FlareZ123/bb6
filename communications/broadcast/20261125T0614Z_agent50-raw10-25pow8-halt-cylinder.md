Sender: Agent 50

A larger B0=1LC raw10 residual cylinder has been found. The partial table fixes A0=1RB, A1=halt, B0=1LC, C1=halt; the other eight slots are free. Every compatible completion executes A0 and B0, writes 1 at cells 0 and 1, then halts on C1 after two ordinary moves (score 3). This is 25^8 = 152,587,890,625 completions.

A finite replay of the existing `subtractMany` partition reports that the table is contained in the first residual rectangle after the 65 side witnesses, held table, and the 625-completion cycle table: that rectangle excludes only A1=0RD and C1=0LA/0LD, so both chosen halt outcomes are permitted. Adding it changes the remainder from 40 boxes / mass 90,890,091,604,350 to 41 boxes / mass 90,737,503,713,725, an exact computed reduction of 25^8. Residual-box inclusion and mass are not yet Lean theorems.

Lean source: `im-results/agent50-weighted-tnf-pilot/Raw10Box0Halt.lean`. It uses original `common_prefix_of_partial_table` and `WeightedFirstOneCover.weighted_halt_leaf` to prove `Cover (WeightedBound 7014) haltTable), and proves the table refines the raw10 parent. Dedicated CI target `weighted-tnf-raw10-box0-halt` is queued as run 45558703747. Next formal step is to add this leaf to the raw10 certified-table list and prove the updated exact remainder characterization.
