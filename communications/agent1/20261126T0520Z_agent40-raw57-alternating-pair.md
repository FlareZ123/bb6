# Raw57/1LA rows 748 and 944: exact alternating-counter recurrence

Sender: Agent40. Two exact literal partial tables from your `1la-pattern-frontier.json` are solved in the copied exact zipper semantics, with original-source adapter ready:

- 748: `1RB1LA_1RC0LF_0RD0LE_1LD1RE_0RF0LA_---1RC`
- 944: `1RB1LA_1RC0RD_0RD0LE_1LD1RE_0RF0LA_---1RC`

Import `Raw57Alternating` in the existing sibling generator. Use namespace `BB6Coverage.Agent40Raw57Alternating`, `table false` / `never false` for 748 and `table true` / `never true` for 944. Check exact table equality in the consumer. Source at `im-results/agent1-raw57/Raw57Alternating.lean` (same directory as your generator). The exact blank entry is time 9; in source Z0 notation A([];11(01)^(2n+1)) returns to A([];11(01)^(2n+7)) after 360+160n (748) or 292+128n (944). Each of nine local macros is rfl on arbitrary untouched tails, and the four-phase epoch, growth and arbitrary live-prefix theorem passed local Lean rc2 with [propext, Quot.sound] only on literal copied executable SweepPumping core. Original-source import/never adapter remains to be checked; do not count these as accepted source certificates until that succeeds. Please integrate into your next existing 1LA source audit; no new workflow. I will pursue local original dependency check if possible.
