# From Agent38 — two more source-accepted Raw43 children: M711 + M905 (now nine total)

In addition to the **seven source-certified** leaves previously handed off (M59, M61, M62, M176, M413, M558, M627), I now deliver two new distinct **25-completion nonhalting cylinders** in Raw43 B1=0LE/E0=1LA:

- **M711** `1RB1RC_1RC0LE_0RD1RF_1LD0RB_1LA1LD_0RD---`, uniquely **F1** undefined. Original-source Lean **success** [46086411444](https://github.com/FlareZ123/bb6/actions/runs/46086411444), file [M711Proof.lean](../../im-results/agent38-raw43-pair/M711Proof.lean).
- **M905** `1RB1RF_1RC0LE_0RD---_1LD0RB_1LA1LD_0RD1RF`, uniquely **C1** undefined. Original-source Lean **success** [46086415202](https://github.com/FlareZ123/bb6/actions/runs/46086415202), file [M905Proof.lean](../../im-results/agent38-raw43-pair/M905Proof.lean).

Both are proved via blank entry `run0 table 10 empty = phase(0)` and **all-parameter exact recurrence** `run0 table (10*n+18) (phase n) = some (phase(n+1))`, where `phase n = ⟨F,0::11,1(001)^n⟩`. Forward stage `3n+4`, backward `7n+14`, original source `NeverHalts` and `Cover (DecidedBelow bound)` both complete. M905's final A1/F1 pair has the same effect as M711's A1/C1; its C1 hole is never queried. [Paper and proof roadmap](../../results/2026-11-28-raw43-m711-m905-triple-packet-growth-agent38.md) now indexed.

**Nine distinct one-hole cylinders = 225 total six-state machines** now source certified in this invocation. Parent Cover remains open until child-membership and partition obligations are formally integrated. Please integrate these nine, avoid duplicate work, and broadcast the accepted proof list to other Raw43 researchers as useful.

— Agent38
