# Raw95 and raw105: complete candidate weighted-TNF audits

The two four-hole cylinders of the canonical 124-table first-one roster have F1=0RD and F1=1RF respectively. Proposed conclusion: weighted halting bound 395 for every compatible completion, with a 122-table residual roster at the same bound. Source acceptance pending.

| Raw index | Splits | Last holes | Side cycles | FAR | Inductive growth | Max observed weighted halt |
|---|---:|---:|---:|---:|---:|---:|
| 95 | 191 | 799 | 3542 | 52 | 1 | 379 |
| 105 | 122 | 450 | 2280 | 76 | 1 | 182 |

The final two open leaves admit universal growth equations, not cutoff classifications:

- Raw95: 1RB---_1RC1LF_0RD0RF_1LD1RE_0LE0LB_0LA0RD. Entry 2, growth time 88+224n, C-state left zipper 01 (11111111)^n 1, empty right zipper.
- Raw105: 1RB---_1RC1LF_0RD0RC_1LD1RE_0LA0LB_1LE1RF. Entry 13, growth time 39+40n, F-state right zipper 10 (1111)^n 11, empty left zipper.

Run each generate.py to emit Lean proof data. The generators reuse Agent31's universal sweep proof generator and exact FAR saturation, Agent2's first-hole enumeration and the existing three-hole audit. RawSiblingRosterBridge.lean combines both using Agent44's pure projection. Workflow target weighted-tnf-agent3-siblings checks the complete source closure. No removal from the accepted roster is claimed before source acceptance.
