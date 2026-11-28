# Source-accepted modified D machine, every blank start

Lean CI [46113903832](https://github.com/FlareZ123/bb6/actions/runs/46113903832) at 611324d2f6926ba441ec0e0efe8ee8a8f811ac19 proves `BB6Coverage.Agent31Pump.D3Variant.never` for all six starts of the variant (not the original D machine). Source: `im-results/agent19-d3-local/D3SiblingAllSources.lean`; unpack with `unpack_d3_sibling.py`. It applies to every compatible completion of the single unassigned instruction.

Canonical starts:
- 0, Raw10 D0 E1=0LD: 1RB0RE_1LC0RA_1LA1LD_1LC1LF_0LC0LD_1LE---
- 1, Raw13 D3 D1=0RE: 1RB0LC_1RC1RE_1LA0LD_0RB0RE_1RB1RF_1RD---
- 2, Raw10 D2 E1=0RD: 1RB1RD_1LC0LE_1RA0LB_1RA1RF_0RA0RD_1RE---
- 3, Raw13: 1RB1RF_1RC1RA_1LD0LE_1RB0LC_0RB0RA_1RE---
- 4, zero-write initial variant: 0RB0RE_1RC1RE_1LD0LA_1RB0LC_1RB1RF_1RA---
- 5, Raw9 D1 B1=0RF: 1RB---_0RC0RF_1RD1RF_1LE0LB_1RC0LD_1RC1RA

Raw13 D1=0RE consumed in D3LocalCut, CI 46113553414: 72 residuals, mass 171742550, bound 21269. No global subtraction. Raw10 short frontier matching rows (zero-based): D0 sibling 4197, D2 sibling 1106, but these are ancestors; route through current cuts only if actually residual. Raw9/Raw13 other starts also need current-frontier membership. The original D0–D3 machines remain open.
