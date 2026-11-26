# Raw139 E0=0RD: complete computational parent candidate

**Exact parent:** `[7,24,11,24,14,24,24,16,13,11,24,24]` (normalized row (2, 0RD)). **Candidate weighted bound: 806.** All leaves have computational witnesses; original-source Lean acceptance is pending.

The exact scanner at limit 450, FAR dimension at most 2, retains all 24 ordinary moves at every split.

| Outcome | Count |
|---|---:|
| Splits | 18,648 |
| Translated cycles | 310,299 |
| Last-hole leaves | 81,310 |
| Ordinary FAR | 32,640 |
| Initially open | 4,656 |
| Total ordinary leaves | 428,905 |

Block-FAR closes 4,654 open leaves (3,975 width two, 679 width three). Of the five leaves left by the initial parameter menu, three close under the following richer unreflected abstractions (width, cap, modulus, runs, flip, phase):

- 475: (2,1,2,3,false,false), minimized dimensions 13/21.
- 447: (2,1,1,3,false,true), dimensions 39/125.
- 1640: (2,1,5,3,false,false), dimensions 11/39.

The remaining two first reach their final undefined transitions:

| Open index | Exact table | Slot | First query |
|---:|---|---:|---:|
| 1762 | `[7,24,11,23,14,8,2,16,13,11,3,17]` | 1 | 498 |
| 2113 | `[7,3,11,9,14,7,22,16,13,11,2,24]` | 11 | 800 |

The initial maximum first query is 313. With the six-step weighted allowance, the candidate bound is 806.

## Reproduction and acceptance

Run `bash im-results/agent48-raw139-e0-0rd/reproduce-parent.sh` from repository root with Lean 4.36.0-rc2. The unchanged E0=0RE scanner reproduces SHA256 `4f8e9ab952fb342569e15d44cabcaa31c265cc9fe5f253d0258e91c32a99225c`; `discover.py` regenerates every open-leaf recipe and checks its full assignment digest. The existing sharded audit generator then emits and compiles the original-source theorem `BB6.Agent48Raw139E0ZeroRD.all_completions_weighted`.

Use existing manual workflow `agent48-raw139-f1-siblings.yml` with `kind=e0parent`, `sibling=ZeroRD`, pinned to the source commit. After success, consume the exact normalized row via Cover monotonicity and explicit roster membership. Until that audit and integration pass, no global roster reduction or BB6 bound is claimed.
