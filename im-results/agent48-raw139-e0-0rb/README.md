# Raw139 E0=0RB: complete computational parent candidate

**Exact parent:** `[7,24,11,24,14,24,24,16,5,11,24,24]` (normalized row (2, 0RB)). **Candidate weighted bound: 1217.** The complete finite partition has computational witnesses; the original-source Lean audit is pending. No BB6 bound or global roster reduction is claimed.

The exact scanner at limit 450, FAR dimension at most 2, retains all 24 ordinary moves at every split:

| Outcome | Count |
|---|---:|
| Splits | 18,483 |
| Translated cycles | 330,158 |
| Last-hole leaves | 70,001 |
| Ordinary FAR | 22,834 |
| Initially open | 2,117 |
| Total ordinary leaves | 425,110 |

The maximum first query in the initial partition is 367. Block-FAR closes 2,115 initially open leaves (1,758 width two; 357 width three; maximum minimized left/right dimensions 30/88). The remaining two reach their last undefined transition:

| Open index | Exact table | Slot | First query |
|---:|---|---:|---:|
| 440 | `[7,20,11,3,14,1,24,16,5,11,2,8]` | 6 | 1211 |
| 2093 | `[7,0,11,24,14,23,2,16,5,11,9,19]` | 3 | 1121 |

Thus 1217 is the candidate bound including the six-step weighted allowance. This is a complete computational classification of this cylinder, not yet a kernel-checked certificate.

## Reproduction and source acceptance

Run `bash im-results/agent48-raw139-e0-0rb/reproduce-parent.sh` from the repository root with Lean 4.36.0-rc2. It reuses the existing E0=0RE original-source checker pipeline, produces the exact partition (SHA256 `37153ae6051299131f4f5681415cde2fcdb0ee8d6f8e3d61fe59d9e497ca9808`), regenerates every open-leaf witness using `discover.py` with digest and count checks, emits sharded certificates using `package6.py`, and audits the exported theorem `BB6.Agent48Raw139E0ZeroRB.all_completions_weighted` and its axioms.

Use the existing manual `agent48-raw139-f1-siblings.yml` workflow with `kind=e0parent`, `sibling=ZeroRB`, pinned to a commit containing these inputs. Once accepted, the integration must match this exact parent against the live normalized roster and use Cover monotonicity; it must not infer coverage from the leaf count alone. E0=0RA, E0=0RE, and E0=0LC are distinct siblings.
