# Raw60 weighted parent closure

Raw residual 60 (canonical index 36), E1=1RA, partial table `1RB---_1RC---_0RD---_1LD1RE_---1RA_------`, six holes. The first hole A1 is queried after seven ordinary transitions. The research target is the unconditional original-source theorem `BB6.Agent1Raw60Root.all60 : ∀ m, compatible parent m → WeightedBound 1175 m`, in [Raw60RootFull.lean](Raw60RootFull.lean). **The full theorem is a draft pending source assembly.** It is sufficient to delete this parent at any global target at least 1175, but no such canonical deletion is established yet.

## Exhaustive partition and remaining evidence gate

[Raw60RootCut.lean](Raw60RootCut.lean) covers the halt choice and eleven immediate side-cycle ordinary choices and reduces the remaining thirteen ordinary choices to exact child certificates. [Raw60RootProgress.lean](Raw60RootProgress.lean) and [Raw60RootAssembly.lean](Raw60RootAssembly.lean) combine nine children, preserving the four remaining children. The new full consumer uses all four remaining bounds, lifting each to 1175. Each ordinary child has five holes, and the source checker accounts for the halt query with its incoming blank delay.

| A1 | Candidate bound | Evidence |
| --- | ---: | --- |
| 0RC | 376 | Original-source accepted [45526080641](https://github.com/FlareZ123/bb6/actions/runs/45526080641) |
| 0RE | 719 | Original-source accepted [45526080641](https://github.com/FlareZ123/bb6/actions/runs/45526080641) |
| 0LD | 176 | Complete candidate specification; full common-revision assembly required |
| 0RF | 1175 | Complete candidate specification; full common-revision assembly required |
| 0LB | 258 | Complete candidate specification; full common-revision assembly required |
| 1LA | 178 | Complete candidate specification; full common-revision assembly required |
| 1LB | 620 | Complete candidate specification; full common-revision assembly required |
| 1LC | 253 | Complete candidate specification; full common-revision assembly required |
| 1RF | 276 | Complete candidate specification; full common-revision assembly required |
| 0LC | 251 | Source-linked local acceptance; [dossier](0LC-closure.md) |
| 0LF | 802 | Prior conditional source acceptance, complete replacement witness set now prepared |
| 1LF | 1175 | Complete candidate specification; full common-revision assembly required |
| 1RE | 211 | Complete candidate specification; full common-revision assembly required |

The complete candidate inputs are [specs.json](specs.json), [spec-0LC.json](spec-0LC.json), [0lf-frontier.json](0lf-frontier.json), [spec-1LF.json](spec-1LF.json) and [spec-1RE.json](spec-1RE.json). No unassigned exception remains at the candidate level; this is not equivalent to all thirteen child theorems being kernel-accepted.

## 0LF: complete candidate frontier

The exact open-list SHA-256 is `c2e602b2f109edb8da536af520c072abbb152ba68cfe626512e92b470935dc39`. The enumeration has 1,583 split nodes, 26,182 cycle leaves, 8,604 last-hole leaves and 1,624 open leaves. The exact certificate partition is 1,346 FAR, 170 n-gram, 45 symbolic multi-block pumps, 23 manually specified recursive proofs, and 40 generated recursive unary/delimiter-fill proofs. The last three groups use universally quantified macro equations and induction rather than bounded simulation. The three DATA dictionaries in generate_0lf_unary.py, generate_0lf_second.py and generate_0lf_sentinel.py are disjoint and exactly cover the remaining 40 listed IDs; generate_0lf_audit.py consumes them and must emit an empty Exceptions type.

Original-source conditional audit [45646236835](https://github.com/FlareZ123/bb6/actions/runs/45646236835) succeeded at bcefa8e3a5723be26f2159fdc90955a1f7058296 for all but 19 explicitly retained exceptions. The latest manual proofs replace every one of those exceptions, including the arbitrary-word run grammar (1569), parity counter (1417), mixed-block counters (985/986/989), separator counters (980/982), and prefix-counter family (1024/1032/1035/1036/1038). Their current combined source audit must establish `all_closed` rather than the older conditional statement.

## Reproduction and acceptance

Use the shared manual workflow `agent13-coverage.yml` with target `weighted-tnf-raw60-complete`. It generates each exact child at one source revision with `BB6_SHARD_AUDIT=1`, checks the unconditional named child theorem, and preserves separate source/import/object manifests. The final job uses the existing strict Raw109 merger and the relative-path source compiler to compile [Raw60RootFull.lean](Raw60RootFull.lean) against the thirteen checked child closures. It requires the named standard-axiom profile of `all60`. It does not use a new per-agent workflow or assume legacy artifact identity. The earlier 0LF-only workflow remains for historical reproducibility until the shared replacement succeeds.

After acceptance, use the existing canonical graft interface and the exact parent membership, retaining the full complement. The old canonical78 graft is historical: the current accepted roster must be read at the time of integration. The full six-state upper bound remains unresolved.

## Earlier constructions and evidence

The prior detailed dossier is preserved in [Raw60-history-before-full.md](Raw60-history-before-full.md). It records the recursive counter mechanisms, finite initial census, accepted conditional child proofs and historical canonical78 composition attempts. It is not the current status.
