# Raw59 six-hole refinement

## Current parent and canonical integration state — 26 November 2026

**Exact weighted parent maximum: 4,136,171 (source-accepted).** The parent is

`1RB---_1RC---_0RD---_1LD1RE_---1LA_------`

with 25^6 = 244,140,625 literal completions. A1 is first queried after seven ordinary steps. The proof closes all branches, including the seven previously retained children. The 4,200,000 Cover is superseded by the exact bound and attainment accepted in [run 45786187618](https://github.com/FlareZ123/bb6/actions/runs/45786187618), artifact 15100876549. The extremal completion executes 4,136,170 ordinary transitions followed by its halt query. See [Upgrade.md](Upgrade.md) for branch proof development.

**Current integration frontier: Canonical58; Raw59 is the next technical cut.** Canonical59's five-parent integration is accepted, and the subsequent Raw113 delta is now source-accepted as Canonical58 (run [45891227622](https://github.com/FlareZ123/bb6/actions/runs/45891227622), artifact 15151767938). Canonical58 has 58 residual Covers and still retains Raw59. The Raw59 parent Cover itself is already source-accepted at exact weighted bound 4,136,171 (run [45786187618](https://github.com/FlareZ123/bb6/actions/runs/45786187618), artifact 15100876549); only its ingestion into the current roster remains.

[Isolation.md](Isolation.md) records the concrete archived-source difference, the namespace-isolation repair and the exact verification requirements. The relocated width-two core, certificate and original-machine bridge for Raw59/1LB/194 passed the earlier isolated-import pilot, and the first large downstream Kid00 object passed actual kernel replay. The full Raw59 relocation is now being attempted from the accepted source closure in [run 45878179911](https://github.com/FlareZ123/bb6/actions/runs/45878179911); it remains in progress and is not yet accepted. If the one-shot replay fails or times out, the existing staged fallback is in `kernel-slice/stage_relocate.py` and `kernel-slice/KernelStage.lean`, with workflow target `canonical64-raw59-kernel-staged`.

A follow-on `Canonical56Raw59Graft.lean` and `assemble_canonical56_raw59_graft.py` are prepared to consume Raw59 after an accepted Canonical57 (Raw113+Raw112) base. They are intermediate drafts only: no Canonical56 theorem is claimed. If Raw112 does not pass first, the same accepted Raw59 slice can instead be grafted onto Canonical58, subject to coordination with Agent17. All duplicate imported kernel objects must still pass the exact-hash or kernel-equality audit before the combined consumer is accepted.

No global upper bound or exact BB(6) value follows from the accepted Raw59 cylinder or any current conditional roster.

## Historical branch certificates

| A1 | Weighted bound | Splits | Cycle leaves | Last-hole leaves | Open-leaf certificates | Source CI |
|---|---:|---:|---:|---:|---|---|
| 0RD | 157 | 632 | 11674 | 2778 | 85 FAR | [passed](https://github.com/FlareZ123/bb6/actions/runs/45544923268) |
| 1LC | 84 | 1066 | 18816 | 5525 | 178 FAR | [passed](https://github.com/FlareZ123/bb6/actions/runs/45544928483) |
| 1RB | 135 | 1398 | 25275 | 6231 | 648 FAR + counter | [passed](https://github.com/FlareZ123/bb6/actions/runs/45544934401) |
| 1RD | 93 | 547 | 9528 | 2372 | 681 FAR + sweep | [passed](https://github.com/FlareZ123/bb6/actions/runs/45544939936) |
| 0LC | 140 | 1478 | 25737 | 7824 | 432 FAR + 2 sweeps | [passed](https://github.com/FlareZ123/bb6/actions/runs/45544945859) |
| 0RE | 167 | 1650 | 29417 | 7862 | 671 FAR + sweep | [passed](https://github.com/FlareZ123/bb6/actions/runs/45544953161) |
| 0RB | 241 | 1481 | 26750 | 7006 | 306 FAR + 2 ngram | [passed](https://github.com/FlareZ123/bb6/actions/runs/45532160410) |
| 0LD | 125 | 1413 | 25038 | 6748 | 698 FAR + 11 ngram + 5 sweeps | [passed](https://github.com/FlareZ123/bb6/actions/runs/45532361189) |
| 1RC | 190 | 1619 | 28427 | 8164 | 645 FAR + sweep + shared RC | [passed](https://github.com/FlareZ123/bb6/actions/runs/45534269425) |
| 0RC | 226 | 1787 | 31130 | 9692 | 278 FAR + sweep + shared RC | [passed](https://github.com/FlareZ123/bb6/actions/runs/45534341369) |
| 0RF | 223 | 2301 | 42708 | 9471 | 731 FAR + 8 ngram + 6 sweeps | [passed](https://github.com/FlareZ123/bb6/actions/runs/45535002020) |
| 1LA | 293 | 1047 | 16645 | 4556 | 2861 FAR + 12 ngram + 7 sweeps + counter | [passed](https://github.com/FlareZ123/bb6/actions/runs/45534793732) |
| 1RF | 376 | 2531 | 45809 | 10651 | 1724 FAR + 15 ngram + 5 sweeps + 10 manual | [passed](https://github.com/FlareZ123/bb6/actions/runs/45544328523) |
| 0RA, 1LD, 1RA, 1RE | 395 | 0 | 1 each | 0 | direct cycles | accepted via final parent |
| halt | 395 | 0 | 0 | 0 | zero-delay graph | accepted via final parent |

The thirteen independently source-checked ordinary branches cover 126,953,125 literal completions. Including the four direct-cycle branches and the halt branch proved in Raw59Base (imported by the successful source checks), 18 of the 25 A1 choices satisfy the bound 395, leaving seven children (68,359,375 literal completions). These are historical individual branch results; all seven formerly retained children and the full parent were subsequently source-accepted in run 45786187618. The combined theorem `Raw59Refinement.lean` is a candidate graft covering 17 of 25 first-hole choices (166,015,625 completions), leaving 8 five-hole children (78,125,000 completions) and 131 entries in the overall residual roster. No global upper bound is asserted. The original partial graft is superseded by the full accepted parent; global roster removal still requires the coordinated canonical integration.

## Mathematical holdouts

* [Shared RC finite-language invariant](Raw59RC.md): two ten-plus-one-transition machines with B1 unassigned; all completions never halt. Exact universal macro composition, finite language closure, arbitrary live duration, and bridge to actual source semantics passed [CI](https://github.com/FlareZ123/bb6/actions/runs/45534189368).
* [1LA binary counter](Raw59LACount.lean): arbitrary width, exact cost recurrence c(0)=0, c(n+1)=2c(n)+10+2n; epoch length 12*2^n-2. Local proof checked against copied computational zipper definitions, [original-source certificate passed](https://github.com/FlareZ123/bb6/actions/runs/45534793732).
* 1RF: five recursive restoration counters with a shared parametric proof [accepted](https://github.com/FlareZ123/bb6/actions/runs/45535386620), one triple-block grammar machine [accepted](https://github.com/FlareZ123/bb6/actions/runs/45535698689), four finite-language scan/flush machines (core Lean proof checked, [original-source branch proof passed](https://github.com/FlareZ123/bb6/actions/runs/45544328523)). The entire 1RF branch certificate combines these with FAR, n-gram and framed sweeps.
* [Three-cell recursive counter](Raw59RBCount.lean), [alternating sweep](Raw59RDSweep.lean), and generated exact sweeps. All macro rules preserve arbitrary untouched tails.

## Reproduce

`python generate.py <A1>` regenerates one exact enumeration tree, its certificate bank and Lean theorem. `python generate.py` regenerates all. `python unpack_rc.py` materializes the digest-checked shared RC source. Manual workflow `agent32-zero-path-global.yml`, `verify_raw59=true`, `raw59_child=all` checks the combined original-source graft. Other choices check individual branches or RCShared. No sorry or native_decide permitted.
