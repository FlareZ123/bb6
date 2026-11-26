## Current parent and canonical integration state — 26 November 2026

The accepted global conditional frontier is now Canonical64, not the older Canonical68 snapshot. Raw59 is one of the ten still-open E1 sibling parents in that 64-entry roster.

### Raw59 parent Cover

The six-hole parent is

\`1RB---_1RC---_0RD---_1LD1RE_---1LA_------\`

with 25^6 = 244,140,625 literal completions. The existing proof closes 18 of 25 first-hole choices at weighted bound 395 and refines the seven retained children (0LA, 0LB, 1LB, 0LE, 1LE, 0LF, 1LF) to a parent Cover at 4,200,000.

- Source-accepted upgraded children: 0LE and 1LF from run 45675872170; 1LE and ClosedA–F from run 45727352966; 0LB, 0LF and 1LB from run 45742419127.
- The only remaining child in the focused upgrade set was 0LA. Run 45742419127 reached Raw59Upgrade0LAKid11.lean:4058 and failed with Lean's maximum-recursion-depth diagnostic, not a theorem counterexample.
- The generated decidable proof-fragment size is now 32 rather than 240. Focused source audit 45753302154 was dispatched with target Upgrade0LA; the existing workflow reuses the already accepted sibling artifacts and then composes the full Raw59 parent Cover. This run is pending at the time of this update. Do not claim the parent Cover until its parent-composition job succeeds.

### Canonical integration

Raw59Canonical64Integrated.lean composes the Raw59 parent with the source-accepted Canonical64 artifact 15085029091 (run 45750164590). It checks unique membership of Raw59 in the exact 64-entry roster, removes it, and states a 63-entry conditional exactness interface at the common weighted floor 6,766,859.

assemble_raw59_canonical64.py verifies both producer runs and the Raw59 artifact manifest, links only recursive import closures, compares all differing reachable kernel objects, and checks the exported axiom profiles. The existing Agent32 workflow has a separate Canonical64Compose target for this integration; supply the successful Raw59 parent run ID as raw59_parent_run_id. The integration has not yet run and must not be treated as accepted.

Agent31 is independently pursuing Raw112→Canonical63. If that route is accepted first, the Raw59 parent should be composed against its exact accepted 63-entry roster to produce a 62-entry interface, rather than treating two different 63-entry rosters as separate frontier improvements.

No global upper bound or exact BB(6) value follows from any of these conditional reductions.

---

# Raw59 six-hole refinement

Raw index 59 of Agent31's 124-cylinder roster: `1RB---_1RC---_0RD---_1LD1RE_---1LA_------`. A1 is first queried after 7 ordinary steps. The cylinder has 25^6 = 244,140,625 literal completions.

## Branch certificates

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
| 0RA, 1LD, 1RA, 1RE | 395 | 0 | 1 each | 0 | direct cycles | pending combined |
| halt | 395 | 0 | 0 | 0 | zero-delay graph | pending combined |

The thirteen independently source-checked ordinary branches cover 126,953,125 literal completions. Including the four direct-cycle branches and the halt branch proved in Raw59Base (imported by the successful source checks), 18 of the 25 A1 choices satisfy the bound 395, leaving seven children (68,359,375 literal completions). These are individual branch results; the all-branch canonical consumer has not yet passed as a single closed theorem. The combined theorem `Raw59Refinement.lean` is a candidate graft covering 17 of 25 first-hole choices (166,015,625 completions), leaving 8 five-hole children (78,125,000 completions) and 131 entries in the overall residual roster. No global upper bound is asserted. Pending entries must not be counted as accepted until their original-source proof checks succeed.

## Mathematical holdouts

* [Shared RC finite-language invariant](Raw59RC.md): two ten-plus-one-transition machines with B1 unassigned; all completions never halt. Exact universal macro composition, finite language closure, arbitrary live duration, and bridge to actual source semantics passed [CI](https://github.com/FlareZ123/bb6/actions/runs/45534189368).
* [1LA binary counter](Raw59LACount.lean): arbitrary width, exact cost recurrence c(0)=0, c(n+1)=2c(n)+10+2n; epoch length 12*2^n-2. Local proof checked against copied computational zipper definitions, [original-source certificate passed](https://github.com/FlareZ123/bb6/actions/runs/45534793732).
* 1RF: five recursive restoration counters with a shared parametric proof [accepted](https://github.com/FlareZ123/bb6/actions/runs/45535386620), one triple-block grammar machine [accepted](https://github.com/FlareZ123/bb6/actions/runs/45535698689), four finite-language scan/flush machines (core Lean proof checked, [original-source branch proof passed](https://github.com/FlareZ123/bb6/actions/runs/45544328523)). The entire 1RF branch certificate combines these with FAR, n-gram and framed sweeps.
* [Three-cell recursive counter](Raw59RBCount.lean), [alternating sweep](Raw59RDSweep.lean), and generated exact sweeps. All macro rules preserve arbitrary untouched tails.

## Reproduce

`python generate.py <A1>` regenerates one exact enumeration tree, its certificate bank and Lean theorem. `python generate.py` regenerates all. `python unpack_rc.py` materializes the digest-checked shared RC source. Manual workflow `agent32-zero-path-global.yml`, `verify_raw59=true`, `raw59_child=all` checks the combined original-source graft. Other choices check individual branches or RCShared. No sorry or native_decide permitted.
