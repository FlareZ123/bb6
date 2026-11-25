# Raw59 six-hole refinement

Raw index 59 of Agent31's 124-cylinder roster: `1RB---_1RC---_0RD---_1LD1RE_---1LA_------`. A1 is first queried after 7 ordinary steps. The cylinder has 25^6 = 244,140,625 literal completions.

## Branch certificates

| A1 | Weighted bound | Splits | Cycle leaves | Last-hole leaves | Open-leaf certificates | Source CI |
|---|---:|---:|---:|---:|---|---|
| 0RD | 157 | 632 | 11674 | 2778 | 85 FAR | pending combined |
| 1LC | 84 | 1066 | 18816 | 5525 | 178 FAR | pending combined |
| 1RB | 135 | 1398 | 25275 | 6231 | 648 FAR + counter | pending combined |
| 1RD | 93 | 547 | 9528 | 2372 | 681 FAR + sweep | pending combined |
| 0LC | 140 | 1478 | 25737 | 7824 | 432 FAR + 2 sweeps | pending combined |
| 0RE | 167 | 1650 | 29417 | 7862 | 671 FAR + sweep | pending combined |
| 0RB | 241 | 1481 | 26750 | 7006 | 306 FAR + 2 ngram | [passed](https://github.com/FlareZ123/bb6/actions/runs/45532160410) |
| 0LD | 125 | 1413 | 25038 | 6748 | 698 FAR + 11 ngram + 5 sweeps | [passed](https://github.com/FlareZ123/bb6/actions/runs/45532361189) |
| 1RC | 190 | 1619 | 28427 | 8164 | 645 FAR + sweep + shared RC | [passed](https://github.com/FlareZ123/bb6/actions/runs/45534269425) |
| 0RC | 226 | 1787 | 31130 | 9692 | 278 FAR + sweep + shared RC | submitted |
| 0RF | 223 | 2301 | 42708 | 9471 | 731 FAR + 8 ngram + 6 sweeps | retry: first run failed Lean installation (503) |
| 1LA | 293 | 1047 | 16645 | 4556 | 2861 FAR + 12 ngram + 7 sweeps + counter | submitted |
| 0RA, 1LD, 1RA, 1RE | 395 | 0 | 1 each | 0 | direct cycles | pending combined |
| halt | 395 | 0 | 0 | 0 | zero-delay graph | pending combined |

The independent branch successes cover 29,296,875 literal completions. The combined theorem `Raw59Refinement.lean` is a candidate graft covering 17 of 25 first-hole choices (166,015,625 completions), leaving 8 five-hole children (78,125,000 completions) and 131 entries in the overall residual roster. No global upper bound is asserted. Pending entries must not be counted as accepted until their original-source proof checks succeed.

## Mathematical holdouts

* [Shared RC finite-language invariant](Raw59RC.md): two ten-plus-one-transition machines with B1 unassigned; all completions never halt. Exact universal macro composition, finite language closure, arbitrary live duration, and bridge to actual source semantics passed [CI](https://github.com/FlareZ123/bb6/actions/runs/45534189368).
* [1LA binary counter](Raw59LACount.lean): arbitrary width, exact cost recurrence c(0)=0, c(n+1)=2c(n)+10+2n; epoch length 12*2^n-2. Local proof checked against copied computational zipper definitions, original-source bridge submitted.
* [Three-cell recursive counter](Raw59RBCount.lean), [alternating sweep](Raw59RDSweep.lean), and generated exact sweeps. All macro rules preserve arbitrary untouched tails.

## Reproduce

`python generate.py <A1>` regenerates one exact enumeration tree, its certificate bank and Lean theorem. `python generate.py` regenerates all. `python unpack_rc.py` materializes the digest-checked shared RC source. Manual workflow `agent32-zero-path-global.yml`, `verify_raw59=true`, `raw59_child=all` checks the combined original-source graft. Other choices check individual branches or RCShared. No sorry or native_decide permitted.
