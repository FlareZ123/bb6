# #429 exact canonical J-chart: three boundary returns and three infinite prepared-tape halting families

**Status:** Original six-state, two-symbol raw transition table; Lean 4.36.0-rc2; all stated theorems universally quantified; full two-sided tape equality. Every source CI rejects `sorryAx`. **All initial tapes here are synthetic prepared J tapes**, and no connection to the authentic blank root is asserted.

## Complete three-way near-boundary return

The source symbolic chart is the actual infinite-tape `BB429JPhysical.jTape u w`, and `J_d(u,w)` is the physical raw-machine configuration with state A, absolute head d, and tape `fun x => jTape u w (x-d)`.

| J family | Exact successor | Raw transition count | Original-source CI |
|---|---|---:|---|
| `J_d(u,2u)` | `J_(d-(2u+6))(0,4u+12)` | `4u²+28u+110` | [42519928933](https://github.com/FlareZ123/bb6/actions/runs/42519928933) |
| `J_d(u,2u+1)` | `J_(d+6-2u)(11,4u+2)` | `4u²+28u+306` | [42519928933](https://github.com/FlareZ123/bb6/actions/runs/42519928933) |
| `J_d(u,2u+2)` | `J_(d-(2u+10))(0,4u+18)` | `4u²+44u+204` | [42520666118](https://github.com/FlareZ123/bb6/actions/runs/42520666118) |

Source modules: [JuncCanonical.lean](JuncCanonical.lean), [JChartTwo.lean](JChartTwo.lean), [JChartThree.lean](JChartThree.lean). The Junc equivalence makes these literal equality-of-physical-configuration theorems, including all unvisited tape cells. Verified [Junc tape bridge CI 42519618540](https://github.com/FlareZ123/bb6/actions/runs/42519618540).

High-zero and high-one branch derivations: [../agent18-429-high0](../agent18-429-high0/README.md) and [../agent18-429-high1](../agent18-429-high1/README.md). The high-two physical precursor comes from [Agent32's High2Return.lean](../agent32-429-high2-prefix/High2Return.lean). The outer `w≥2u+3` ladder and `w=2u-1` fatal predecessor are existing [High3Ladder.lean](../agent32-429-high3-ladder/High3Ladder.lean) and [JFirstBranch.lean](../agent1-429-j-first-branch/JFirstBranch.lean).

## Three new exact raw-machine halting families for prepared tapes

Let `k≥0`; all families begin in state A, at physical head 0, on the exact infinite `J(u,w)` tape. Theorems state `run target429 (fatalTime k) (jConfig ...) = none` and prove `seed(k) < seed(k+1)`.

| Input J tape | Seed u(k) | High-3 returns after boundary transition | Certified CI | First example `k=0` |
|---|---|---:|---|---|
| `J(u,2u)` | `3·2^(4k+5)−(10+3k)` | `4k+5` | [42520555787](https://github.com/FlareZ123/bb6/actions/runs/42520555787) | `J(86,172)`, halt by raw step 78,794 |
| `J(u,2u+1)` | `14·2^(4k+1)−(10+3k)` | `4k+1` | [42520551906](https://github.com/FlareZ123/bb6/actions/runs/42520551906) | `J(18,37)`, halt by raw step 5,504 |
| `J(u,2u+2)` | `3·2^(4k+3)−(10+3k)` | `4k+3` | [42520738348](https://github.com/FlareZ123/bb6/actions/runs/42520738348) | `J(14,30)`, halt by raw step 4,166 |

Each family has `High0FatalFamily.lean`, `High1FatalFamily.lean`, or `High2FatalFamily.lean` in this directory. The corresponding `fatalTime` is the exact sum of certified primitive-time blocks: one new near-boundary return, `branchCostSum` of the consecutive high-3 ladder, and the fatal `JFirstBranch.j_fatal_branch` bound. It is an explicit **halting-by** time; this dossier makes no separate claim about the precise last live step of the final fatal boundary.

The `seed` and `turns` formulas were derived by solving the exact high-3 ladder closed forms `branchU_closed` and `branchShift_closed` for the terminal equality `w+1=2u` after the prescribed number of returns. Each family has an all-natural-number arithmetic proof and a raw-machine proof via existing `run_add'`, translation invariance and the fatal J boundary.

## Open actual-root problem

The authentic all-blank trajectory may never enter any of these prepared J inputs. Even a finite halting family on an infinity of nonblank tapes does **not** decide blank-tape #429, establish a six-state Busy Beaver lower bound, or prove BB(6). A genuine source-to-root connection, or an independently rooted original-machine halting/nonhalting invariant, remains necessary. All this work is retained under `im-results/` as intermediate rigorous mathematics.

Current best next step: derive an original-blank-root chart-entry invariant that can supply actual `J(u,w)` tapes or exclude the proven terminal `(u,w)` ancestry. Use the physically exact three-way J chart alongside the existing B/001 blank-halting event equivalence.