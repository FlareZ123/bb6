# External BB(6) champion baseline (retrieved 2026-11-06)

## Current published baseline

BusyBeaverWiki identifies the current six-state, two-symbol champion as

`1RB1RA_1RC1RZ_1LD0RF_1RA0LE_0LD1RC_1RA0RE`

discovered by mxdys on 25 June 2025. Its BB(6) page states the lower bound

`S(6) > 2 ↑↑↑ 5`.

The individual machine page gives an approximate halting-time analysis with

`2 ↑↑↑ 5 < T < 2 ↑↑↑ 6`

and an estimated runtime expression between the two bounds. It also reports a separate, more precise sigma score of

`10 ↑↑ 10 ↑↑ 10 ↑↑ 8.10237`.

Keep the quantities distinct: `S(6)` is the maximum number of steps, while `Σ(6)` is the maximum number of ones. The sigma-score estimate is not an exact primitive step count. The exact champion step count is not supplied by these pages.

The machine page links a Rocq analysis at the pinned source revision:

- [busycoq, SOBCv5.v, lines 10210–11283](https://github.com/ccz181078/busycoq/blob/3f302b87f5fb933c46e97672ffbb6907f373fb6e/verify/SOBCv5.v#L10210-L11283)
- [BB(6) page](https://wiki.bbchallenge.org/wiki/BB(6))
- [Champion machine page](https://wiki.bbchallenge.org/wiki/1RB1RA_1RC1RZ_1LD0RF_1RA0LE_0LD1RC_1RA0RE)
- [Champions page](https://wiki.bbchallenge.org/wiki/Champions)
- [Σ(6) page](https://wiki.bbchallenge.org/wiki/%CE%A3(6))

The BB(6) wiki page was last edited 27 October 2025; the individual machine page was last edited 16 November 2025. These are external status references retrieved on 6 November 2026, not proof artifacts in this repository.

## Repository boundary

`im-results/agent48-champion-root/README.md` and its `ChampionRootBridge.lean` formalize a conditional all-time equivalence between the champion root and TM63. They do not import the external Rocq halting proof as a Lean theorem, and do not prove the exact primitive step count. Do not promote the external lower bound to a repository-certified result until an unconditional source-checked Lean halting/score bridge exists.

The F287 root used in `im-results/agent4-coverage-smoke/AuthenticTurnBranchAudit.lean` is a separate historic holdout root, with an upstream Cryptids nonhalting proof. It is not the current champion and does not improve the published BB(6) lower bound.

