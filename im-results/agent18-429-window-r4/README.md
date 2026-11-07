# #429: a certified finite-window invariant and authentic D/0 left-prefix exclusion

**Evidence:** source-connected, all-time, real blank-tape mathematical theorems. The unchanged six-state original physical semantics in the repository and all new Lean modules compiled in **Lean 4.36.0-rc2**, [manual CI 42338704666](https://github.com/FlareZ123/bb6/actions/runs/42338704666) **PASSED**, with no `sorryAx`; the earlier standalone-window check was [42338226051](https://github.com/FlareZ123/bb6/actions/runs/42338226051). No machine-level halt/nonhalt decision, exact BB(6), new runtime upper bound, or external novelty claim follows. This is an intermediate result.

## Result 1: all-time exact physical nine-cell abstract invariant

[WindowR4.lean](WindowR4.lean) defines a full head-centered radius-4 physical tape window, 9 bits for cells with offsets -4 through +4, for each actual control state of the original physical holdout

`1RB0LF_1RC1RA_0RD0RB_1LE---_0LA1LE_1RD1LA`.

The possible finite windows are encoded as a 3072-bit natural-number mask indexed by the six states and nine bits. It has exactly **1059 marked state/windows** (the mask popcount, reproduced independently using local Python). It was generated from an exploratory least-closed-overapproximation BFS with both possible incoming far-edge bits after each head shift, starting at A with nine blank cells. Crucially, the *theorem does not trust that BFS*: Lean's kernel checks the seed membership and **every one of 6 × 512 × 2 abstract source-table transition cases** under all far-side bits using `by decide` in `allowed_closed`. `view_move` checks the correspondence between window shift and the genuine bi-infinite-tape `applyMove`. The source theorem `all_blank_runs_allowed` inducts over all successful genuine blank-origin steps. Any reachable physical configuration is therefore in that certified 1059-cell collection.

One unconditional corollary, `forbidden_blank_A0_window`, excludes for **every** original blank-root time n any A/0 scanning at physical position x for which all of these simultaneously hold:

- x−1 is **1**;
- x−3 is **0**;
- x+1, x+2, and x+3 are **0**.

All other tape cells, including x−2 and x−4, are unrestricted. This exclusion is infinite-horizon and grounded in the full physical source, not a finite execution trace or a synthetic counter orbit.

## Result 2: true-blank D/0 predecessor pattern is impossible

[BB429D0Window.lean](BB429D0Window.lean), theorem `D0_prefix_forbidden`, proves: for every original blank-origin successful step at which state **D** reads **0** at x, the following four source-relative tape constraints cannot all hold:

| cell | x−6 | x−4 | x−3 | x−1 |
| --- | --- | --- | --- | --- |
| value excluded together | 0 | 1 | 1 | 0 |

No condition is imposed on x−2 or x−5 (or any farther cells). To derive the contradiction, an authentic D/0 with its immediate left 0 must follow C/0, because the alternative incoming F/0 writes 1 immediately left. The C/0 must follow B/0. Its preceding B/0 with left 1 must follow A/0, because the alternative C/1 predecessor would write 0 immediately left. These **three forced real source transitions** all move right, with exact one-cell writes, and transport the four D-left constraints back into exactly the forbidden A/0 radius-four pattern of Result 1. Every predecessor is a *genuine earlier blank-origin configuration*; the proof includes the initial-time cases and does not assume arbitrary past history.

This rules out the precise authentic D/0 entry that could launch the [Agent 18 previously source-verified synthetic 18-step E excursion](../agent18-429-lastwriter/README.md) from a seven-bit left packet 0,1,1,1,0,0,0. It does **not** exclude the remaining E/1 and F/1 last-writer sources or every possible D/0 return from other left patterns. In particular, independent finite experiments with arbitrary synthetic left tapes exhibit other D/0 one-sided returns that evade this theorem. Those artificial starting tapes are not blank-root witnesses.

## How this relates to the exact halt gate

Agent32's independently checked [`halts iff genuine C/01` theorem](../agent32-429-raw-parent/README.md) and the source-checked [one-sided last-left-writer characterization](../agent18-429-lastwriter/README.md) show that any real #429 halt requires a right-marked C/0 entry and an earlier D/0, E/1 or F/1 write-one left departure at the right-hand cell, with all intervening heads strictly to its left. The new D/0 theorem forbids one concrete candidate departure neighborhood but does not close the all-time existential condition.

Global finite-window closure alone can be overly permissive: the radius-four abstraction admits some C/01 configurations even though the actual blank-origin reachability of any fatal C/01 remains unproved. The nine-cell mask therefore proves precisely the listed necessary local restrictions, without deciding #429 or the global BB(6) problem.

## Verification and reproducibility

The complete CI [42338704666](https://github.com/FlareZ123/bb6/actions/runs/42338704666), revision `d94361331ec724d108cd6defc0c834133968ce51`, compiles the original checked-in `Frontier.lean`, original physical `BB429PhysicalFrontier.lean`, Agent32's raw predecessor and C/01 proof chain, then [WindowR4.lean](WindowR4.lean) into an olean and [BB429D0Window.lean](BB429D0Window.lean) as a source import. Manual-only workflow: [agent18-429-window-r4.yml](../../.github/workflows/agent18-429-window-r4.yml). The workflow prints theorem axioms and rejects `sorryAx`. Local Lean 4.36.0-rc2 compilation also passed without errors; dependencies in the original-source CI are more authoritative. The strongest new declarations depend only on standard Lean logical axioms (propext, Classical.choice where needed, Quot.sound).

The mask source uses the exact six-state raw transition table, and its finite transition closure, tape-semantics bridge, authentic-root induction, and D/0 backward chain are all explicit in the two files. The exploratory BFS and any external source labels are **not** axioms of the proof.

## Best next question

Develop an original-blank-root invariant for **E/1 and F/1** marked-right departures, or an all-time language description of the left half-line that the machine produces on entering the corresponding E or A successor. A finite-window criterion will help only if it excludes every such genuine history that could return to C/01; arbitrary synthetic departures are insufficient. Alternatively construct an actual blank-root C/01 witness. Prior strong modular halting-gate filters [Agent1](../agent1-429-262144-sieve/README.md) and [Agent6](../agent6-harmonic429/README.md) remain distinct, and no inclusion claim over their arithmetic restrictions is made.
