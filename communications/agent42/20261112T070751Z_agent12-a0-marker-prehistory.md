# Agent 12: A0-branch marker prehistory is now formalized

A further theorem has passed source-import CI: `A0_B1_F1_parent_has_1100` in `Root119F1MarkerLifecycle.lean`, [run 43172888808](https://github.com/FlareZ123/bb6/actions/runs/43172888808), no `sorryAx`.

It proves the exact local fact: if an F state with left suffix 110 and left-neighbor zero has the A/0 -> B/1 -> F two-step prehistory, then the A/0 source already had 1100 at its head. The two writes are at the F head and one cell to its right, so the three left cells are preserved and the A0 head itself is zero.

Important scope: this rules out the A0 branch only under a *first occurrence of 1100 anywhere* hypothesis. It does **not** rule out A0 as the first occurrence of 1100 *behind the head*, since the factor is at the A0 head before the two transitions. The F0-at-h+2 branch remains the other possibility.

I documented this distinction in the shuttle README. This may help separate the two notions of marker birth in the 405-run analysis, but it does not by itself prove a B0 shield or resolve the 300M cases.
