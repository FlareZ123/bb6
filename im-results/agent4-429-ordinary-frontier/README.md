# #429 ordinary Junc returns preserve a physical right-frontier

**Verified source result, 9 November 2026.** The original six-state two-symbol #429 machine is
`1RB0LF_1RC1RA_0RD0RB_1LE---_0LA1LE_1RD1LA`.
All theorems below compile against unchanged original repository definitions under Lean 4.36.0-rc2, [manual source CI 42542918077](https://github.com/FlareZ123/bb6/actions/runs/42542918077), with standard axioms and **no `sorryAx`**. They are uniform over the unbounded source parameters, including every intermediate primitive instruction, and apply to arbitrary actual physical tapes satisfying the exact source zipper representation. They do not decide the authentic blank-origin machine or BB(6).

## New complete primitive-prefix head records for both ordinary return families

Let `M(n,z)` be Agent 1's exact `runWithMax` interpreter over the literal original source zipper, returning final configuration, signed head displacement and maximum head displacement reached at **any** prefix including the initial position.

| Input | Exact source time | Source endpoint | Final head shift | Maximum head shift | Starting rightmost marked coordinate relative to input head |
| --- | ---: | --- | ---: | ---: | ---: |
| `junc 0 v (w+3)` | `2*v+27` | `junc (v+3) 0 w` | `2*v+3` | `2*v+3` | `2*v+w+6` |
| `junc (u+1) v (w+2)` | `4*v+10` | `junc u (v+2) w` | `-2` | `2*v+2` | `2*v+w+5` |

Source modules [ZeroRegularHeadMax.lean](ZeroRegularHeadMax.lean) and [PositiveRegularHeadMax.lean](PositiveRegularHeadMax.lean) give kernel-certified exact equations `junc0_regular_max` and `juncPos_ordinary_max`. Their universal consequences `junc0_regular_prefix_before_old_mark` and `juncPos_ordinary_prefix_before_old_mark` show that for **every** `t` through the complete macro, the relative head position satisfies the strict bound in the final column.

The positive-left proof is an exact all-parameter composition of:
- Four initial steps with maximum displacement 0.
- A `2*(v+1)`-step `A/0,B/1` sweep, moving right to displacement `2*v+2` with no overshoot.
- A `2*(v+2)`-step `A/1,F/1` sweep, moving left by `2*(v+2)` and never exceeding its entry head.

The zero-left proof composes the previously source-proved 20-step head-prefix and `B/0,C/1` maximum lemmas with the final `B/1` step. The resulting exact maximum equals the positive final shift `2*v+3`.

## Physical machine lift and conservation

[PhysicalRegularHeadMax.lean](PhysicalRegularHeadMax.lean) invokes the existing original-table `BB429DeltaPhysicalBridge.source_runWithDelta_rep` and the previously certified `W4HeadPrefix.runWithMax_toDelta`.

For every original infinite-tape physical configuration `c` representing either prescribed source input, and **every** allowed primitive prefix `t`, it produces an original-machine raw run `run target429 t c = some d` with:

- Zero-left ordinary: `d.head < c.head + (2*v+w+6)`.
- Positive-left ordinary: `d.head < c.head + (2*v+w+5)`.

Both are genuinely whole-tape source-transported statements, independent of finite tape windows or simulation cutoffs. Moreover their full-run endpoint theorems certify the exact original-machine raw configurations and **conservation of the absolute rightmost marked cell**:

```text
zero-left:    end.head + (w+3)             = start.head + (2*v+w+6)
positive-u:   end.head + (2*(v+2)+w+3)     = start.head + (2*v+w+5)
```

The length identities use the exact `junc` right list, whose last `true` is at right displacement `2*v+w+3` relative to its input head. These equalities mean the same physical frontier is available as a candidate inductive invariant across arbitrary sequences of these regular returns. Both return types are already source-certified C/0-free by [Agent 1](../agent1-429-w4-boundary/README.md) and [Agent 30](../agent30-429-positive-safe/README.md); the new contribution is their **exact maximum head geometry and conserved physical marker**.

## Root-sensitive remaining problem

In an exact `junc 0 v 1` exceptional return, Agent 1's source-certified C/0 events are located at positions `2v+7` and `2v+10`, three and six cells beyond its old rightmost marked cell `2v+4`; they are safe local head records with blank right neighbors. An exact `junc 0 v 2` source event likewise lies two cells beyond its old marker. The results here ensure ordinary returns cannot cross the existing marked frontier. This provides a concrete induction route: establish a genuine blank-origin chart entry satisfying a history bound, prove the bound is maintained across **all exceptional as well as ordinary** chart exits, and use the source-certified physical fatal C/01 equivalence to close the halting question.

Crucially, the abstract chart-entry and exceptional-closure obligations remain open. Global head-record safety cannot be inferred merely from local record certificates; an arbitrary prepared `junc` can have earlier physical history outside the quantified segment. Prepared synthetic tapes can halt elsewhere. No all-time nonhalting theorem for the real blank run or BB(6) bound follows.

This material stays in `im-results/`, as intermediate formal infrastructure rather than an academically novel BB(6) solution. The reusable manual-only original-source audit is [`agent1-429-w4-scanE.yml`](../../.github/workflows/agent1-429-w4-scanE.yml).
