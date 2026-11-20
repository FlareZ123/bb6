# Direct drift proof for the Agent 27 five-slot leaf

This file gives a small, direct proof for the same five-slot partial table
defined as `BB6Coverage.agent27WordPump` in
`im-results/agent27-translated-five-slot/TranslatedFiveSlot.lean`.
The transition rows are transcribed identically:

| Read slot | Transition |
|---|---|
| A/0 | 1RB |
| B/0 | 1LC |
| C/1 | 0RD |
| D/1 | 1RE |
| E/0 | 1LC |

## Invariant

For every compatible total machine (m), after (2+3k) moves the machine is
in state C, its head is at cell (k), and its tape is 1 exactly at cells
(k) and (k+1) (0 everywhere else).

- The first two transitions A/0 and B/0 establish the invariant at (k=0).
- From the invariant configuration, C/1 writes 0 at (k), moves right to
  (k+1), and enters D.
- D/1 writes 1 at (k+1), moves right to (k+2), and enters E.
- E/0 writes 1 at (k+2), moves left to (k+1), and returns to C.
  The two adjacent 1s have therefore shifted right by one cell.

All three transitions in the cycle are fixed by the partial table. The
intermediate configurations are also explicit, so every natural step count
is covered by (n=2+3k+r), (rin{0,1,2}). No compatible completion can
halt.

## Formal result

- `fiveSlot_never`: every total completion compatible with the five rows
  has a defined configuration at every finite time.
- `fiveSlot_cover`: for every natural bound, the entire five-slot cylinder
  is a certified leaf of `Cover (DecidedBelow bound)`.

The proof uses only `Frontier` and Lean core. It does not import the
translated finite-oracle or physical-lasso audit stacks. It can therefore
replace the translated-oracle leaf certificate in the larger graft while
leaving the parent's audit construction unchanged.

## Validation boundary

Locally typechecked with Lean 4.36.0-rc2 against the exact current-main
`Frontier.lean` blob (Git blob SHA
`115438c4f244b5416a91be4dd7a3f12103d5448d`). The direct theorem axiom
profiles are `[propext, Quot.sound]`; no `sorryAx` or project-specific
axiom is used.

This closes one five-slot cylinder only. It is not a global coverage proof,
does not determine BB(6), and has not yet been wired into
`FiveSlotLeafGraft.lean`.


## Integration sketch

The definitions `a0` through `e0`, their actions, and the nested
`p0` through `p4` refinements in `FiveSlotDirect.lean` are the same five
assignments and parent chain as `agent27A0` through `agent27E0` and
`agent27P0` through `agent27P4` in `TranslatedFiveSlot.lean`. A wrapper can
replace its translated-oracle import with `DirectFiveSlot` and alias those
names into `BB6Coverage`; then
`agent27WordPump_cover bound` is obtained from
`DirectFiveSlot.fiveSlot_cover bound`. This removes the translated finite
oracle from the wrapper's dependency closure. It does not remove the separate
`LassoTraceAudit` dependency used to establish that the P4 parent is open.

The module also exports `fiveSlot_is_p4_child`,
`p4_e0_unassigned`, and `fiveSlot_parent_compatible`, so the wrapper can
reuse the exact P4-child relation and parent-compatibility implication without
re-proving them.

The phase formulas are exported explicitly as `run_cycle`,
`run_phase_d`, and `run_phase_e`: they identify the exact configuration at
each residue class modulo three after the two-step startup, not merely the
existence of a run. The `run_exists` theorem then covers every finite time.
