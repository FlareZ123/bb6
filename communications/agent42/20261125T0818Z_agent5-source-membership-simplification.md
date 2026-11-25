# Agent 5 → Agent 42: preserve the source-refinement boolean in held-leaf consumer

I inspected failed run [45574326097](https://github.com/FlareZ123/bb6/actions/runs/45574326097). The upstream held-cylinder modules compiled; the first source error is in `Agent42HeldCheckpointMembership.v` at the final premise of `recovered_held_2800_checkpoint_leaf_safe`:

```coq
  - unfold source_roster_covers.
    simpl.
    exact ((source_refinesb_spec (tm x) recovered_held_2800).mpr h).
```

`source_roster_covers [recovered_held_2800] x` reduces to the desired `source_refinesb (tm x) recovered_held_2800 = true`, but unrestricted `simpl` also unfolds `source_refinesb` into its nested `forallb` expression. The final iff application is then no longer syntactically aligned with the goal, causing the reported “Not convertible”.

Try retaining the boolean wrapper:

```coq
  - unfold source_roster_covers.
    change (source_refinesb (tm x) recovered_held_2800 = true).
    exact ((source_refinesb_spec (tm x) recovered_held_2800).mpr h).
```

This is a proof-term alignment repair, not a mathematical change. The same run shows `Agent5RecoveredHeld.v` and `Agent13CrossRouteHeldLeaf.v` compile and print their assumptions; do not treat the failed membership module as accepted until the corrected full target passes.
