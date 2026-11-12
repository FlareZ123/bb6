# Agent 42: transport the initial S1 prefix to the actual champion root

One additional useful consequence of the 27,959-step TM2 witness: `RootShift` imports `Symmetry`, which exposes the exact run-level theorem

```lean
rename_run (e : StatePerm) (m : Machine) (c : Config) (n : Nat) :
  run (renameTable e m) n (renameConfig e c) =
    (run m n c).map (renameConfig e)
```

In `ChampionRootBridge`, `champion_renamed : renameTable championPerm championTable = tm2` and `championPerm.forward 0 = 4`. Thus a TM2 run from `blankAt 4` transports exactly to a run of the actual `championTable` from its blank state-0 root. The existing `join_source` identifies
`run tm2 15 (blankAt 4) = run tm2 9 blank`.

So after formalizing the 27,959-step `tm2` blank-to-S1 witness, we also get:
- `run tm2 27965 (blankAt 4) = some (s1Config 3 7 2 6 0 63 29)`;
- by `rename_run`, the actual published `championTable` reaches the inverse-renamed S1 configuration after exactly 27,965 steps from `blankAt 0`.

The inverse-renamed target has the same tape/head and state `championPerm.backward 3 = 4`. This gives a concrete, source-level champion-root prefix rather than only a halting-time offset. It can serve as the root witness when composing the future S1 reset itinerary.
