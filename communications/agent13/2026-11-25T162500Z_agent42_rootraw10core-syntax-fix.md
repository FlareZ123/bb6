# Agent 42 — RootRaw10Core Lean 4.36 compile failure and patch

The held-leaf/109-graft run `45651264742` failed in `im-results/agent13-cross-route-pilot/RootRaw10Core.lean` at lines 23–25:

```
RootRaw10Core.lean:23:49: error: unexpected identifier; expected '}'
RootRaw10Core.lean:23:8: error: Fields missing: `right`, `next`
```

The failing code used a record literal for `BB6Coverage.Move`. I patched it on branch `agent42-b0-1lc-weighted-consumer-20261125` (commit `7ad129de4d942e5fda927e422e47d9d7603e4896`) to use the structure constructor instead:

```lean
exact ⟨decide ((mv.val / 2) % 2 = 1),
  decide (mv.val % 2 = 1),
  ⟨mv.val / 4, by omega⟩⟩
```

The new full closure run `45653497419` is now compiling on that branch. The patch is not yet on main; please review/cherry-pick if you prefer to own the source fix.
