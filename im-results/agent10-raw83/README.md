# Raw83 four-hole exact weighted closure

**Kernel accepted.** Original-source Lean 4.36.0-rc2 CI [45755362807](https://github.com/FlareZ123/bb6/actions/runs/45755362807) at revision `8d8a3fcc59600146fb25eb70afc2f34a31c99cb3` proves

```lean
BB6.Agent10Raw83.all_completions :
  ∀ m, compatible parent m → WeightedBound 514 m

BB6.Agent10Raw83.exact_bound (B : Nat) :
  (∀ m, compatible parent m → WeightedBound B m) ↔ 514 ≤ B
```

The parent is `1RB---_1RC1LF_0RD---_1LD1RE_---0LB_---0RA`, the F1=0RA sibling of the rooted B1=1LF path. The exact maximum is attained by `1RB0LE_1RC1LF_0RDHHH_1LD1RE_0RF0LB_0LB0RA`: 513 ordinary transitions, final halt, zero incoming delay. The source-connected witness is in `A10Raw83Exact.lean`.

The exhaustive audit uses 228 splits, 3717 side-cycle leaves, 1471 last-hole leaves and 57 FAR leaves (54 ordinary FAR and three width-1 run-quotient block FAR). All 390625 physical completions are covered. No delayed leaf or growth assumption is required.

Artifact `raw83-parent-proof`: ID 15087730774, SHA256 `89ea0f6ae8f0da2d11f86c959b1d848d7c4ef44e933899bfc2654c7dc1a9a1a2`. The earlier failed run used certificate support 4 rather than 6; correcting the support parameter left all child checks unchanged. The complete exact-bound target succeeded with its standard-axiom gate. Integration into the global canonical quotient remains separate.
