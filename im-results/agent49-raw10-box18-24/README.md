# Raw10 base34 rectangles 18–24: source-checked partial cut

Seven exact, pairwise-disjoint domain rectangles inside the `B0=1LC` first-one parent are covered by an exhaustive first-hole proof tree. Each rectangle has 7,500 completions (52,500 total). Their common weighted upper bound is **598**: the largest ordinary prefix is 592 transitions, with the final halt and at most five initial blank-delay steps included.

This is a partial parent cut, not a determination of BB(6). The other raw10 remainder boxes, the separate held FARv3 leaf, and all other root-roster entries remain obligations.

## Exact domains and search certificate

Fixed encoded rows are `[8,a,11,6,17,13,11,-1,2,23,-1,-1]`, with `a = 19,18,17,8,6,3,2` respectively. D1 and F1 are unrestricted; F0 ranges over `[0,2,4,11,12,14,15,16,19,20,22,24]`. Zero denotes a genuine halt and -1 a generator hole.

The seven domains are checked against `raw10Remainder` indices 18–24. The source consumer exports:
- `source_indices_checked : sourceIndexCheck = true`;
- `rectBound`: every completion of each listed rectangle satisfies `WeightedBound 598`;
- `residual_without_18to24`: for any `B ≥ 598`, bounds on every remainder box with `closedMatch = false` extend to every box in `raw10Remainder`, using `rectBound` for the seven matched rectangles.

The search exhaustively branches over allowed ordinary actions, bounds genuine halt branches at first holes, uses translated half-line cycles and local-window invariants, and invokes the last-hole theorem when all other instructions are assigned. No candidate leaves remain open.

| A1 | Branch nodes | Right cycles | Left cycles | Ngram leaves | Last-hole leaves | Max hole time |
|---:|---:|---:|---:|---:|---:|---:|
| 19 | 8 | 69 | 66 | 14 | 23 | 85 |
| 18 | 8 | 70 | 63 | 14 | 25 | 592 |
| 17 | 8 | 48 | 78 | 19 | 27 | 85 |
| 8 | 9 | 55 | 89 | 20 | 31 | 85 |
| 6 | 8 | 66 | 68 | 14 | 24 | 85 |
| 3 | 9 | 81 | 71 | 14 | 29 | 85 |
| 2 | 8 | 69 | 66 | 14 | 23 | 85 |

## Original-source Lean acceptance

Archive SHA-256: `4953030d5ed1231349228a856045dc8eaf37cc69d476c3a937006fb6a3856e55`. The existing manual target `weighted-tnf-raw10-box18to24` unpacks `source.tar.xz`, runs `generate.py`, and compiles the generated source against the repository's Lean modules.

- **Run 45690247771 — success:** fixed the `RootRaw10Core.lean` Move construction and compiled the 61-module original-source closure.
- **Run 45690983793 — success:** exposed the exact theorem signatures for the source index check and residual consumer.
- **Run 45692778592 — success:** compiled 63 project modules from both the generated source and the new root-level consumer `Raw10Box18to24Bridge.lean` under Lean 4.36.0-rc2. The workflow's `sorryAx|native_decide` rejection check passed.

The generated source theorem profiles are:
- `source_indices_checked`: [propext, Quot.sound]
- `rectBound`: [propext, Classical.choice, Quot.sound]
- `residual_without_18to24`: [propext, Classical.choice, Quot.sound]

The new source-checked adapter exports:
- `raw10_cover_after_boxes18to24`: consumes the seven rectangles inside the parent `Cover`, retaining the explicit `closedMatch = false` complement and the held-leaf premise;
- `exact_from_raw10_boxes18to24`: lifts that parent cover through the first-one root quotient to `ExactBB6 B`, parameterized by the roster, its quotient-soundness theorem, exact parent membership, the held-leaf bound, the false-match complement bounds, all other roster covers, and the champion witness.

Both adapter theorems depend only on [propext, Classical.choice, Quot.sound]. The root-level adapter is generic and does **not** silently assume a roster. Its intended instantiation is the accepted post-raw114 77-entry roster, with that roster's soundness and exact membership of this parent supplied explicitly.

## Remaining obligations and limitations

1. Instantiate the generic adapter with the accepted canonical77 roster. A direct source-closure import of `CanonicalRaw114Accepted`/`Canonical77HeldMembership` currently encounters missing archived imports `FourHoleData` (and, via the larger `Root109Membership` chain, `Raw66Data`). The generic adapter deliberately avoids these legacy imports; it does not claim the canonical77 instantiation is already compiled here.
2. Prove the held FARv3 leaf in the Lean `WeightedBound` interface. The existing `raw10_cover` explicitly takes this as `hHeld`; the Coq FARv3 result is not silently treated as a Lean proof.
3. Discharge the explicit `closedMatch = false` complement of `raw10Remainder` and every other roster entry.

The earlier local fixture checks were not used as source acceptance. The accepted claims above come from the original-source CI closure. Local shell/Python execution was unavailable in this invocation, so no local Lean compile is claimed.
