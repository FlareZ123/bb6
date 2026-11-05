# Machine C: a second unbounded forced-inverse tower and sharp two-edge source cone

**Agent 3, 2026-11-05.** Intermediate Machine C mathematics, not a decision of the blank-start Machine C or of BB(6). The source-theorem chain has been checked in Lean 4.36.0-rc2 against unchanged repository section definitions.

## Source-level facts

The exact original-source section return map is `BB6.Agent46.secNext`. The rectangle `(16p+3,32q+16)` had already been proved absent from the actual blank-entry section orbit in `EvenChild.lean`. New `ChildATwoDepth.lean` proves something stronger:

- `child_A_two_witness`: for every `p,q : Nat`, there is an *actual* two-edge path
  `(8p+24q+10,4p+20q+7) → (16p+32q+17,16q+7) → (16p+3,32q+16)`.
- `child_A_no_three`: for any section starting pair and time `t`, the state `(16p+3,32q+16)` is impossible after `t+3` genuine returns. Thus **the all-start incoming ancestry length is exactly two**.
- Why: the final step has a unique source (`even_child_parent_iff`). Every parent of that unique source has first coordinate `2 mod 4`, odd second coordinate `3 mod 4` and second ≥7 (`odd_sliver_parents_forbidden`), so it cannot itself be a section output (`section_odd_image`). The two witness edges use one exact odd-bounce branch and the exact even-child source iff.

Full unchanged-source **manual Lean CI [41958713083](https://github.com/FlareZ123/bb6/actions/runs/41958713083) SUCCESS**. The source file is [ChildATwoDepth.lean](ChildATwoDepth.lean). The final theorem is a universal all-root bound, with no simulation cutoff.

## New 2D higher-stopping tower

Set

```text
J(q,0) = 512q+426
J(q,n+1) = 16J(q,n)+42
T(q,n) = (2J(q,n)+3,15J(q,n)+40).
```

`HighTowerA.lean` proves for **all natural** `q,n`:

1. `highA_halt_input`: `secNext T(q,n)=none`. This uses the original source-verified complete high-stopping Diophantine equation with parameter `m=1`.
2. `highA_exact_depth`: the exact Agent15 affine forced-inverse depth of the right counter is `4n+4`.
3. `highA_normalized_cone`: the exact affine normalizer `P(q,n)` has `P.1 mod16=3`, `P.2 mod32=16`, and `P.2≥16`. In fact `P.2=480q+400`. Thus it belongs to the entire previously certified A rectangle.
4. `highA_blank_unreachable`: no member `T(q,n)` is ever reached by the *actual blank-entry section orbit*; this is an exact source theorem with no finite trace length, from the original `reach_iff_normalize` and A-rectangle exclusion.
5. `highA_power_identity`: `15J(q,n)+42=16^(n+1)*(480q+402)`, directly exposing its valuation depth and separating it from the previous `4n+3` stopping tower.

Example: `q=n=0` gives `J=426` and the authentic hypothetical stopping input `(855,6430)`; the full affine normalizer is `(12899,400)`, inside the source-certified A rectangle.

**Full unchanged-source CI [41959481261](https://github.com/FlareZ123/bb6/actions/runs/41959481261) SUCCESS.** The job's `#print axioms` reports `[propext, Classical.choice, Quot.sound]` for the halt, depth, normalization, and blank nonreach theorems and `[propext, Quot.sound]` for the power identity, with no `sorryAx`. The source is [HighTowerA.lean](HighTowerA.lean).

## What remains open

This family is disjoint from the earlier `4n+3` tower by exact forced inverse depth. Nonetheless it excludes a proper part of an infinite fatal stopping family; **it does not eliminate the entire high stopping locus**, settle a real six-state machine, or improve a universal BB(6) bound. The main research value is the all-start two-edge structural obstruction and its composition with unbounded affine depth. External novelty and overlap with stronger exact source barriers need further review; do not promote this to `results/` without that check.

Next: extend `HighTowerAllStart.lean`'s exact all-start ancestry theorem to the new A tower, predicting sharp maximum path length `4n+6`; investigate larger sets of stopping inputs whose normalized source lies in finite-depth inverse cones, then seek a mechanism closing a **complete** true-blank stopping family rather than further isolated residues.
