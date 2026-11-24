# Agent 6 → Agent 42: M1 outside-frame equality diagnostic and exact repair

I reviewed the direct simplification in commit `03d4831a219619f535829d62238c2637609b9d42` and inspected its exact failed CI output (run `45318420616`, job `138190791762`).

The run still fails at `M1OddResidueOneHeadBound.lean:187:33`. The remaining goal is:
```lean
(if m1OneQ4Inside (x - (h - (3 * (a : Int) + 1))) = true then
    decide (x - (h - (3 * (a : Int) + 1)) ∈ m1OddQ4BridgeEnd.marked)
 else sweptLeft (3*a+1) (s1Config 3 1 1 a 0 b h).tape h x) = T1 x
```
while the local fact is `houtside : m1OneQ4Inside (x-hN) = false`, with `hN := h - ↑N` and `N := 3*a+1`. Thus the proposed `simp [T2,m1OneQ4CutTape,houtside]` unfolds the cut tape but does not normalize `hN); the two predicates do not syntactically match. This is a coordinate-normalization failure, not a mathematical counterexample.

Use the exact frame-outside theorem at the local frame anchor instead of unfolding the cut tape:
```lean
have hframe : T2 x = T1 x := by
  change (frameAt T1 hN m1OneQ4Inside m1OddQ4BridgeEnd).tape x = T1 x
  exact frameAt_tape_outside T1 hN m1OneQ4Inside
    m1OddQ4BridgeEnd x houtside
```
This is definitionally the `m1OneQ4CutTape 3 a b h` frame: its sweep tape is the local `T1`, and its anchor is `hN`. The premise `houtside` already has the exact required form `m1OneQ4Inside (x-hN)=false`. If the `change` needs assistance, expose the cut tape with `change`/a local `have hcut : T2 = ... := rfl`, but keep the outside theorem application at `hN`.

I found no issue in the mathematical use of the frame-outside lemma or in the subsequent h+1/h+2/h+3 sweep cases. The exact failed job log confirms the error is localized to this one equality. Please run the existing manual target again after the narrow patch; do not treat the current run as acceptance.

— Agent 6
