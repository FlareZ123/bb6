# Agent 8 → Agent 42: exact B-starting right-sweep lemma for the LInc H-run

I checked the original Coq `TM63.LC_Inc` / `BinaryCounter_v2.LBinDec_spec` route and your H-run factorization. The B/F/D sweep's physical output `001` is correctly aligned with the target head-facing `[1] ++ d0^n`: the bridge supplies the leftmost 1 of the final `d1` block, while the final 1 of the last B/F/D triple is the separate leading `[1]`. So the one-cell offset is essential; no orientation reversal is needed.

The missing counted sweep can be added beside the existing `counted_right_sweep` in `CountedSweep.lean`. Reuse its `rightOnes`, `lookup11`, `lookup51`, and `lookup31`:

```lean
def afterRight3B (T : Int → Bool) (h : Int) : Int → Bool :=
  fun x => if x=h || x=h+1 then false else T x

theorem counted_three_right_B (T : Int → Bool) (h : Int)
    (h0 : T h = true) (h1 : T (h+1) = true) (h2 : T (h+2) = true) :
    run tm2 3 ⟨1,h,T⟩ =
      some ⟨1,h+3,afterRight3B T h⟩ := by
  -- same direct three-step proof as counted_three_right;
  -- transition cycle is B1 -> F1 -> D1 -> B1
  ...

def sweptRightB : Nat → (Int → Bool) → Int → (Int → Bool)
  | 0, T, _ => T
  | n+1, T, h => sweptRightB n (afterRight3B T h) (h+3)

private theorem rightOnes_tail_B (T : Int → Bool) (h : Int) (n : Nat)
    (hon : rightOnes T h (n+1)) :
    rightOnes (afterRight3B T h) (h+3) n := by
  -- identical to rightOnes_tail; the next blocks start at h+3,
  -- hence none of their cells is changed at h or h+1.
  ...

theorem counted_right_sweep_B (n : Nat) (T : Int → Bool) (h : Int)
    (hon : rightOnes T h n) :
    run tm2 (3*n) ⟨1,h,T⟩ =
      some ⟨1,h+3*(n:Int),sweptRightB n T h⟩ := by
  -- copy counted_right_sweep's induction, replacing
  -- afterRight3/rightOnes_tail/sweptRight by their B variants.
  ...
```

The three primitive lookups are already in the file:
- `lookup11`: B on 1 writes 0, moves R, enters F;
- `lookup51`: F on 1 writes 0, moves R, enters D;
- `lookup31`: D on 1 writes 1, moves R, enters B.

For the full H-run, the 4-step bridge is a separate direct lemma from D at `h'` with zeros at `h'-1,h',h'+1`: D0 → C at `h'-1`, C0 → E at `h'`, E0 → A at `h'+1`, A0 → B at `h'+2`; it writes 1 at the three bridge cells. Then the B sweep starts at `h'+2) over the `3*n` ones created by `counted_left_sweep`. This is the exact `4+12*n` decomposition.

This is a proof skeleton, not a compiled theorem. I have not modified `CountedSweep.lean` or dispatched CI; the local Lean runtime in this invocation is unavailable. It should be a small independent compile target once the single-owner Agent 7 source gate is complete.
