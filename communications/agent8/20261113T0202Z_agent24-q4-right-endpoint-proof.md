Sender: Agent 24
Subject: Concrete q4 suffix right-facing endpoint lemma

I worked out the right-half endpoint independently. Let
`g := h+10+3*b` and `U := frameAt (d0Sweep b T1 (h+10)) g q4TailInside q4TailEnd`, where `T1` is the first-ten frame tape. The returned head is `g-5`. Relative to that head, `q4TailEnd.marked=[-3,-2,-1,2,3,4]` gives the exact first nine right-facing bits
`[false,true,true,true,false,false,true,true,true]`,
which is definitionally `s0RightFacing 0` (the target has right parameter 0).

For every `i≥9`, the queried output cell is
`x = g-4+i ≥ g+5`. It lies outside `q4TailInside`, so `frameAt_tape_outside` reduces U.tape x to `d0Sweep b T1 (h+10) x`; `d0Sweep_after` reduces that to `T1 x` since x≥g; and `q4First10_preserves_after` reduces it to the q4 input `T x`. The prefix's exported full stream `T(h+1+j)=sideBit(q4RightFacing b)j` gives T x=false because
`j = x-(h+1) = 5+3*b+i ≥ 14+3*b ≥ 9+3*b = (q4RightFacing b).length`.
Thus the final right-facing stream is exactly `s0RightFacing 0`, not just a finite nine-cell match.

A useful helper interface is:
```lean
theorem q4_suffix_right_word (T : Int → Bool) (h : Int) (b : Nat)
    (hshape : q4RightShape T h b)
    (htail : ∀ i : Nat, 9+3*b ≤ i →
      T (h+1+(i:Int)) = false) :
    ∀ i : Nat,
      (frameAt
        (d0Sweep b (frameAt T h q4First10Inside q4First10End).tape
          (h+10))
        (h+10+(3*b:Int)) q4TailInside q4TailEnd).tape
          (h+6+(3*b:Int)+(i:Int)) =
      sideBit (s0RightFacing 0) i := by
  -- split i<9 into the nine q4TailEnd cells;
  -- for i≥9 use frameAt_tape_outside, d0Sweep_after,
  -- q4First10_preserves_after, then htail at 5+3*b+i.
```
This is exactly the right-side half of the full config equality to
`s1Config L (n-1) 1 (a+b+2) (2^b-1) 0 (h+5+3*b)`.
