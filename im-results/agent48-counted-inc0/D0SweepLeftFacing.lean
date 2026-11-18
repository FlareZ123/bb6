import Q4Suffix
import S1Encoder
import Lean.Elab.Tactic.Omega

/-!
# Left-facing d0-counter invariant for the counted block sweep

A state-1 scan converts n right-facing 111 blocks into n left-to-right
001 blocks. After q4Tail moves the head five cells left, the left-facing
stream begins with exactly d0pow (n-1). The final 1 of that counter is
the first separator cell immediately to the left of the scan start.

This lemma isolates the counter-width fact needed to identify later S0
inputs. It is independent of the exterior tape except for that boundary 1.
-/

namespace BB6Coverage.Agent48D0SweepLeftFacing

open BB6Coverage
open BB6Coverage.Agent8S1Encoder
open BB6Coverage.Agent8Q4Suffix
open BB6Coverage.Agent8Rst1Prime

/-- The i-th bit of d0pow n is 001 repeated. -/
theorem sideBit_d0pow_pattern (n i : Nat) (hi : i < 3*n) :
    sideBit (d0pow n) i = decide (i % 3 = 2) := by
  induction n generalizing i with
  | zero => omega
  | succ n ih =>
      cases i with
      | zero => simp [d0pow,sideBit,d0]
      | succ i =>
          cases i with
          | zero => simp [d0pow,sideBit,d0]
          | succ i =>
              cases i with
              | zero => simp [d0pow,sideBit,d0]
              | succ i =>
                  have hi' : i < 3*n := by omega
                  have hmod : (i+3)%3 = i%3 := by omega
                  simpa [d0pow,sideBit,d0,hmod] using ih i hi'

/-- Reading left from the head five cells before the end of an n-block
d0Sweep gives exactly d0pow (n-1), provided the nearest cell to the
left of the sweep start is 1. -/
theorem d0Sweep_leftFacing_d0pow
    (n : Nat) (T : Int → Bool) (h : Int)
    (hn : 2≤n) (hleft : T (h-1) = true)
    (i : Nat) (hi : i < 3*(n-1)) :
    d0Sweep n T h (h+(3*n:Int)-5-(i:Int)) =
      sideBit (d0pow (n-1)) i := by
  have hside :
      sideBit (d0pow (n-1)) i = decide (i%3=2) :=
    sideBit_d0pow_pattern (n-1) i (by omega)
  have hmod : i%3=0 ∨ i%3=1 ∨ i%3=2 := by omega
  rcases hmod with h0|h1|h2
  · let q : Nat := i/3
    let j : Nat := n-q-2
    have hiq : i=3*q := by dsimp [q]; omega
    have hj : j<n := by dsimp [j]; omega
    have heq : h+(3*n:Int)-5-(i:Int) = h+3*(j:Int)+1 := by
      rw [hiq]
      dsimp [j]
      omega
    have hb := d0Sweep_block n T h j hj
    rw [heq,hside]
    simpa [h0] using hb.2.1
  · let q : Nat := i/3
    let j : Nat := n-q-2
    have hiq : i=3*q+1 := by dsimp [q]; omega
    have hj : j<n := by dsimp [j]; omega
    have heq : h+(3*n:Int)-5-(i:Int) = h+3*(j:Int) := by
      rw [hiq]
      dsimp [j]
      omega
    have hb := d0Sweep_block n T h j hj
    rw [heq,hside]
    simpa [h1] using hb.1
  · let q : Nat := i/3
    by_cases hq : q=n-2
    · have hiq : i=3*(n-2)+2 := by
        dsimp [q] at hq
        omega
      have heq : h+(3*n:Int)-5-(i:Int) = h-1 := by
        rw [hiq]
        omega
      rw [heq,hside]
      have hbefore : d0Sweep n T h (h-1) = T (h-1) :=
        d0Sweep_before n T h (h-1) (by omega)
      rw [hbefore]
      simpa [h2] using hleft
    · let j : Nat := n-q-3
      have hiq : i=3*q+2 := by dsimp [q]; omega
      have hj : j<n := by dsimp [j]; omega
      have heq : h+(3*n:Int)-5-(i:Int) = h+3*(j:Int)+2 := by
        rw [hiq]
        dsimp [j]
        omega
      have hb := d0Sweep_block n T h j hj
      rw [heq,hside]
      simpa [h2] using hb.2.2

/-- q4Tail does not change cells strictly to the left of its four-cell
left boundary. -/
private theorem q4Tail_frame_preserves_before
    (T : Int → Bool) (h x : Int) (hx : x < h-4) :
    (frameAt T h q4TailInside q4TailEnd).tape x = T x := by
  rw [frameAt_tape]
  have hnot : q4TailInside (x-h) = false := by
    simp [q4TailInside]
    omega
  simp [frameAt_tape,hnot]

/-- The exact left-facing counter prefix after d0Sweep followed by q4Tail
is d0pow (n-1). This proves the width is n-1, not merely a sampled run
length. -/
theorem q4Tail_output_leftCounter
    (n : Nat) (T : Int → Bool) (h : Int)
    (hn : 2≤n) (hleft : T (h-1) = true) :
    ∀ i : Nat, i < 3*(n-1) →
      (frameAt (d0Sweep n T h) (h+(3*n:Int))
        q4TailInside q4TailEnd).tape
        (h+(3*n:Int)-5-(i:Int)) =
      sideBit (d0pow (n-1)) i := by
  intro i hi
  let g : Int := h+(3*n:Int)
  have hpres :
      (frameAt (d0Sweep n T h) g q4TailInside q4TailEnd).tape
        (g-5-(i:Int)) =
      d0Sweep n T h (g-5-(i:Int)) := by
    apply q4Tail_frame_preserves_before
    dsimp [g]
    omega
  have hscan := d0Sweep_leftFacing_d0pow n T h hn hleft i hi
  change (frameAt (d0Sweep n T h) g q4TailInside q4TailEnd).tape
    (g-5-(i:Int)) = _
  rw [hpres]
  simpa [g] using hscan

#print axioms sideBit_d0pow_pattern
#print axioms d0Sweep_leftFacing_d0pow
#print axioms q4Tail_frame_preserves_before
#print axioms q4Tail_output_leftCounter

end BB6Coverage.Agent48D0SweepLeftFacing
