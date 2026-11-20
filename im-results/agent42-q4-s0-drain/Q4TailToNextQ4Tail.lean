import Q4TailToS0Frame
import P2S0ToNextQ4Tail
import Lean.Elab.Tactic.Omega

/-!
# One complete q4Tail-to-q4Tail recurrence step

This composes the generic q4Tail-to-S0 frame identity with the existing
corrected P2 S0 drain/postlude and next first-cycle prefix.  It is
conditional on the source-side residual/blank-ray facts and the
three-cell 100 tail guard; it does not claim those facts for a root.
-/

namespace BB6Coverage.Agent42Q4TailToNextQ4Tail

open BB6Coverage
open BB6Coverage.Agent6Q4Prefix
open BB6Coverage.Agent8S1Encoder
open BB6Coverage.Agent8Q4Suffix
open BB6Coverage.Agent42Q4TailToS0Frame
open BB6Coverage.Agent44P2Postlude
open BB6Coverage.Agent48P2NextQ4Tail
open BB6Coverage.Agent48Q4S0Macros
open BB6Coverage.Agent48PositiveZFirstCyclePrefix

set_option maxHeartbeats 3000000

/-- A q4Tail frame with the authentic P2 residual and blank right ray
feeds the corrected S0 drain/postlude and the next type-A prefix,
returning another q4Tail frame. -/
theorem q4Tail_to_next_q4Tail
    (m n : Nat) (tail : List Bool) (T : Int → Bool) (h : Int)
    (hn : 2 ≤ n)
    (hleft : T (h-1) = true)
    (hres : ∀ i : Nat,
      T (h-2-(i:Int)) = sideBit (p2ResidualLeft m tail) i)
    (hright : ∀ i : Nat,
      T (h+(3*n:Int)+5+(i:Int)) = false)
    (hhead : h = (m:Int)+7)
    (ht0 : sideBit tail 0 = true)
    (ht1 : sideBit tail 1 = false)
    (ht2 : sideBit tail 2 = false) :
    let a : Nat := n-1
    let H : Nat := m+2+3*n
    let nNext : Nat := 2^a
    let P := p2PostludeFrame m n tail
    let T1 := (frameAt P.tape 1
      firstCyclePrefix22Inside firstCyclePrefix22End).tape
    let h1 : Int := 1+4+(H:Int)
    let T2 := afterFirstCycleTwoZero T1 h1
    let h2 : Int := h1+2
    let T3 : Int → Bool := d0Sweep nNext T2 h2
    let g : Int := h2+3*(nNext:Int)
    run tm2
      ((6*4^a+42*2^a-12*a-48) + (3*H-5) +
        (22+H+2+3*nNext+29))
      (frameAt (d0Sweep n T h) (h+(3*n:Int))
        q4TailInside q4TailEnd) =
    some (frameAt T3 g q4TailInside q4TailEnd) := by
  have hframe := q4Tail_frame_eq_s0Config n
    (p2ResidualLeft m tail) T h hn hleft hres hright
  have hH : h+(3*n:Int)-5 = (m+2+3*n:Int) := by omega
  rw [hframe]
  simpa [hH] using
    (p2S0_to_next_q4Tail m n tail hn ht0 ht1 ht2)

#print axioms q4Tail_to_next_q4Tail

end BB6Coverage.Agent42Q4TailToNextQ4Tail
