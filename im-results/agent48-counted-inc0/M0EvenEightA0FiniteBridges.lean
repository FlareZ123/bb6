import ChampionRootBridge
import CountedQ4Prefix

namespace BB6Coverage.Agent48M0EvenEightA0FiniteBridges

open BB6Coverage.Agent48Champion
open BB6Coverage.Agent6Q4Prefix

/-- The fixed ten-step setup after the a=0 valuation prefix.  Its input
window is [0,9]: head bit 1, then 011100111. -/
def a0SetupStart : FConfig := ⟨1,0,[0,2,3,4,7,8,9]⟩

/-- The ten-step setup consumes the first d1 block and leaves a d0 block
at the right edge of its written window. -/
def a0SetupEnd : FConfig := ⟨1,10,[9,6,5,4,3,2,1]⟩

theorem a0_setup_10 :
    fRun tm2 10 a0SetupStart = some a0SetupEnd := by
  decide

/-- All pre-transition heads of the ten-step setup lie in [0,9]. -/
def a0SetupInside (x : Int) : Bool := decide (0 ≤ x ∧ x ≤ 9)

theorem a0_setup_heads :
    (List.range 10).all (fun k =>
      a0SetupInside ((fRun tm2 k a0SetupStart).getD a0SetupStart).head) = true := by
  decide

/-- Lift the ten-step setup to an arbitrary tape agreeing on [0,9]. -/
theorem a0_setup_at (T : Int → Bool) (h : Int)
    (hmatch : ∀ x, a0SetupInside x = true →
      T (h+x) = decide (x ∈ a0SetupStart.marked)) :
    run tm2 10 ⟨1,h,T⟩ =
      some ⟨1,h+10,frameAt T h a0SetupInside a0SetupEnd⟩ := by
  simpa [a0SetupStart,a0SetupEnd] using
    bridgeAt T h a0SetupInside a0SetupStart a0SetupEnd 10 rfl
      a0_setup_10 a0_setup_heads hmatch

/-- The fixed 29-step return bridge.  Its input window is [-4,4]:
bits 1,0,0,1,0 followed by four blanks. -/
def a0ReturnStart : FConfig := ⟨1,0,[-4,-1]⟩

/-- The return bridge writes the nine-cell right word 011100111 and
moves five cells left into state 3. -/
def a0ReturnEnd : FConfig := ⟨3,-5,[-3,-2,-1,2,3,4]⟩

theorem a0_return_29 :
    fRun tm2 29 a0ReturnStart = some a0ReturnEnd := by
  decide

/-- All pre-transition heads of the return bridge lie in [-4,4]. -/
def a0ReturnInside (x : Int) : Bool := decide (-4 ≤ x ∧ x ≤ 4)

theorem a0_return_heads :
    (List.range 29).all (fun k =>
      a0ReturnInside ((fRun tm2 k a0ReturnStart).getD a0ReturnStart).head) = true := by
  decide

/-- Lift the 29-step return bridge; the cell at h-5 and the entire
left exterior are preserved from the input tape. -/
theorem a0_return_at (T : Int → Bool) (h : Int)
    (hmatch : ∀ x, a0ReturnInside x = true →
      T (h+x) = decide (x ∈ a0ReturnStart.marked)) :
    run tm2 29 ⟨1,h,T⟩ =
      some ⟨3,h-5,frameAt T h a0ReturnInside a0ReturnEnd⟩ := by
  simpa [a0ReturnStart,a0ReturnEnd] using
    bridgeAt T h a0ReturnInside a0ReturnStart a0ReturnEnd 29 rfl
      a0_return_29 a0_return_heads hmatch

#print axioms a0_setup_10
#print axioms a0_setup_heads
#print axioms a0_setup_at
#print axioms a0_return_29
#print axioms a0_return_heads
#print axioms a0_return_at

end BB6Coverage.Agent48M0EvenEightA0FiniteBridges
