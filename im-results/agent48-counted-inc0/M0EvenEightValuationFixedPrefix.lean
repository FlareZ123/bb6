import M0EvenEightQ4Bridge
import CountedQ4Prefix
import Lean.Elab.Tactic.Omega

namespace BB6Coverage.Agent48M0EvenEightValuationFixedPrefix

open BB6Coverage.Agent48Champion
open BB6Coverage.Agent48M0EvenEightQ4Bridge
open BB6Coverage.Agent6Q4Prefix

/-- The 44-step bridge input with the not-yet-read boundary bit at -14. -/
def bridgeStartWithBit (bit : Bool) : FConfig :=
  { m0EvenEightBridgeStart with
    marked := if bit then (-14) :: m0EvenEightBridgeStart.marked
      else m0EvenEightBridgeStart.marked }

/-- The fixed 44-step output; the boundary bit at -14 is preserved. -/
def bridgeMidWithBit (bit : Bool) : FConfig :=
  { state := 3
    head := -14
    marked := if bit then
      [-12,-11,-10,-9,-8,-7,-6,-5,-4,-3,-2,-1,0,-14,2,3]
      else [-12,-11,-10,-9,-8,-7,-6,-5,-4,-3,-2,-1,0,2,3] }

/-- The first 44 moves never read the variable cell at -14. -/
theorem bridge_prefix44 (bit : Bool) :
    fRun tm2 44 (bridgeStartWithBit bit) =
      some (bridgeMidWithBit bit) := by
  cases bit <;> decide

/-- All pre-transition heads of the fixed prefix lie in [-13,3]. -/
def bridgeInside44 (x : Int) : Bool := decide (-13 ≤ x ∧ x ≤ 3)

private theorem bridge_heads44_all (bit : Bool) :
    (List.range 44).all (fun k =>
      match fRun tm2 k (bridgeStartWithBit bit) with
      | none => true
      | some f => bridgeInside44 f.head) = true := by
  cases bit <;> decide

theorem bridge_heads44 (bit : Bool) (k : Nat) (hk : k < 44) :
    bridgeInside44
      ((fRun tm2 k (bridgeStartWithBit bit)).getD
        (bridgeStartWithBit bit)).head = true := by
  have hall := List.all_eq_true.mp (bridge_heads44_all bit) k
    (List.mem_range.mpr hk)
  cases hrun : fRun tm2 k (bridgeStartWithBit bit) with
  | none => simp [hrun,bridgeStartWithBit,m0EvenEightBridgeStart,bridgeInside44]
  | some f => simpa [hrun] using hall


/-- Lift the fixed 44-step prefix to any source tape agreeing on [-13,3].
The cell at -14 and all further-left cells are preserved from the source. -/
theorem bridge_prefix44_at (T : Int → Bool) (h : Int) (bit : Bool)
    (hmatch : ∀ x, bridgeInside44 x = true →
      T (h+x) = decide (x ∈ (bridgeStartWithBit bit).marked)) :
    run tm2 44 ⟨3,h,T⟩ =
      some (frameAt T h bridgeInside44 (bridgeMidWithBit bit)) := by
  simpa [bridgeStartWithBit,m0EvenEightBridgeStart,bridgeMidWithBit] using
    bridgeAt T h bridgeInside44
      (bridgeStartWithBit bit) (bridgeMidWithBit bit) 44 rfl
      (bridge_prefix44 bit) (bridge_heads44_all bit) hmatch

/-- Tape update of the four-step zero exit from state 3 to state 1. -/
def afterZeroExit4 (T : Int → Bool) (h : Int) : Int → Bool :=
  fun x => if x = h-1 || x = h || x = h+1 then true else T x

private theorem lookup30_zero :
    tm2 ((3 : Fin 6), false) = some ⟨false,false,2⟩ := by rfl

private theorem lookup20_zero :
    tm2 ((2 : Fin 6), false) = some ⟨true,true,4⟩ := by rfl

private theorem lookup40_zero :
    tm2 ((4 : Fin 6), false) = some ⟨true,true,0⟩ := by rfl

private theorem lookup00_zero :
    tm2 ((0 : Fin 6), false) = some ⟨true,true,1⟩ := by rfl

/-- Four original-table moves across a 000 boundary enter state 1. -/
private def zeroExitStart : FConfig := ⟨3,0,[]⟩
private def zeroExitEnd : FConfig := ⟨1,2,[1,0,-1]⟩
private def zeroExitInside (x : Int) : Bool := decide (-1 ≤ x ∧ x ≤ 1)

private theorem zeroExit_exact :
    fRun tm2 4 zeroExitStart = some zeroExitEnd := by decide

private theorem zeroExit_heads :
    (List.range 4).all (fun k =>
      match fRun tm2 k zeroExitStart with
      | none => true
      | some f => zeroExitInside f.head) = true := by decide

/-- A four-step physical exit proved by lifting its exact finite source trace.
The input agrees with the finite trace at precisely the three read cells;
all other tape cells remain arbitrary. -/
theorem state3_zero_exit4 (T : Int → Bool) (h : Int)
    (hleft : T (h-1) = false) (h0 : T h = false)
    (hright : T (h+1) = false) :
    run tm2 4 ⟨3,h,T⟩ = some ⟨1,h+2,afterZeroExit4 T h⟩ := by
  have hmatch : ∀ x, zeroExitInside x = true →
      T (h+x) = decide (x ∈ zeroExitStart.marked) := by
    intro x hx
    have hrange : -1 ≤ x ∧ x ≤ 1 := by
      simpa [zeroExitInside] using hx
    have hcases : x = -1 ∨ x = 0 ∨ x = 1 := by omega
    rcases hcases with hm | hz | hp
    · subst x
      have hc : h + (-1 : Int) = h-1 := by omega
      simpa [zeroExitStart,hc] using hleft
    · subst x
      simpa [zeroExitStart] using h0
    · subst x
      simpa [zeroExitStart] using hright
  have hlift := bridgeAt T h zeroExitInside zeroExitStart zeroExitEnd
    4 rfl zeroExit_exact zeroExit_heads hmatch
  have hend :
      frameAt T h zeroExitInside zeroExitEnd =
        (⟨(1:Fin 6),h+2,afterZeroExit4 T h⟩ : Config) := by
    apply config_ext
    · simp [zeroExitEnd]
    · simp [zeroExitEnd]
      omega
    · funext x
      rw [frameAt_tape]
      by_cases hm : x = h-1
      · subst x
        have hc : h-1-h = -1 := by omega
        simp [zeroExitInside,zeroExitEnd,afterZeroExit4,hc]
      by_cases hz : x = h
      · subst x
        have hc : h-h = 0 := by omega
        simp [zeroExitInside,zeroExitEnd,afterZeroExit4,hc]
      by_cases hp : x = h+1
      · subst x
        have hc : h+1-h = 1 := by omega
        simp [zeroExitInside,zeroExitEnd,afterZeroExit4,hc]
      have hout : zeroExitInside (x-h) = false := by
        simp [zeroExitInside]
        omega
      simp [hout,afterZeroExit4,hm,hz,hp]
  simpa [zeroExitStart,hend] using hlift

#print axioms bridge_prefix44
#print axioms bridge_heads44
#print axioms state3_zero_exit4

end BB6Coverage.Agent48M0EvenEightValuationFixedPrefix
