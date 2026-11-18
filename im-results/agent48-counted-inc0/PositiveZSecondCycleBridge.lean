import CountedRst1Prime
import Lean.Elab.Tactic.Omega

/-!
# Later q4 checkpoint: 34-step finite prefix bridge

At the second q4 checkpoint, the left-facing marker window is different
from the first checkpoint. When the first two BinDec digits are d1,d0,
the eleven-cell window at offsets [-7,3] is 00111110000. The exact
34-step trace below returns to state 4 at head +4, ready to scan the
first right unary run.

This is an intermediate source draft. The finite trace and head-window
certificate are decidable, but this module has NOT passed local Lean
4.36.0-rc2 compilation.
-/

namespace BB6Coverage.Agent48PositiveZSecondCycle

open BB6Coverage
open BB6Coverage.Agent48Champion
open BB6Coverage.Agent8Rst1Prime
open BB6Coverage.Agent8S1Encoder

/-- If the binary value is even with odd half, its first two BinDec blocks
are d1 then d0. This is the exact marker pattern at q4 checkpoint 2 when
M-2 has the form 2*(2*r+1). -/
theorem binDec_twoDigit_d1d0 (w r : Nat) (hr : r < 2^w) :
    binDec (w+2) (2*(2*r+1)) = d1 ++ d0 ++ binDec w r := by
  have hpow : 2^(w+1) = 2*2^w := by
    rw [Nat.pow_succ]
    ac_rfl
  have hq : 2*r+1 < 2^(w+1) := by
    rw [hpow]
    omega
  rw [binDec_even (w+1) (2*r+1) hq, binDec_odd w r hr]

/-- The finite window read by the second-checkpoint bridge. -/
def secondCyclePrefix34Inside (x : Int) : Bool :=
  decide (-7 ≤ x ∧ x ≤ 3)

/-- Input bits on offsets -7..3 are 0,0,1,1,1,1,1,0,0,0,0. -/
def secondCyclePrefix34Start : FConfig :=
  ⟨4, 0, [-5,-4,-3,-2,-1]⟩

/-- The 34-step bridge returns to state 4 at head +4. -/
def secondCyclePrefix34End : FConfig :=
  ⟨4, 4, [-7,-6,-5,-2,1,3]⟩

theorem secondCyclePrefix34_exact :
    fRun tm2 34 secondCyclePrefix34Start =
      some secondCyclePrefix34End := by
  decide

theorem secondCyclePrefix34_heads :
    (List.range 34).all (fun k =>
      match fRun tm2 k secondCyclePrefix34Start with
      | none => true
      | some f => secondCyclePrefix34Inside f.head) = true := by
  decide

/-- Arbitrary-tape lift of the second-checkpoint 34-step bridge. -/
theorem secondCyclePrefix34_at (T : Int → Bool) (h : Int)
    (hinput :
      T (h-7) = false ∧
      T (h-6) = false ∧
      T (h-5) = true ∧
      T (h-4) = true ∧
      T (h-3) = true ∧
      T (h-2) = true ∧
      T (h-1) = true ∧
      T h = false ∧
      T (h+1) = false ∧
      T (h+2) = false ∧
      T (h+3) = false) :
    run tm2 34 ⟨4,h,T⟩ =
      some (frameAt T h secondCyclePrefix34Inside secondCyclePrefix34End) := by
  rcases hinput with
    ⟨h7,h6,h5,h4,h3,h2,h1,h0,hp1,hp2,hp3⟩
  apply bridgeAt T h secondCyclePrefix34Inside
    secondCyclePrefix34Start secondCyclePrefix34End 34 rfl
    secondCyclePrefix34_exact secondCyclePrefix34_heads
  intro x hx
  have hrange : -7 ≤ x ∧ x ≤ 3 := by
    simpa [secondCyclePrefix34Inside] using hx
  have hcases :
      x=(-7) ∨ x=(-6) ∨ x=(-5) ∨ x=(-4) ∨ x=(-3) ∨
      x=(-2) ∨ x=(-1) ∨ x=0 ∨ x=1 ∨ x=2 ∨ x=3 := by omega
  rcases hcases with
    hx7|hx6|hx5|hx4|hx3|hx2|hx1|hx0|hxp1|hxp2|hxp3
  · have heq : h+(-7:Int)=h-7 := by omega
    rw [heq]
    simpa [secondCyclePrefix34Start] using h7
  · have heq : h+(-6:Int)=h-6 := by omega
    rw [heq]
    simpa [secondCyclePrefix34Start] using h6
  · have heq : h+(-5:Int)=h-5 := by omega
    rw [heq]
    simpa [secondCyclePrefix34Start] using h5
  · have heq : h+(-4:Int)=h-4 := by omega
    rw [heq]
    simpa [secondCyclePrefix34Start] using h4
  · have heq : h+(-3:Int)=h-3 := by omega
    rw [heq]
    simpa [secondCyclePrefix34Start] using h3
  · have heq : h+(-2:Int)=h-2 := by omega
    rw [heq]
    simpa [secondCyclePrefix34Start] using h2
  · have heq : h+(-1:Int)=h-1 := by omega
    rw [heq]
    simpa [secondCyclePrefix34Start] using h1
  · simpa [secondCyclePrefix34Start] using h0
  · simpa [secondCyclePrefix34Start] using hp1
  · simpa [secondCyclePrefix34Start] using hp2
  · simpa [secondCyclePrefix34Start] using hp3

#print axioms binDec_twoDigit_d1d0

#print axioms secondCyclePrefix34_exact
#print axioms secondCyclePrefix34_heads
#print axioms secondCyclePrefix34_at

end BB6Coverage.Agent48PositiveZSecondCycle
