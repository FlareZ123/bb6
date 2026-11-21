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
  exact (List.append_assoc d1 d0 _).symm

/-- The finite window read by the second-checkpoint bridge. -/
def secondCyclePrefix34Inside (x : Int) : Bool :=
  decide (-7 ≤ x ∧ x ≤ 3)

/-- Input bits on offsets -7..3 are 0,0,1,1,1,1,1,0,0,0,0. -/
def secondCyclePrefix34Start : FConfig :=
  ⟨4, 0, [-5,-4,-3,-2,-1]⟩

/-- The 34-step bridge returns to state 4 at head +4. -/
def secondCyclePrefix34End : FConfig :=
  ⟨4, 4, [3,1,-2,-5,-6,-7]⟩

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
  · subst x
    have heq : h+(-7:Int)=h-7 := by omega
    rw [heq]
    simpa [secondCyclePrefix34Start] using h7
  · subst x
    have heq : h+(-6:Int)=h-6 := by omega
    rw [heq]
    simpa [secondCyclePrefix34Start] using h6
  · subst x
    have heq : h+(-5:Int)=h-5 := by omega
    rw [heq]
    simpa [secondCyclePrefix34Start] using h5
  · subst x
    have heq : h+(-4:Int)=h-4 := by omega
    rw [heq]
    simpa [secondCyclePrefix34Start] using h4
  · subst x
    have heq : h+(-3:Int)=h-3 := by omega
    rw [heq]
    simpa [secondCyclePrefix34Start] using h3
  · subst x
    have heq : h+(-2:Int)=h-2 := by omega
    rw [heq]
    simpa [secondCyclePrefix34Start] using h2
  · subst x
    have heq : h+(-1:Int)=h-1 := by omega
    rw [heq]
    simpa [secondCyclePrefix34Start] using h1
  · subst x
    simpa [secondCyclePrefix34Start] using h0
  · subst x
    simpa [secondCyclePrefix34Start] using hp1
  · subst x
    simpa [secondCyclePrefix34Start] using hp2
  · subst x
    simpa [secondCyclePrefix34Start] using hp3

/-- A generic two-sided tape with nearest-first left and right streams. -/
def q4TapeFromSides (left right : List Bool) (h x : Int) : Bool :=
  if x ≤ h then
    sideBit left (Int.toNat (h-x))
  else
    sideBit right (Int.toNat (x-h-1))

/-- The q4 checkpoint-2 side streams force the exact 34-step input window
whenever the left stream begins 011,d1,d0 and the right stream begins 000. -/
theorem secondCyclePrefix34_input_from_sides
    (tailL tailR : List Bool) (h : Int) :
    let T := q4TapeFromSides
      ([false,true,true] ++ d1 ++ d0 ++ tailL)
      ([false,false,false] ++ tailR) h
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
    T (h+3) = false := by
  have le7 : h-7 ≤ h := by omega
  have le6 : h-6 ≤ h := by omega
  have le5 : h-5 ≤ h := by omega
  have le4 : h-4 ≤ h := by omega
  have le3 : h-3 ≤ h := by omega
  have le2 : h-2 ≤ h := by omega
  have le1 : h-1 ≤ h := by omega
  have gt1 : h < h+1 := by omega
  have gt2 : h < h+2 := by omega
  have gt3 : h < h+3 := by omega
  have nle1 : ¬ h+1 ≤ h := by omega
  have nle2 : ¬ h+2 ≤ h := by omega
  have nle3 : ¬ h+3 ≤ h := by omega
  have l7 : h-(h-7) = (7:Int) := by omega
  have l6 : h-(h-6) = (6:Int) := by omega
  have l5 : h-(h-5) = (5:Int) := by omega
  have l4 : h-(h-4) = (4:Int) := by omega
  have l3 : h-(h-3) = (3:Int) := by omega
  have l2 : h-(h-2) = (2:Int) := by omega
  have l1 : h-(h-1) = (1:Int) := by omega
  have l0 : h-h = (0:Int) := by omega
  have r1 : h+1-h-1 = (0:Int) := by omega
  have r2 : h+2-h-1 = (1:Int) := by omega
  have r3 : h+3-h-1 = (2:Int) := by omega
  simp [q4TapeFromSides,sideBit,d1,d0,l7,l6,l5,l4,l3,l2,l1,l0,r1,r2,r3,
    le7,le6,le5,le4,le3,le2,le1,nle1,nle2,nle3]

/-- Specialize the preceding window lemma to a BinDec value whose first
two source digits are d1,d0. -/
theorem secondCyclePrefix34_input_from_binDec
    (w r : Nat) (hr : r < 2^w) (tailR : List Bool) (h : Int) :
    let T := q4TapeFromSides
      ([false,true,true] ++ binDec (w+2) (2*(2*r+1)))
      ([false,false,false] ++ tailR) h
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
    T (h+3) = false := by
  simpa [binDec_twoDigit_d1d0 w r hr] using
    secondCyclePrefix34_input_from_sides (binDec w r) tailR h

/-- For the q4 checkpoint-2 marker value
M=2^A*(2^(L+2)-1), A≥2, the first two BinDec blocks of M-2 are
exactly d1,d0. -/
theorem q4Checkpoint2_binDec_prefix (A L : Nat) (hA : 2≤A) :
    binDec (A+L+2) (2^A*(2^(L+2)-1)-2) =
      d1 ++ d0 ++
        binDec (A+L) (2^(A-2)*(2^(L+2)-1)-1) := by
  let r : Nat := 2^(A-2)*(2^(L+2)-1)-1
  have hAeq : A = (A-2)+2 := by omega
  have hpowA : 2^A = 4*2^(A-2) := by
    calc
      2^A = 2^((A-2)+2) := by congr 1 <;> omega
      _ = 2^(A-2)*2^2 := by rw [Nat.pow_add]
      _ = 4*2^(A-2) := by
        rw [show (2:Nat)^2=4 by decide, Nat.mul_comm]
  have hval :
      2^A*(2^(L+2)-1)-2 = 2*(2*r+1) := by
    dsimp [r]
    rw [hpowA]
    have htwo : 2 ≤ 2^(L+2) := by
      have h := Nat.pow_le_pow_right (by decide : 0<2)
        (show 1≤L+2 by omega)
      simpa using h
    have hCpos : 0 < 2^(L+2)-1 := by omega
    have hprodpos : 0 < 2^(A-2)*(2^(L+2)-1) :=
      Nat.mul_pos (Nat.pow_pos (by decide)) hCpos
    have hmul : 4*2^(A-2)*(2^(L+2)-1) =
        4*(2^(A-2)*(2^(L+2)-1)) := by ac_rfl
    rw [hmul]
    omega
  have hpowAL :
      2^(A+L) = 2^(A-2)*2^(L+2) := by
    rw [show A+L = (A-2)+(L+2) by omega, Nat.pow_add]
  have hltC : 2^(L+2)-1 < 2^(L+2) := by
    have hpos : 0 < 2^(L+2) := Nat.pow_pos (by decide)
    omega
  have hprod :
      2^(A-2)*(2^(L+2)-1) < 2^(A+L) := by
    rw [hpowAL]
    exact Nat.mul_lt_mul_of_pos_left hltC (Nat.pow_pos (by decide : 0<2))
  have hr : r < 2^(A+L) := by
    dsimp [r]
    omega
  rw [hval]
  simpa [r] using binDec_twoDigit_d1d0 (A+L) r hr

#print axioms binDec_twoDigit_d1d0
#print axioms q4Checkpoint2_binDec_prefix
#print axioms secondCyclePrefix34_input_from_sides
#print axioms secondCyclePrefix34_input_from_binDec

#print axioms secondCyclePrefix34_exact
#print axioms secondCyclePrefix34_heads
#print axioms secondCyclePrefix34_at

end BB6Coverage.Agent48PositiveZSecondCycle
