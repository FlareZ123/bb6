import ChampionRootBridge
import Lean

/-!
# State-1 left-hole sweep for the TM63 source machine

A small source-level macro intended for the missing M1-even valuation row.
It shifts a blank one cell left in three original TM2 steps, and iterates
without bounded-tape approximations.
-/

namespace BB6Coverage.Agent48M1EvenValuationSweep

open BB6Coverage
open BB6Coverage.Agent48Champion

private theorem lookup10 :
    tm2 ((1 : Fin 6), false) = some ⟨true,false,2⟩ := by rfl

private theorem lookup21 :
    tm2 ((2 : Fin 6), true) = some ⟨false,false,3⟩ := by rfl

private theorem lookup31 :
    tm2 ((3 : Fin 6), true) = some ⟨true,true,1⟩ := by rfl

/-- Move the unique blank at h one cell left, preserving all other cells. -/
def holeLeft (T : Int → Bool) (h : Int) : Int → Bool :=
  fun x => if x = h then true else if x = h-1 then false else T x

/-- One 3-step state-1 cycle shifts the blank from h to h-1. -/
theorem state1_three_left (T : Int → Bool) (h : Int)
    (h0 : T h = false) (h1 : T (h-1) = true) (h2 : T (h-2) = true) :
    run tm2 3 ⟨1,h,T⟩ = some ⟨1,h-1,holeLeft T h⟩ := by
  have heq1 : h + (-1 : Int) = h-1 := by omega
  have heq2 : h + (-1 : Int) + (-1 : Int) = h-2 := by omega
  have h1' : T (h + (-1 : Int)) = true := by
    simpa [heq1] using h1
  have h2' : T (h + (-1 : Int) + (-1 : Int)) = true := by
    simpa [heq2] using h2
  have hne1' : h + (-1 : Int) ≠ h := by omega
  have hne2' : h + (-1 : Int) + (-1 : Int) ≠ h := by omega
  have hne3' : h + (-1 : Int) + (-1 : Int) ≠ h + (-1 : Int) := by omega
  have hne0 : h ≠ h-2 := by omega
  have hne1 : h-1 ≠ h-2 := by omega
  simp [run, rawStep, readSlot, applyMove, h0, h1', h2',
    hne1', hne2', hne3', lookup10, lookup21, lookup31]
  constructor
  · omega
  · funext x
    by_cases hx0 : x = h
    · simp [hx0, holeLeft, hne0]
    · by_cases hx1 : x = h-1
      · simp [hx0, hx1, holeLeft, hne1]
      · by_cases hx2 : x = h-2
        · simp [hx0, hx1, hx2, holeLeft, h2, hne2', hne3']
        · simp [hx0, hx1, hx2, holeLeft]

/-- The cells immediately left of the moving blank are all one. -/
def state1LeftOnes (T : Int → Bool) (h : Int) (n : Nat) : Prop :=
  ∀ i : Nat, i < n → T (h-1-(i:Int)) = true

theorem state1LeftOnes_tail (T : Int → Bool) (h : Int) (n : Nat)
    (hon : state1LeftOnes T h (n+1)) :
    state1LeftOnes (holeLeft T h) (h-1) n := by
  intro i hi
  have hold := hon (i+1) (by omega)
  have htarget : (h-1)-1-(i:Int) = h-1-((i+1:Int)) := by omega
  have hne0 : (h-1)-1-(i:Int) ≠ h := by omega
  have hne1 : (h-1)-1-(i:Int) ≠ h-1 := by omega
  unfold holeLeft
  rw [if_neg hne0, if_neg hne1, htarget]
  exact hold

def state1SweptLeft : Nat → (Int → Bool) → Int → (Int → Bool)
  | 0, T, _ => T
  | n+1, T, h => state1SweptLeft n (holeLeft T h) (h-1)

/-- Exactly 3*n original TM2 transitions shift a blank left over n cells.
The premise includes the extra one needed by the final 3-step cycle. -/
theorem counted_left_sweep_from1 (n : Nat) (T : Int → Bool) (h : Int)
    (h0 : T h = false)
    (hon : state1LeftOnes T h (n+1)) :
    run tm2 (3*n) ⟨1,h,T⟩ =
      some ⟨1,h-(n:Int),state1SweptLeft n T h⟩ := by
  induction n generalizing T h with
  | zero =>
      simp [run, state1SweptLeft]
  | succ n ih =>
      have h1 : T (h-1) = true := by
        have hh := hon 0 (by omega)
        have heq : h-1-(0:Int) = h-1 := by omega
        simpa [heq] using hh
      have h2 : T (h-2) = true := by
        have hh := hon 1 (by omega)
        have heq : h-1-(1:Int) = h-2 := by omega
        simpa [heq] using hh
      have hstep := state1_three_left T h h0 h1 h2
      have hon' : state1LeftOnes (holeLeft T h) (h-1) (n+1) :=
        state1LeftOnes_tail T h (n+1) hon
      have hne : h-1 ≠ h := by omega
      have h0' : holeLeft T h (h-1) = false := by
        simp [holeLeft, hne]
      have htail := ih (holeLeft T h) (h-1) h0' hon'
      have hnum : 3*(n+1) = 3 + 3*n := by omega
      rw [hnum, run_append, hstep]
      simp only [Option.bind_some]
      rw [htail]
      have hhead : h-1-(n:Int) = h-((n+1:Int)) := by omega
      simpa [state1SweptLeft, hhead]

theorem counted_four_left_hole (T : Int → Bool) (h : Int)
    (h0 : T h = false)
    (hon : state1LeftOnes T h 5) :
    run tm2 12 ⟨1,h,T⟩ =
      some ⟨1,h-4,state1SweptLeft 4 T h⟩ := by
  simpa using counted_left_sweep_from1 4 T h h0 hon

#print axioms state1_three_left
#print axioms counted_left_sweep_from1
#print axioms counted_four_left_hole

end BB6Coverage.Agent48M1EvenValuationSweep
