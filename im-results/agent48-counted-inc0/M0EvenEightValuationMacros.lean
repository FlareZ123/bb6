import CountedSweep
import Lean.Elab.Tactic.Omega

namespace BB6Coverage.Agent48M0EvenEightValuation

open BB6Coverage.Agent48Champion

/-- The state-1 rightward scan writes a d1 block 111 as 001. -/
def afterRight1 (T : Int → Bool) (h : Int) : Int → Bool :=
  fun x => if x = h || x = h+1 then false else if x = h+2 then true else T x

private theorem lookup11_from1 :
    tm2 ((1 : Fin 6), true) = some ⟨false,true,5⟩ := by rfl

private theorem lookup51_from1 :
    tm2 ((5 : Fin 6), true) = some ⟨false,true,3⟩ := by rfl

private theorem lookup31_from1 :
    tm2 ((3 : Fin 6), true) = some ⟨true,true,1⟩ := by rfl

/-- Three original-table moves from state 1 scan one d1 block to 001. -/
theorem counted_three_right_from1 (T : Int → Bool) (h : Int)
    (h0 : T h = true) (h1 : T (h+1) = true) (h2 : T (h+2) = true) :
    run tm2 3 ⟨1,h,T⟩ = some ⟨1,h+3, afterRight1 T h⟩ := by
  have neq1 : h+1 ≠ h := by omega
  have neq2 : h+2 ≠ h := by omega
  have neq3 : h+2 ≠ h+1 := by omega
  have hh : h+1+1=h+2 := by omega
  have neh1 : h≠h+1 := by omega
  have neh2 : h≠h+2 := by omega
  simp [run, rawStep, readSlot, applyMove, h0, h1, h2, hh,
    lookup11_from1, lookup51_from1, lookup31_from1, neq1, neq2, neq3]
  constructor
  · omega
  · funext x
    by_cases hx0 : x=h <;> by_cases hx1 : x=h+1 <;> by_cases hx2 : x=h+2 <;>
      simp [afterRight1,hx0,hx1,hx2,h0,h1,h2,neh1,neh2]

/-- Repeated state-1 right scan of three-cell one-blocks. -/
def sweptRight1 : Nat → (Int → Bool) → Int → (Int → Bool)
  | 0, T, _ => T
  | n+1, T, h => sweptRight1 n (afterRight1 T h) (h+3)

private theorem rightOnes_tail1 (T : Int → Bool) (h : Int) (n : Nat)
    (hon : rightOnes T h (n+1)) :
    rightOnes (afterRight1 T h) (h+3) n := by
  intro i hi
  obtain ⟨a,b,c⟩ := hon (i+1) (by omega)
  have e0 : h+3+3*(i:Int) = h+3*((i+1:Int)) := by omega
  have e1 : h+3+3*(i:Int)+1 = h+3*((i+1:Int))+1 := by omega
  have e2 : h+3+3*(i:Int)+2 = h+3*((i+1:Int))+2 := by omega
  have ne00 : h+3+3*(i:Int) ≠ h := by omega
  have ne01 : h+3+3*(i:Int) ≠ h+1 := by omega
  have ne02 : h+3+3*(i:Int) ≠ h+2 := by omega
  have ne10 : h+3+3*(i:Int)+1 ≠ h := by omega
  have ne11 : h+3+3*(i:Int)+1 ≠ h+1 := by omega
  have ne12 : h+3+3*(i:Int)+1 ≠ h+2 := by omega
  have ne20 : h+3+3*(i:Int)+2 ≠ h := by omega
  have ne21 : h+3+3*(i:Int)+2 ≠ h+1 := by omega
  have ne22 : h+3+3*(i:Int)+2 ≠ h+2 := by omega
  constructor
  · simpa [afterRight1,e0,ne00,ne01,ne02] using a
  constructor
  · simpa [afterRight1,e1,ne10,ne11,ne12] using b
  · simpa [afterRight1,e2,ne20,ne21,ne22] using c

/-- Exactly 3*n original-table moves scan n consecutive d1 blocks from state 1. -/
theorem counted_right_sweep_from1 (n : Nat) (T : Int → Bool) (h : Int)
    (hon : rightOnes T h n) :
    run tm2 (3*n) ⟨1,h,T⟩ =
      some ⟨1,h+3*(n:Int),sweptRight1 n T h⟩ := by
  induction n generalizing T h with
  | zero => simp [run,sweptRight1]
  | succ n ih =>
    obtain ⟨h0,h1,h2⟩ := hon 0 (by omega)
    have hstep := counted_three_right_from1 T h h0 h1 h2
    have hon' := rightOnes_tail1 T h n hon
    have htail := ih (afterRight1 T h) (h+3) hon'
    have hnum : 3*(n+1) = 3+3*n := by omega
    rw [hnum,run_append,hstep]
    simp only [Option.bind_some]
    rw [htail]
    have hhead : h+3+3*(n:Int) = h+3*((n+1:Int)) := by omega
    simpa [sweptRight1,hhead]

/-- Tape update at the final 101 boundary entering state 4. -/
def after101 (T : Int → Bool) (h : Int) : Int → Bool :=
  fun x => if x=h then false else if x=h+1 || x=h+2 then true else T x

private theorem lookup50_from1 :
    tm2 ((5 : Fin 6), false) = some ⟨true,true,4⟩ := by rfl

private theorem lookup41_from1 :
    tm2 ((4 : Fin 6), true) = some ⟨true,true,4⟩ := by rfl

/-- Three original-table moves on 101 enter state 4 at the right boundary. -/
theorem state1_101_boundary (T : Int → Bool) (h : Int)
    (h0 : T h = true) (h1 : T (h+1) = false) (h2 : T (h+2) = true) :
    run tm2 3 ⟨1,h,T⟩ = some ⟨4,h+3,after101 T h⟩ := by
  have neq1 : h+1 ≠ h := by omega
  have neq2 : h+2 ≠ h := by omega
  have neq3 : h+2 ≠ h+1 := by omega
  have hh : h+1+1=h+2 := by omega
  have neh1 : h≠h+1 := by omega
  have neh2 : h≠h+2 := by omega
  simp [run, rawStep, readSlot, applyMove, h0, h1, h2, hh,
    lookup11_from1, lookup50_from1, lookup41_from1, neq1, neq2, neq3]
  constructor
  · omega
  · funext x
    by_cases hx0 : x=h <;> by_cases hx1 : x=h+1 <;> by_cases hx2 : x=h+2 <;>
      simp [after101,hx0,hx1,hx2,h0,h1,h2,neh1,neh2]

#print axioms counted_three_right_from1
#print axioms counted_right_sweep_from1
#print axioms state1_101_boundary

end BB6Coverage.Agent48M0EvenEightValuation
