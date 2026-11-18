import ChampionRootBridge
import Lean

/-!
# State-5 right-hole sweep for the TM63 source machine

The state-1 sweep in Agent48M1EvenValuationSweep moves a blank left over
consecutive ones. This is the matching rightward macro used after that
left sweep has written a consecutive block of ones.
-/

namespace BB6Coverage.Agent24M1EvenValuationBridge

open BB6Coverage
open BB6Coverage.Agent48Champion

private theorem lookup53 :
    tm2 ((5 : Fin 6), true) = some ⟨false,true,3⟩ := by rfl

private theorem lookup31Right :
    tm2 ((3 : Fin 6), true) = some ⟨true,true,1⟩ := by rfl

private theorem lookup15 :
    tm2 ((1 : Fin 6), true) = some ⟨false,true,5⟩ := by rfl

/-- One 3-step state-5 cycle consumes three ones and moves right by three. -/
def holeRight (T : Int → Bool) (h : Int) : Int → Bool :=
  fun x => if x = h then false else if x = h+2 then false else T x

theorem state5_three_right (T : Int → Bool) (h : Int)
    (h0 : T h = true) (h1 : T (h+1) = true) (h2 : T (h+2) = true) :
    run tm2 3 ⟨5,h,T⟩ = some ⟨5,h+3,holeRight T h⟩ := by
  have heq2 : h+1+1 = h+2 := by omega
  have h2' : T (h+1+1) = true := by
    simpa [heq2] using h2
  have hne1 : h+1 ≠ h := by omega
  have hne2' : h+1+1 ≠ h := by omega
  have hne3' : h+1+1 ≠ h+1 := by omega
  have hne0 : h ≠ h+2 := by omega
  have hne12 : h+1 ≠ h+2 := by omega
  simp [run, rawStep, readSlot, applyMove, h0, h1, h2',
    hne1, hne2', hne3', lookup53, lookup31Right, lookup15]
  constructor
  · omega
  · funext x
    by_cases hx0 : x = h
    · subst x
      have hne1 : h ≠ h+1 := by omega
      have hne2 : h ≠ h+2 := by omega
      simp [holeRight, heq2, hne1, hne2]
    · by_cases hx1 : x = h+1
      · subst x
        have hne0 : h+1 ≠ h := by omega
        have hne2 : h+1 ≠ h+2 := by omega
        simp [holeRight, heq2, hne0, hne2, h1]
      · by_cases hx2 : x = h+2
        · subst x
          have hne0 : h+2 ≠ h := by omega
          have hne1 : h+2 ≠ h+1 := by omega
          simp [holeRight, heq2, hne0, hne1]
        · simp [holeRight, heq2, hx0, hx1, hx2]

/-- The cells at and immediately right of the moving state-5 head are one. -/
def state5RightOnes (T : Int → Bool) (h : Int) (n : Nat) : Prop :=
  ∀ i : Nat, i < n → T (h+(i:Int)) = true

theorem state5RightOnes_tail (T : Int → Bool) (h : Int) (n : Nat)
    (hon : state5RightOnes T h (n+3)) :
    state5RightOnes (holeRight T h) (h+3) n := by
  intro i hi
  have hold := hon (i+3) (by omega)
  have htarget : (h+3)+(i:Int) = h+((i+3:Int)) := by omega
  have hne0 : (h+3)+(i:Int) ≠ h := by omega
  have hne1 : (h+3)+(i:Int) ≠ h+2 := by omega
  unfold holeRight
  rw [if_neg hne0, if_neg hne1, htarget]
  exact hold

def state5SweptRight : Nat → (Int → Bool) → Int → (Int → Bool)
  | 0, T, _ => T
  | n+1, T, h => state5SweptRight n (holeRight T h) (h+3)

/-- Exactly 3*n original TM2 transitions sweep state 5 right over 3*n ones. -/
theorem counted_right_sweep_from5 (n : Nat) (T : Int → Bool) (h : Int)
    (hon : state5RightOnes T h (3*n)) :
    run tm2 (3*n) ⟨5,h,T⟩ =
      some ⟨5,h+(3*n:Int),state5SweptRight n T h⟩ := by
  induction n generalizing T h with
  | zero =>
      simp [run, state5SweptRight]
  | succ n ih =>
      have h0 : T h = true := by
        simpa using hon 0 (by omega)
      have h1 : T (h+1) = true := by
        have := hon 1 (by omega)
        simpa using this
      have h2 : T (h+2) = true := by
        have := hon 2 (by omega)
        simpa using this
      have hstep := state5_three_right T h h0 h1 h2
      have hon' : state5RightOnes (holeRight T h) (h+3) (3*n) := by
        apply state5RightOnes_tail T h (3*n)
        simpa [Nat.mul_succ, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using hon
      have htail := ih (holeRight T h) (h+3) hon'
      have hnum : 3*(n+1) = 3 + 3*n := by omega
      rw [hnum, run_append, hstep]
      simp only [Option.bind_some]
      rw [htail]
      have hhead : h+3+(3*n:Int) = h+((3*(n+1)):Int) := by omega
      simpa [state5SweptRight, hhead]

theorem counted_three_right (T : Int → Bool) (h : Int)
    (hon : state5RightOnes T h 3) :
    run tm2 3 ⟨5,h,T⟩ =
      some ⟨5,h+3,holeRight T h⟩ := by
  have h0 : T h = true := by simpa using hon 0 (by omega)
  have h1 : T (h+1) = true := hon 1 (by omega)
  have h2 : T (h+2) = true := hon 2 (by omega)
  exact state5_three_right T h h0 h1 h2


/-- The rightward sweep never changes cells at or beyond its final head. -/
theorem state5SweptRight_preserves_far_right (n : Nat) (T : Int → Bool)
    (h x : Int) (hx : h+(3*n:Int) ≤ x) :
    state5SweptRight n T h x = T x := by
  induction n generalizing T h with
  | zero =>
      simp [state5SweptRight]
  | succ n ih =>
      have hx' : (h+3)+(3*n:Int) ≤ x := by omega
      have hpres := ih (holeRight T h) (h+3) hx'
      have hne0 : x ≠ h := by omega
      have hne2 : x ≠ h+2 := by omega
      simpa [state5SweptRight, holeRight, hne0, hne2] using hpres

#print axioms state5_three_right
#print axioms counted_right_sweep_from5
#print axioms counted_three_right
#print axioms state5SweptRight_preserves_far_right

end BB6Coverage.Agent24M1EvenValuationBridge
