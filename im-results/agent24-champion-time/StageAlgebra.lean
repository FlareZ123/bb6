import CostRecurrence
import Lean.Elab.Tactic.Omega

namespace BB6ChampionArithmetic

/-- Source one-macro right counter, iterated by primitive recursive composition. -/
def iterRight : Nat → Nat → Nat
  | 0, b => b
  | n+1, b => iterRight n (nextRight b)

/-- Sum of the n successive right counter values encountered during consumption. -/
def sumRight : Nat → Nat → Nat
  | 0, _ => 0
  | n+1, b => b + sumRight n (nextRight b)

/-- The 2,2,1 cyclic increments in the three source Rst2/Rst1/Rst0 macros. -/
def offsetCount : Nat → Nat → Nat
  | 0, _ => 0
  | n+1, m => (if m%3=0 then 1 else 2) + offsetCount n (nextMarker m)

theorem sectionResult_right (n m a b : Nat) :
    (sectionResult n m a b).right = iterRight n b := by
  induction n generalizing m a b with
  | zero => rfl
  | succ n ih =>
    simp only [sectionResult, iterRight]
    exact ih (nextMarker m) (nextExponent m a b) (nextRight b)

theorem sectionResult_exponent (n m a b : Nat) :
    (sectionResult n m a b).exponent = a+sumRight n b+offsetCount n m := by
  induction n generalizing m a b with
  | zero => simp [sectionResult, sumRight, offsetCount]
  | succ n ih =>
    simp only [sectionResult, sumRight, offsetCount]
    rw [ih]
    unfold nextExponent
    split <;> omega

theorem iterRight_comm (n b : Nat) :
    iterRight n (nextRight b) = nextRight (iterRight n b) := by
  induction n generalizing b with
  | zero => rfl
  | succ n ih =>
    simp only [iterRight]
    exact ih (nextRight b)

theorem iterRight_succ (n b : Nat) :
    iterRight (n+1) b=nextRight (iterRight n b) := by
  change iterRight n (nextRight b)=nextRight (iterRight n b)
  exact iterRight_comm n b

theorem sumRight_succ (n b : Nat) :
    sumRight (n+1) b = sumRight n b + iterRight n b := by
  induction n generalizing b with
  | zero => simp [sumRight, iterRight]
  | succ n ih =>
    change b+sumRight (n+1) (nextRight b) =
      b+sumRight n (nextRight b)+iterRight n (nextRight b)
    rw [ih]
    omega

/-- Original BusyCoq tower equations, with st2(0,b)=b. -/
theorem tower_eq_iterRight (n b : Nat) : tower n b=iterRight n b := by
  induction n with
  | zero => rfl
  | succ n ih =>
    change nextRight (tower n b)=iterRight (n+1) b
    rw [iterRight_succ, ih]

theorem source_sumTower_bridge (n b : Nat) :
    sumTower n b = b + sumRight n (nextRight b) := by
  induction n with
  | zero => simp [sumTower, sumRight]
  | succ n ih =>
    simp only [sumTower]
    rw [ih, sumRight_succ, tower_eq_iterRight]
    rw [iterRight_succ, ← iterRight_comm]
    omega

/-- Exact n=7 stage exponent as in source Rsts1, without computing the tower. -/
theorem authentic_first_stage_exponent :
    (sectionResult 7 2 6 63).exponent = sumTower 7 6+12 := by
  have h := sectionResult_exponent 7 2 6 63
  have h63 : nextRight 6 = 63 := by decide
  have hs := source_sumTower_bridge 7 6
  rw [h63] at hs
  have hc : offsetCount 7 2 = 12 := by decide
  rw [hc] at h
  omega

#print axioms sectionResult_right
#print axioms sectionResult_exponent
#print axioms source_sumTower_bridge
#print axioms authentic_first_stage_exponent

end BB6ChampionArithmetic
