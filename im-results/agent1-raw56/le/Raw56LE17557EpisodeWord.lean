import Lean.Elab.Tactic.Omega

namespace BB6.Agent1Raw56.LE17557EpisodeWord

def substLetter : Bool → List Bool
  | false => [false, true, false]
  | true  => [true, true, false]

def subst (w : List Bool) : List Bool := w.flatMap substLetter

def episode : Nat → List Bool
  | 0 => [true, false]
  | r + 1 => subst (episode r)

def countA (w : List Bool) : Nat := w.count false
def countB (w : List Bool) : Nat := w.count true

@[simp] theorem subst_nil : subst [] = [] := rfl
@[simp] theorem subst_cons (b : Bool) (w : List Bool) :
    subst (b :: w) = substLetter b ++ subst w := rfl

@[simp] theorem substLetter_length (b : Bool) : (substLetter b).length = 3 := by
  cases b <;> decide

theorem subst_length (w : List Bool) : (subst w).length = 3 * w.length := by
  induction w with
  | nil => rfl
  | cons b w ih =>
      rw [subst_cons, List.length_append, substLetter_length, ih]
      simp
      omega

@[simp] theorem countA_letter (b : Bool) :
    countA (substLetter b) = if b then 1 else 2 := by
  cases b <;> decide

@[simp] theorem countB_letter (b : Bool) :
    countB (substLetter b) = if b then 2 else 1 := by
  cases b <;> decide

theorem countA_subst (w : List Bool) :
    countA (subst w) = 2 * countA w + countB w := by
  induction w with
  | nil => rfl
  | cons b w ih =>
      unfold countA countB at ih ⊢
      rw [subst_cons, List.count_append]
      cases b <;> simp [substLetter, ih] <;> omega

theorem countB_subst (w : List Bool) :
    countB (subst w) = countA w + 2 * countB w := by
  induction w with
  | nil => rfl
  | cons b w ih =>
      unfold countA countB at ih ⊢
      rw [subst_cons, List.count_append]
      cases b <;> simp [substLetter, ih] <;> omega

@[simp] theorem episode_succ (r : Nat) : episode (r + 1) = subst (episode r) := rfl

theorem episode_length (r : Nat) : (episode r).length = 2 * 3^r := by
  induction r with
  | zero => decide
  | succ r ih =>
      rw [episode_succ, subst_length, ih]
      simp [Nat.pow_succ]
      omega

theorem episode_balanced (r : Nat) :
    countA (episode r) = 3^r ∧ countB (episode r) = 3^r := by
  induction r with
  | zero => decide
  | succ r ih =>
      rcases ih with ⟨ha, hb⟩
      constructor
      · rw [episode_succ, countA_subst, ha, hb]
        simp [Nat.pow_succ]
        omega
      · rw [episode_succ, countB_subst, ha, hb]
        simp [Nat.pow_succ]
        omega

theorem substLetter_last (b : Bool) : (substLetter b).getLast? = some false := by
  cases b <;> decide

theorem substLetter_middle (b : Bool) : (substLetter b)[1]! = true := by
  cases b <;> decide

#print axioms subst_length
#print axioms countA_subst
#print axioms countB_subst
#print axioms episode_length
#print axioms episode_balanced

end BB6.Agent1Raw56.LE17557EpisodeWord
