import Phase6
import Lean.Elab.Tactic.Omega

namespace BB6.Agent2F321Phase12
open BB6.Agent31F321Density
open BB6.Agent2F321Phase6

/-- A small mod-12 refinement of Phase6. Every non-seed authentic state lies
    in one of these three structural classes. -/
def Phase12 (a d : Nat) : Prop :=
  (a % 2 = 1 ∧ d % 12 = 5) ∨
  (a % 4 = 0 ∧ d % 6 = 1) ∨
  (a % 4 = 2 ∧ (d % 6 = 1 ∨ d % 6 = 2))

theorem phase12_preserved {a d A D : Nat}
    (hp : Phase12 a d) (hm : CounterMove a d A D) : Phase12 A D := by
  unfold Phase12 at hp ⊢
  rcases hp with hodd | h40 | h42
  · cases hm with
    | high d hg =>
        by_cases hz : (a-d-2) % 4 = 0
        · right; left; omega
        · right; right; omega
    | equal => omega
    | far d h1 h2 =>
        right; right
        omega
    | middleEven d h1 h2 hpar =>
        right; right
        omega
    | middleOdd d h1 h2 hpar => omega
  · cases hm with
    | high d hg =>
        left
        omega
    | equal => omega
    | far d h1 h2 =>
        right; right
        omega
    | middleEven d h1 h2 hpar => omega
    | middleOdd d h1 h2 hpar =>
        right; right
        omega
  · rcases h42.2 with hd1 | hd2
    · cases hm with
      | high d hg =>
          left
          omega
      | equal => omega
      | far d h1 h2 =>
          right; right
          omega
      | middleEven d h1 h2 hpar => omega
      | middleOdd d h1 h2 hpar =>
          right; right
          omega
    · cases hm with
      | high d hg =>
          by_cases hz : (a-d-2) % 4 = 0
          · right; left; omega
          · right; right; omega
      | equal =>
          right; left
          omega
      | far d h1 h2 =>
          right; right
          omega
      | middleEven d h1 h2 hpar =>
          right; right
          omega
      | middleOdd d h1 h2 hpar => omega

theorem seed_step_phase12 {A D : Nat} (hm : CounterMove 1 1 A D) : Phase12 A D := by
  unfold Phase12
  cases hm with
  | high d hg => omega
  | equal =>
      right; right
      omega
  | far d h1 h2 => omega
  | middleEven d h1 h2 hp => omega
  | middleOdd d h1 h2 hp => omega

theorem root_phase12 {n a d : Nat} (hr : Reach n a d) :
    (n = 0 ∧ a = 1 ∧ d = 1) ∨ Phase12 a d := by
  induction hr with
  | nil => exact Or.inl ⟨rfl,rfl,rfl⟩
  | @step n a d A D hr hm ih =>
      right
      rcases ih with hseed | hp
      · rcases hseed with ⟨hn,ha,hd⟩
        subst n; subst a; subst d
        exact seed_step_phase12 hm
      · exact phase12_preserved hp hm

/-- A reachable middle-even predecessor is either odd with d=5 mod12, or
    has first counter 2 mod4 and d=2 mod6. -/
theorem reachable_middleEven_shape {n a d : Nat} (hr : Reach n a d)
    (h1 : a < d) (hp : (d-a)%2 = 0) :
    (a % 2 = 1 ∧ d % 12 = 5) ∨ (a % 4 = 2 ∧ d % 6 = 2) := by
  have hphase := root_phase12 hr
  rcases hphase with hseed | hphase
  · rcases hseed with ⟨hn,ha,hd⟩
    subst a; subst d
    omega
  · unfold Phase12 at hphase
    rcases hphase with hodd | h40 | h42
    · exact Or.inl hodd
    · omega
    · rcases h42.2 with hd1 | hd2
      · omega
      · exact Or.inr ⟨h42.1,hd2⟩

#print axioms phase12_preserved
#print axioms root_phase12
#print axioms reachable_middleEven_shape
end BB6.Agent2F321Phase12
