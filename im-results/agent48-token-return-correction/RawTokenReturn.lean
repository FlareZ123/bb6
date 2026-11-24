import DStartFinite
import Lean.Elab.Tactic.Omega

namespace BB6.Portfolio

/-- Mirrored #85 token state tok_DR [2,0] [(s,0)] [0], positioned at head 0. -/
def tokenT (s : Nat) : Cfg :=
  ⟨0,0,fun i => decide ((0 ≤ i ∧ i ≤ 2) ∨ (5 ≤ i ∧ i ≤ (s:Int)+5))⟩

@[simp] private theorem d0_0_false : D0 (0:State) false = some (true, .R, (1 : State)) := rfl
@[simp] private theorem d0_0_true : D0 (0:State) true = some (false, .R, (4 : State)) := rfl
@[simp] private theorem d0_1_false : D0 (1:State) false = some (true, .L, (2 : State)) := rfl
@[simp] private theorem d0_1_true : D0 (1:State) true = some (false, .R, (0 : State)) := rfl
@[simp] private theorem d0_2_false : D0 (2:State) false = some (true, .L, (0 : State)) := rfl
@[simp] private theorem d0_2_true : D0 (2:State) true = some (true, .L, (3 : State)) := rfl
@[simp] private theorem d0_3_false : D0 (3:State) false = some (true, .L, (2 : State)) := rfl
@[simp] private theorem d0_3_true : D0 (3:State) true = some (true, .L, (5 : State)) := rfl
@[simp] private theorem d0_4_false : D0 (4:State) false = some (false, .L, (2 : State)) := rfl
@[simp] private theorem d0_4_true : D0 (4:State) true = some (false, .L, (1 : State)) := rfl
@[simp] private theorem d0_5_false : D0 (5:State) false = some (true, .L, (4 : State)) := rfl
@[simp] private theorem d0_5_true : D0 (5:State) true = none := rfl

theorem tokenT_to_F0Pure (s : Nat) :
    run D0 21 (some (tokenT s)) = some (F0Pure (s+8) (-3)) := by
  have h : (0:Int) ≤ (s:Int) := by omega
  simp [run, step, Dir.dx, tokenT, updateTape, F0Pure]
  congr 1
  funext i
  simp only [updateTape]
  by_cases hm2 : i = -2
  · subst i; simp; omega
  by_cases hm1 : i = -1
  · subst i; simp; omega
  by_cases h0 : i = 0
  · subst i; simp; omega
  by_cases h1 : i = 1
  · subst i; simp; omega
  by_cases h2 : i = 2
  · subst i; simp; omega
  by_cases h3 : i = 3
  · subst i; simp; omega
  by_cases h4 : i = 4
  · subst i; simp; omega
  simp [hm2, hm1, h0, h1, h2, h3, h4]
  apply Bool.eq_iff_iff.mpr
  simp only [Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_eq]
  omega

#print axioms tokenT_to_F0Pure

private theorem token_run_add (n m : Nat) (c : Option Cfg) :
    run D0 (n+m) c = run D0 m (run D0 n c) := by
  induction m with
  | zero => rfl
  | succ m ih =>
    rw [Nat.add_succ]
    change (run D0 (n+m) c).bind (step D0) = (run D0 m (run D0 n c)).bind (step D0)
    rw [ih]

def tokenHaltsAt (c : Cfg) (n : Nat) : Prop :=
  ∃ last, run D0 n (some c) = some last ∧ step D0 last = none

theorem tokenT_halting_iff (s : Nat) :
    (∃ n, tokenHaltsAt (tokenT s) n) ↔
      (∃ n, tokenHaltsAt (F0Pure (s+8) (-3)) n) := by
  constructor
  · rintro ⟨n, last, hr, hs⟩
    have h21 := tokenT_to_F0Pure s
    have hn : 21 ≤ n := by
      by_cases h : 21 ≤ n
      · exact h
      · have he : 21 = n+1+(20-n) := by omega
        rw [he, token_run_add, run, hr] at h21
        change run D0 (20-n) (step D0 last) = some (F0Pure (s+8) (-3)) at h21
        rw [hs] at h21
        have hz : ∀ m, run D0 m none = none := by
          intro m; induction m <;> simp [run, *]
        rw [hz] at h21
        contradiction
    refine ⟨n-21, last, ?_, hs⟩
    have he : n=21+(n-21) := by omega
    conv at hr => lhs; rw [he, token_run_add, h21]
    exact hr
  · rintro ⟨n,last,hr,hs⟩
    exact ⟨21+n,last,by rw [token_run_add, tokenT_to_F0Pure, hr],hs⟩

#print axioms tokenT_halting_iff
end BB6.Portfolio
