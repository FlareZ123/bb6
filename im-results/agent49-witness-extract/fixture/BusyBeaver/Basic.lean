module
public import Lean
@[expose] public section
namespace BusyBeaver
universe u v
variable {Γ : Type u} {Λ : Type v} [Inhabited Γ] [Inhabited Λ]
structure Cfg (Γ : Type u) (Λ : Type v) [Inhabited Γ] where
  a : Γ
  b : Λ
  x : Nat
abbrev Machine (Γ : Type u) (Λ : Type v) [Inhabited Γ] := Cfg Γ Λ → Option (Cfg Γ Λ)
def step (M : Machine Γ Λ) (c : Cfg Γ Λ) := M c
def multiStep (M : Machine Γ Λ) (c : Cfg Γ Λ) : Nat → Option (Cfg Γ Λ)
  | 0 => some c
  | n+1 => (step M c).bind fun c' => multiStep M c' n
def ReachesIn (M : Machine Γ Λ) (n : Nat) (c d : Cfg Γ Λ) : Prop := multiStep M c n = some d
def ReachesStar (M : Machine Γ Λ) (c d : Cfg Γ Λ) : Prop := ∃ n, multiStep M c n = some d
def ReachesPlus (M : Machine Γ Λ) (c d : Cfg Γ Λ) : Prop := ∃ n > 0, multiStep M c n = some d
theorem ReachesIn.step_left {M : Machine Γ Λ} {c₁ c₂ c₃ : Cfg Γ Λ} {n : Nat}
    (h₁ : step M c₁ = some c₂) (h₂ : ReachesIn M n c₂ c₃) : ReachesIn M (n+1) c₁ c₃ := by
  unfold ReachesIn at *; simp [multiStep,h₁,h₂]
theorem multiStep_trans {M : Machine Γ Λ} {c₁ c₂ c₃ : Cfg Γ Λ} {m n : Nat}
    (h₁ : multiStep M c₁ m = some c₂) (h₂ : multiStep M c₂ n = some c₃) : multiStep M c₁ (m+n) = some c₃ := by
  induction m generalizing c₁ with
  | zero => simp [multiStep] at h₁; subst c₂; simpa using h₂
  | succ m ih =>
    cases h : step M c₁ with
    | none => simp [multiStep,h] at h₁
    | some c' =>
      simp [multiStep,h] at h₁
      have he : m+1+n=m+n+1 := by omega
      rw [he,multiStep,h]; simp [ih h₁]
theorem ReachesIn.trans {M : Machine Γ Λ} {c₁ c₂ c₃ : Cfg Γ Λ} {m n : Nat}
    (h₁ : ReachesIn M m c₁ c₂) (h₂ : ReachesIn M n c₂ c₃) : ReachesIn M (m+n) c₁ c₃ := multiStep_trans h₁ h₂
theorem ReachesIn.zero (M : Machine Γ Λ) (c : Cfg Γ Λ) : ReachesIn M 0 c c := rfl
theorem ReachesIn.single {M : Machine Γ Λ} {c₁ c₂ : Cfg Γ Λ} (h : step M c₁ = some c₂) : ReachesIn M 1 c₁ c₂ := by
  unfold ReachesIn; simp [multiStep,h]
theorem ReachesPlus.to_star {M : Machine Γ Λ} {c₁ c₂ : Cfg Γ Λ} (h : ReachesPlus M c₁ c₂) : ReachesStar M c₁ c₂ := by
  obtain ⟨n,_,hn⟩ := h; exact ⟨n,hn⟩
theorem step_stepStar_stepPlus {M : Machine Γ Λ} {c₁ c₂ c₃ : Cfg Γ Λ}
    (h₁ : step M c₁ = some c₂) (h₂ : ReachesStar M c₂ c₃) : ReachesPlus M c₁ c₃ := by
  obtain ⟨n,hn⟩ := h₂
  exact ⟨n+1,by omega,ReachesIn.step_left h₁ hn⟩
abbrev stepPlus_stepStar := @ReachesPlus.to_star
theorem ReachesStar.trans {M : Machine Γ Λ} {c₁ c₂ c₃ : Cfg Γ Λ} (h₁ : ReachesStar M c₁ c₂) (h₂ : ReachesStar M c₂ c₃) : ReachesStar M c₁ c₃ := by
  obtain ⟨m,hm⟩ := h₁; obtain ⟨n,hn⟩ := h₂; exact ⟨m+n,multiStep_trans hm hn⟩
end BusyBeaver
