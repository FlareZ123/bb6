import Lean
import Lean.Elab.Tactic.Omega

namespace S4Power

def W : List Nat → Nat
  | [] => 0
  | b :: T => b + 1 + 2 * W T

def H (a : Nat) (L : List Nat) : Option (List Nat) :=
  match L with
  | [] =>
      if a % 2 = 0 then
        if a = 0 then none else some [a/2+2,a/2-1]
      else
        if a ≤ 1 then none else (H (a/2) []).map (a/2::·)
  | b::S =>
      if a % 2 = 0 then some ((a/2+2)::(b+a/2)::S)
      else (H (b+a/2+1) S).map (a/2::·)
termination_by (L.length, a)
decreasing_by
  all_goals simp_wf
  all_goals
    first
    | omega
    | apply Prod.Lex.left; simp
    | apply Prod.Lex.right; omega

set_option maxHeartbeats 0

def Pow2 (x : Nat) : Prop := ∃ k : Nat, x = 2^k

theorem pow2_double (x : Nat) : Pow2 (2*x) ↔ Pow2 x := by
  constructor
  · rintro ⟨k,h⟩
    cases k with
    | zero => simp at h; omega
    | succ k =>
        refine ⟨k, ?_⟩
        rw [Nat.pow_succ] at h
        omega
  · rintro ⟨k,h⟩
    refine ⟨k+1, ?_⟩
    rw [Nat.pow_succ, ←h]
    omega

private theorem not_odd_gt_one_pow2 (x : Nat) (hx : 1 < x) (ho : x % 2 = 1) : ¬ Pow2 x := by
  rintro ⟨k,hk⟩
  cases k with
  | zero => simp at hk; omega
  | succ k =>
      rw [Nat.pow_succ] at hk
      omega

private theorem even_branch_not_pow2 (a : Nat) (L : List Nat) (he : a%2=0)
    (hpos : a≠0 ∨ L≠[]) : ¬ Pow2 (a+1+2*W L) := by
  have ha : 2*(a/2)=a := by omega
  have hgt : 1 < a+1+2*W L := by
    cases L with
    | nil => simp [W] at hpos ⊢; omega
    | cons b S => simp [W]; omega
  apply not_odd_gt_one_pow2 _ hgt
  omega

theorem H_none_iff_pow2 : ∀ (L : List Nat) (a : Nat),
    H a L = none ↔ Pow2 (a+1+2*W L) := by
  intro L
  induction L with
  | nil =>
      intro a
      induction a using Nat.strongRecOn with
      | ind a ih =>
        by_cases he : a%2=0
        · by_cases hzero : a=0
          · subst a
            simp [H, W, Pow2]
            exact ⟨0, rfl⟩
          · have hp := even_branch_not_pow2 a [] he (Or.inl hzero)
            simp [H,he,hzero,hp]
        · by_cases hsmall : a ≤ 1
          · have ha : a=1 := by omega
            subst a
            simp [H, W, Pow2]
            exact ⟨1, rfl⟩
          · have hlt : a/2 < a := by omega
            have ha : a=2*(a/2)+1 := by omega
            rw [H]
            simp only [he,hsmall,ite_false]
            rw [Option.map_eq_none_iff]
            rw [ih (a/2) hlt]
            have hp : a+1+2*W ([] : List Nat) = 2*((a/2)+1+2*W ([] : List Nat)) := by
              simp [W]; omega
            rw [hp,pow2_double]
  | cons b S ih =>
      intro a
      by_cases he : a%2=0
      · have hp := even_branch_not_pow2 a (b::S) he (Or.inr (by simp))
        simp [H,he,hp]
      · have ha : a=2*(a/2)+1 := by omega
        have hp : a+1+2*W (b::S) = 2*((b+a/2+1)+1+2*W S) := by
          simp [W]; omega
        rw [H]
        simp only [he,ite_false]
        rw [Option.map_eq_none_iff, ih (b+a/2+1),hp,pow2_double]

def bump17 : List Nat → List Nat
  | [] => [16]
  | b::S => (b+17)::S

def F : List Nat → Option (List Nat)
  | [] => (H 44 []).map bump17
  | b::S => (H (b+45) S).map bump17

theorem F_none_iff_pow2 (T : List Nat) :
    F T = none ↔ Pow2 (W T+45) := by
  cases T with
  | nil =>
      have hn : H 44 [] = some [24,21] := by simp [H]
      have hp : ¬ Pow2 (W ([] : List Nat)+45) := by
        apply not_odd_gt_one_pow2
        · simp [W]
        · simp [W]
      simp [F,hn,hp]
  | cons b S =>
      have hp : W (b::S)+45 = (b+45)+1+2*W S := by simp [W]; omega
      simp only [F, Option.map_eq_none_iff]
      rw [H_none_iff_pow2, ←hp]

#print axioms H_none_iff_pow2
#print axioms F_none_iff_pow2
end S4Power
