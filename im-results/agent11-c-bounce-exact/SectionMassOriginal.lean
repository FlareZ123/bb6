import FastSectionDef
import GenericSection
import Lean.Elab.Tactic.Omega

namespace BB6.Agent11Mass
open BB6.Agent46
open BB6.Agent8Section

theorem bounce_weight_growth (c : Nat) : ∀ k x y : Nat,
    (bounce k c).2 = some (x,y) → c+2*k+4≤x+2*y := by
  induction c using Nat.strongRecOn with
  | ind c ih =>
    intro k x y h
    rw [bounce.eq_1] at h
    by_cases hc : c<4
    · simp [hc] at h
    simp only [hc, ite_false] at h
    by_cases hk : k%2=1
    · simp only [hk, ite_true] at h
      by_cases hs : c≤2*k+6
      · simp only [hs, ite_true] at h
        cases h
        omega
      · simp only [hs, ite_false] at h
        have hlt : c-(2*k+3)<c := Nat.sub_lt (by omega) (by omega)
        have hp := ih (c-(2*k+3)) hlt (2*k+3) x y h
        omega
    · simp only [hk, ite_false] at h
      by_cases hc4 : c=4
      · simp only [hc4, ite_true] at h
        cases h
        omega
      · simp only [hc4, ite_false] at h
        by_cases hc5 : c=5
        · simp [hc5] at h
        · simp only [hc5, ite_false] at h
          by_cases hs : c≤2*k+8
          · simp only [hs, ite_true] at h
            cases h
            omega
          · simp only [hs, ite_false] at h
            have hlt : c-(2*k+5)<c := Nat.sub_lt (by omega) (by omega)
            have hp := ih (c-(2*k+5)) hlt (2*k+4) x y h
            omega

theorem secNext_weight_growth (a k x y : Nat)
    (h : secNext (a,k) = some (x,y)) : a+2*k+2 ≤ x+2*y := by
  change (exactSection (a,k)).2 = some (x,y) at h
  unfold exactSection at h
  by_cases ha0 : a=0
  · simp only [ha0,ite_true] at h
    by_cases hk0 : k=0
    · simp [hk0] at h
    · simp only [hk0,ite_false] at h
      by_cases hk1 : k=1
      · simp only [hk1,ite_true] at h
        cases h
        omega
      · simp only [hk1,ite_false] at h
        have hb := bounce_weight_growth (2*k+1) 1 x y h
        omega
  · simp only [ha0,ite_false] at h
    by_cases ha1 : a=1
    · simp only [ha1,ite_true] at h
      by_cases hk0 : k=0
      · simp only [hk0,ite_true] at h
        cases h
        omega
      · simp only [hk0,ite_false] at h
        by_cases hk1 : k=1
        · simp only [hk1,ite_true] at h
          cases h
          omega
        · simp only [hk1,ite_false] at h
          by_cases hk2 : k=2
          · simp only [hk2,ite_true] at h
            cases h
            omega
          · simp only [hk2,ite_false] at h
            by_cases hk3 : k=3
            · simp only [hk3,ite_true] at h
              cases h
              omega
            · simp only [hk3,ite_false] at h
              have hb := bounce_weight_growth (2*k-3) 4 x y h
              omega
    · simp only [ha1,ite_false] at h
      by_cases hk0 : k=0
      · simp only [hk0,ite_true] at h
        cases h
        omega
      · simp only [hk0,ite_false] at h
        by_cases hregion : 2*k≤a
        · simp only [hregion,ite_true] at h
          cases h
          omega
        · simp only [hregion,ite_false] at h
          have hb := bounce_weight_growth (2*k-a+3) (a-1) x y h
          omega

def SectionReach (x y : Nat) : Prop :=
  ∃ n, run secNext n (some (5,1)) = some (x,y)

theorem run_weight_growth (n : Nat) : ∀ x y : Nat,
  run secNext n (some (5,1)) = some (x,y) → 7+2*n ≤ x+2*y := by
  induction n with
  | zero =>
    intro x y h
    simp only [run] at h
    cases h
    omega
  | succ n ih =>
    intro x y h
    change (run secNext n (some (5,1))).bind secNext = some (x,y) at h
    cases hp : run secNext n (some (5,1)) with
    | none => simp [hp] at h
    | some p =>
      rcases p with ⟨a,k⟩
      have hmass := ih a k hp
      simp only [hp,Option.bind_some] at h
      have hstep := secNext_weight_growth a k x y h
      omega

theorem section_reach_iff_bounded (x y : Nat) :
 SectionReach x y ↔ ∃ n ≤ x+2*y, run secNext n (some (5,1))=some (x,y) := by
  constructor
  · rintro ⟨n,h⟩
    have hb := run_weight_growth n x y h
    exact ⟨n,by omega,h⟩
  · rintro ⟨n,_,h⟩
    exact ⟨n,h⟩

instance section_reach_decidable (x y:Nat) : Decidable (SectionReach x y) := by
  rw [section_reach_iff_bounded]
  infer_instance

#print axioms bounce_weight_growth
#print axioms secNext_weight_growth
#print axioms run_weight_growth
#print axioms section_reach_iff_bounded
#print axioms section_reach_decidable

end BB6.Agent11Mass
