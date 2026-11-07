import Std
namespace PeriodRotate

theorem double_threshold (B S Q H : Nat)
    (hB : 0 < B) (hS : 0 < S)
    (h : B*Q=S*H) : (2*Q<S ↔ 2*H<B) := by
  constructor
  · intro hq
    by_cases hh : 2*H<B
    · exact hh
    · have hle : B≤2*H := by omega
      have hm : B*(2*Q) = S*(2*H) := by
        calc
          B*(2*Q) = 2*(B*Q) := by ac_rfl
          _ = 2*(S*H) := by rw [h]
          _ = S*(2*H) := by ac_rfl
      have hl := Nat.mul_lt_mul_of_pos_left hq hB
      have hr := Nat.mul_le_mul_left S hle
      have hc : B*S=S*B := by ac_rfl
      omega
  · intro hh
    by_cases hq : 2*Q<S
    · exact hq
    · have hle : S≤2*Q := by omega
      have hm : B*(2*Q) = S*(2*H) := by
        calc
          B*(2*Q) = 2*(B*Q) := by ac_rfl
          _ = 2*(S*H) := by rw [h]
          _ = S*(2*H) := by ac_rfl
      have hl := Nat.mul_lt_mul_of_pos_left hh hS
      have hr := Nat.mul_le_mul_left B hle
      have hc : B*S=S*B := by ac_rfl
      omega

/-- Exact synchronized binary rotation for an integral rational H/B=Q/S.
    The odd denominator prevents the rotated residue from becoming zero. -/
theorem ratio_rotates (B S Q H : Nat)
    (hB : 0 < B) (hOdd : B%2=1) (hS : 0 < S)
    (hH : 0<H ∧ H<B) (hQ : 0<Q ∧ Q<S)
    (h : B*Q=S*H) :
    B*((2*Q)%S)=S*((2*H)%B) ∧
    0<(2*Q)%S ∧ (2*Q)%S<S ∧
    0<(2*H)%B ∧ (2*H)%B<B := by
  have hth := double_threshold B S Q H hB hS h
  have hm : B*(2*Q)=S*(2*H) := by
    calc
      B*(2*Q)=2*(B*Q) := by ac_rfl
      _ = 2*(S*H) := by rw [h]
      _ = S*(2*H) := by ac_rfl
  by_cases hlt : 2*Q<S
  · have hHlt := hth.mp hlt
    rw [Nat.mod_eq_of_lt hlt, Nat.mod_eq_of_lt hHlt]
    constructor
    · exact hm
    · have hpq : 0<2*Q := by omega
      have hph : 0<2*H := by omega
      omega
  · have hqge : S≤2*Q := by omega
    have hhge : B≤2*H := by
      have hh := hth.mpr
      omega
    have hqmax : 2*Q-S<S := by omega
    have hhmax : 2*H-B<B := by omega
    have hHne : 2*H≠B := by
      intro he
      have hbmod := congrArg (fun n:Nat => n%2) he
      omega
    have hph : 0<2*H-B := by omega
    have hpq : 0<2*Q-S := by
      by_cases he : 2*Q=S
      · have : 2*H=B := by
          have hEq : B*(2*Q)=B*S := by rw [he]
          rw [hEq] at hm
          have hS2 : 2*H=B := Nat.eq_of_mul_eq_mul_left hS (by
            simpa [Nat.mul_comm] using hm.symm)
          exact hS2
        exact False.elim (hHne this)
      · omega
    rw [Nat.mod_eq_sub_mod hqge, Nat.mod_eq_sub_mod hhge,
      Nat.mod_eq_of_lt hqmax, Nat.mod_eq_of_lt hhmax]
    have heq : B*(2*Q-S)=S*(2*H-B) := by
      rw [Nat.mul_sub_left_distrib, Nat.mul_sub_left_distrib]
      have hc : B*S=S*B := by ac_rfl
      omega
    exact ⟨heq, hpq, hqmax, hph, hhmax⟩

#print axioms ratio_rotates
end PeriodRotate
