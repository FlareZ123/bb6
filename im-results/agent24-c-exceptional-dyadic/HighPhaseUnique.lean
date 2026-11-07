import Lean.Elab.Tactic.Omega

namespace BB6.Agent24Phase

def phaseResidue (j m r : Nat) : Prop :=
    (j+3*m+3)%2^(r+4)=9*2^r ∨
    (j+3*m+3)%2^(r+4)=13*2^r

private theorem phase_lowbit (D r : Nat)
    (h : D%2^(r+4)=9*2^r ∨ D%2^(r+4)=13*2^r) :
    D%2^(r+1)=2^r := by
  have hd : 2^(r+1) ∣ 2^(r+4) := Nat.pow_dvd_pow 2 (by omega)
  have he : 2^(r+1)=2*2^r := by
    rw [Nat.pow_succ]
    omega
  have hp : 0 < 2^r := Nat.pow_pos (by decide)
  rw [←Nat.mod_mod_of_dvd D hd]
  rcases h with h | h
  · rw [h,he, Nat.mul_mod_mul_right]
    simp
  · rw [h,he, Nat.mul_mod_mul_right]
    simp

private theorem phase_high_zero (D r s : Nat) (hrs:r<s)
    (h : D%2^(s+4)=9*2^s ∨ D%2^(s+4)=13*2^s) :
    D%2^(r+1)=0 := by
  have h1 : 2^(r+1) ∣ 2^(s+4) := Nat.pow_dvd_pow 2 (by omega)
  have h2 : 2^(r+1) ∣ 2^s := Nat.pow_dvd_pow 2 (by omega)
  have h9 : 2^(r+1) ∣ 9*2^s := by
    rcases h2 with ⟨w,hw⟩
    refine ⟨9*w,?_⟩
    rw [hw]
    ac_rfl
  have h13 : 2^(r+1) ∣ 13*2^s := by
    rcases h2 with ⟨w,hw⟩
    refine ⟨13*w,?_⟩
    rw [hw]
    ac_rfl
  rw [←Nat.mod_mod_of_dvd D h1]
  rcases h with h | h
  · rw [h]
    exact Nat.mod_eq_zero_of_dvd h9
  · rw [h]
    exact Nat.mod_eq_zero_of_dvd h13

/-- Any high stopping parameter pair admits at most one phase-excluded
    depth. Both branches have exact dyadic valuation r, so even their
    union contains no depth overlap. -/
theorem phase_unique_depth (j m r s : Nat)
    (hr : phaseResidue j m r)
    (hs : phaseResidue j m s) : r=s := by
  by_cases hlt : r < s
  · have h1 := phase_lowbit (j+3*m+3) r hr
    have h0 := phase_high_zero (j+3*m+3) r s hlt hs
    have hp : 0 < 2^r := Nat.pow_pos (by decide)
    omega
  · by_cases hgt : s < r
    · have h1 := phase_lowbit (j+3*m+3) s hs
      have h0 := phase_high_zero (j+3*m+3) s r hgt hr
      have hp : 0 < 2^s := Nat.pow_pos (by decide)
      omega
    · omega

#print axioms phase_unique_depth
end BB6.Agent24Phase
