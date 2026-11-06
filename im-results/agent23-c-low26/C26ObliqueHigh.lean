import C26Oblique
import Lean.Elab.Tactic.Omega

namespace BB6.Agent23C26

private theorem high_margin_34 (n : Nat) :
    3*(n+3)+39 ≤ 3*2^(2*(n+3)+2) := by
  induction n with
  | zero => decide
  | succ n ih =>
      have he : 2*(n+1+3)+2=(2*(n+3)+2)+2 := by omega
      rw [he,Nat.pow_add]
      simp only [show (2:Nat)^2=4 by decide]
      omega

/-- A coupled modular obstruction covering 128 high parameter cells mod256. -/
theorem blank_no_high_oblique (j m k : Nat) (hm : 3≤m)
    (hpair : ((j+3*m+5)%32=6 ∧ (7*j+233)%256=(3*m)%256) ∨
             ((j+3*m+5)%32=14 ∧ (7*j+41)%256=(3*m)%256))
    (hgate : k+j+3*m+5=2^(2*m+2)*(j+3)) :
    ¬ BB6.Agent3.CReach (2*j+3) k := by
  have hpower : 256 ∣ 2^(2*m+2) := by
    change 2^8 ∣ 2^(2*m+2)
    exact Nat.pow_dvd_pow 2 (by omega)
  have hproduct : 256 ∣ 2^(2*m+2)*(j+3) := by
    obtain ⟨a,ha⟩ := hpower
    refine ⟨a*(j+3),?_⟩
    rw [ha]
    ac_rfl
  have hzero : (k+j+3*m+5)%256=0 := by
    rw [hgate]
    exact Nat.mod_eq_zero_of_dvd hproduct
  have hmod : (k%32=26 ∧ (4*(2*j+3)+k)%256=30) ∨
      (k%32=18 ∧ (4*(2*j+3)+k)%256=222) := by
    omega
  have hp : 1≤2^(2*m+2) := Nat.pow_pos (by decide)
  have hj : j≤2^(2*m+2)*j := by
    simpa only [Nat.one_mul] using Nat.mul_le_mul_right j hp
  obtain ⟨n,hn⟩ : ∃ n, m=n+3 := ⟨m-3,by omega⟩
  have hb := high_margin_34 n
  have hsplit : 2^(2*m+2)*(j+3) = 2^(2*m+2)*j + 3*2^(2*m+2) := by
    simp [Nat.mul_add,Nat.mul_comm]
  rw [hsplit] at hgate
  have hkbig : 34≤k := by
    rw [hn] at hgate hj
    omega
  exact blank_no_oblique_mod256 (2*j+3) k hkbig hmod

#print axioms blank_no_high_oblique
end BB6.Agent23C26
