import C26Rectangle
import Lean.Elab.Tactic.Omega

namespace BB6.Agent23C26

private theorem high_margin (n : Nat) :
    3*(n+3)+261 ≤ 3*2^(2*(n+3)+2) := by
  induction n with
  | zero => decide
  | succ n ih =>
      have he : 2*(n+1+3)+2=(2*(n+3)+2)+2 := by omega
      rw [he,Nat.pow_add]
      simp only [show (2:Nat)^2=4 by decide]
      omega

/-- An infinite two-parameter high stopping congruence class falls into the
    uniform original-blank forbidden section rectangle. -/
theorem blank_no_high_pair (j m k : Nat)
    (hj : j%32=31) (hpair : (j+3*m+5)%256=230)
    (hgate : k+j+3*m+5=2^(2*m+2)*(j+3)) :
    ¬ BB6.Agent3.CReach (2*j+3) k := by
  have hm3 : 3≤m := by omega
  have hxmod : (2*j+3)%64=1 := by omega
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
  have hkmod : k%256=26 := by omega
  have hp : 1≤2^(2*m+2) := Nat.pow_pos (by decide)
  have hj : j≤2^(2*m+2)*j := by
    simpa only [Nat.one_mul] using Nat.mul_le_mul_right j hp
  obtain ⟨n,hn⟩ : ∃ n, m=n+3 := ⟨m-3,by omega⟩
  have hb := high_margin n
  have hsplit : 2^(2*m+2)*(j+3) = 2^(2*m+2)*j + 3*2^(2*m+2) := by
    simp [Nat.mul_add, Nat.mul_comm]
  rw [hsplit] at hgate
  have hkbig : 256≤k := by
    rw [hn] at hgate hj
    omega
  have hv : 1≤k/256 := by omega
  have hxform : 2*j+3=64*((2*j+3)/64)+1 := by omega
  have hyform : k=256*(k/256)+26 := by omega
  intro hr
  rw [hxform,hyform] at hr
  exact blank_no_rectangle ((2*j+3)/64) (k/256) hv hr

#print axioms blank_no_high_pair
end BB6.Agent23C26
