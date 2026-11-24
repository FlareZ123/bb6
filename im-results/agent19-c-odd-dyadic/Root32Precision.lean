import Lean.Elab.Tactic.Omega
import Init.Data.Nat.Coprime

namespace BB6.Agent19Root32Precision

/-- Bitwise lifting of the unique solution of 17300+22155*(t+j)=0
    modulo 2^p. No search over the root parameter, or huge exponent. -/
def rootResidue (j : Nat) : Nat → Nat
  | 0 => 0
  | p+1 =>
    let b := rootResidue j p
    if (17300+22155*(b+j))%2^(p+1)=0 then b else b+2^p

private theorem expression_mod (t j m : Nat) :
    (17300+22155*(t%m+j))%m=(17300+22155*(t+j))%m := by
  rw [Nat.add_mod, Nat.mul_mod, Nat.add_mod_mod]
  conv => rhs; rw [Nat.add_mod, Nat.mul_mod]
  simp only [Nat.add_mod_mod, Nat.mod_add_mod]

private theorem unique_residue (x y j p : Nat)
    (hx : x<2^p) (hy : y<2^p)
    (h1 : 2^p ∣ 17300+22155*(x+j))
    (h2 : 2^p ∣ 17300+22155*(y+j)) : x=y := by
  have hco : Nat.Coprime (2^p) 22155 :=
    (show Nat.Coprime 2 22155 by decide).pow_left p
  rcases Nat.le_total x y with h | h
  · have hd := Nat.dvd_sub h2 h1
    have he : (17300+22155*(y+j))-(17300+22155*(x+j))=22155*(y-x) := by omega
    rw [he] at hd
    have hdiv := hco.dvd_of_dvd_mul_left hd
    have hz : y-x=0 := by
      by_cases hn : y-x=0
      · exact hn
      · have := Nat.le_of_dvd (Nat.pos_of_ne_zero hn) hdiv
        omega
    omega
  · have hd := Nat.dvd_sub h1 h2
    have he : (17300+22155*(x+j))-(17300+22155*(y+j))=22155*(x-y) := by omega
    rw [he] at hd
    have hdiv := hco.dvd_of_dvd_mul_left hd
    have hz : x-y=0 := by
      by_cases hn : x-y=0
      · exact hn
      · have := Nat.le_of_dvd (Nat.pos_of_ne_zero hn) hdiv
        omega
    omega

/-- Whenever a genuine exact root exists, lifting recovers its t residue
    at every precision at which the power of two divides the RHS. -/
theorem rootResidue_correct (t j p : Nat)
    (h : 2^p ∣ 17300+22155*(t+j)) : t%2^p=rootResidue j p := by
  induction p with
  | zero => simp [rootResidue,Nat.mod_one]
  | succ p ih =>
    have hm : 0<2^p := Nat.pow_pos (by decide)
    have hd : 2^p ∣ 2^(p+1) := Nat.pow_dvd_pow 2 (by omega)
    have hlo := ih (Nat.dvd_trans hd h)
    let r := t%2^(p+1)
    have hr : r<2^(p+1) := Nat.mod_lt _ (Nat.pow_pos (by decide))
    have hrlo : r%2^p=rootResidue j p := by
      dsimp [r]
      rw [Nat.mod_mod_of_dvd _ hd,hlo]
    have hb : rootResidue j p<2^p := by rw [←hlo]; exact Nat.mod_lt _ hm
    have hrD : r=rootResidue j p ∨ r=rootResidue j p+2^p := by
      have he := Nat.mod_add_div r (2^p)
      rw [hrlo] at he
      have hq : r/2^p≤1 := by
        apply Nat.le_of_lt_succ
        apply (Nat.div_lt_iff_lt_mul hm).2
        simpa [Nat.pow_succ,Nat.mul_comm] using hr
      have hq' : r/2^p=0 ∨ r/2^p=1 := Nat.le_one_iff_eq_zero_or_eq_one.mp hq
      rcases hq' with hq' | hq' <;> simp [hq'] at he <;> omega
    have hrdvd : 2^(p+1) ∣ 17300+22155*(r+j) := by
      apply Nat.dvd_of_mod_eq_zero
      rw [show (17300+22155*(r+j))%2^(p+1)=(17300+22155*(t+j))%2^(p+1) from expression_mod t j _]
      exact Nat.mod_eq_zero_of_dvd h
    change r=rootResidue j (p+1)
    rw [rootResidue]
    split
    · rename_i hz
      exact unique_residue r _ j (p+1) hr (by exact Nat.lt_trans hb (Nat.pow_lt_pow_right (by decide) (by omega))) hrdvd (Nat.dvd_of_mod_eq_zero hz)
    · rename_i hz
      rcases hrD with he | he
      · rw [he] at hrdvd
        exact False.elim (hz (Nat.mod_eq_zero_of_dvd hrdvd))
      · exact he

theorem rootResidue_exact (t j E p : Nat)
    (hp : p≤E-17)
    (h : 17300+22155*(t+j)=5*2^(E-17)) :
    t%2^p=rootResidue j p := by
  apply rootResidue_correct
  rw [h]
  exact Nat.dvd_mul_left_of_dvd (Nat.pow_dvd_pow 2 hp) 5

/-- The computed residue only depends on the root index modulo the requested
    precision. This makes a single certificate valid for the entire cylinder. -/
theorem rootResidue_periodic (j p : Nat) :
    rootResidue j p = rootResidue (j%2^p) p := by
  induction p generalizing j with
  | zero => rfl
  | succ p ih =>
    have hd : 2^p ∣ 2^(p+1) := Nat.pow_dvd_pow 2 (by omega)
    have hlo : rootResidue (j%2^(p+1)) p = rootResidue j p := by
      rw [ih (j%2^(p+1)), Nat.mod_mod_of_dvd _ hd, ←ih j]
    have hmod (b : Nat) :
        (17300+22155*(b+j%2^(p+1)))%2^(p+1)=
        (17300+22155*(b+j))%2^(p+1) := by
      simpa only [Nat.add_comm b] using expression_mod j b (2^(p+1))
    simp only [rootResidue,hlo,hmod]

#print axioms rootResidue_periodic
#print axioms rootResidue_correct
#print axioms rootResidue_exact
end BB6.Agent19Root32Precision
