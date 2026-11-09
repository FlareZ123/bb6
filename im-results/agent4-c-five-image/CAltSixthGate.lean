import CAltSixthStrict
import Lean.Elab.Tactic.Omega

namespace BB6.Agent4Five
open BB6.Agent46

private theorem power_margin_six (q : Nat) :
    3*(q+4)+300 ≤ (2:Nat)^(2*(q+4)+2) := by
  induction q with
  | zero => decide
  | succ q ih =>
      have he : 2*((q+1)+4)+2=(2*(q+4)+2)+2 := by omega
      rw [he,Nat.pow_add]
      simp only [show (2:Nat)^2=4 by decide]
      omega

/-- Every genuine high stopping target in the new two-variable arithmetic
    strip lies in the strict fifth/sixth image gap. -/
private theorem sixth_high_lattice (r m k : Nat)
    (hm : 4≤m)
    (hpair : m%256=(32*r+64)%256)
    (hstop : k+(32*r+29)+3*m+5 =
      (2:Nat)^(2*m+2)*((32*r+29)+3)) :
    ∃ t, 2≤t ∧ (r+t)%2=0 ∧ k=128*t+30 := by
  let j := 32*r+29
  let P := (2:Nat)^(2*m+2)
  have hj : 29≤j := by dsimp [j]; omega
  have hst : k+j+3*m+5=P*(j+3) := by
    simpa only [j,P] using hstop
  have hpow : 256 ∣ P := by
    have hd : (2:Nat)^8 ∣ (2:Nat)^(2*m+2) :=
      Nat.pow_dvd_pow 2 (by omega)
    simpa [P,show (2:Nat)^8=256 by decide] using hd
  obtain ⟨z,hz⟩ := hpow
  have hzero : (k+j+3*m+5)%256=0 := by
    apply Nat.mod_eq_zero_of_dvd
    refine ⟨z*(j+3),?_⟩
    calc
      k+j+3*m+5=P*(j+3) := hst
      _=(256*z)*(j+3) := by rw [hz]
      _=256*(z*(j+3)) := by ac_rfl
  have hres : (k+128*r+226)%256=0 := by
    dsimp [j] at hzero
    omega
  have hp_bound : 3*m+300≤P := by
    have h := power_margin_six (m-4)
    have he : m-4+4=m := by omega
    rw [he] at h
    exact h
  have hp_pos : 1≤P := by omega
  have hjmul : j≤P*j := by
    simpa only [Nat.one_mul] using Nat.mul_le_mul_right j hp_pos
  have hproduct : P*(j+3)=P*j+3*P := by
    rw [Nat.mul_add]
    ac_rfl
  have hlarge : 286≤k := by
    rw [hproduct] at hst
    omega
  have hkmod : k%128=30 := by omega
  let t := (k-30)/128
  have hkt : k=128*t+30 := by dsimp [t]; omega
  have hpar : (r+t)%2=0 := by dsimp [t]; omega
  have ht : 2≤t := by dsimp [t]; omega
  exact ⟨t,ht,hpar,hkt⟩

/-- An independent source-root high halting class, complementary to the
    source-certified fourth/fifth image high filter. No finite cutoff. -/
theorem high_stop_sixth_j_m_unreachable (j m k time : Nat)
    (hj : j%32=29) (hm : 4≤m)
    (hpair : m%256=(j+35)%256)
    (hstop : k+j+3*m+5=(2:Nat)^(2*m+2)*(j+3)) :
    BB6.Agent8Section.run secNext time (some (5,1)) ≠
      some (2*j+3,k) := by
  let r := (j-29)/32
  have hjr : j=32*r+29 := by dsimp [r]; omega
  have hrpair : m%256=(32*r+64)%256 := by
    rw [hjr] at hpair
    omega
  have hrstop : k+(32*r+29)+3*m+5 =
      (2:Nat)^(2*m+2)*((32*r+29)+3) := by
    simpa only [←hjr] using hstop
  obtain ⟨t,ht,hpar,hkt⟩ :=
    sixth_high_lattice r m k hm hrpair hrstop
  have hx : 2*j+3=64*r+61 := by omega
  rw [hx,hkt]
  exact sixth_blank_unreachable r t time ht hpar

#print axioms high_stop_sixth_j_m_unreachable
end BB6.Agent4Five
