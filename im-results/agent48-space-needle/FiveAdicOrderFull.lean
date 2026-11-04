import FiveAdicAll
import Lean.Elab.Tactic.Omega
set_option maxHeartbeats 0
namespace BB6.Agent48.FiveAdic

private theorem pow_two_mod_five_period (n : Nat) : (2:Nat)^(4*n)%5=1 := by
  induction n with
  | zero => decide
  | succ n ih =>
      rw [show 4*(n+1)=4*n+4 by omega, Nat.pow_add, Nat.mul_mod, ih]

private theorem one_mod_five_iff (K : Nat) :
    (2:Nat)^K%5=1 ↔ K%4=0 := by
  let q := K/4
  let r := K%4
  have hq : K=4*q+r := by dsimp [q,r]; omega
  have hr : r<4 := by dsimp [r]; omega
  have hmod : (2:Nat)^K%5=(2:Nat)^r%5 := by
    rw [hq, Nat.pow_add,Nat.mul_mod,pow_two_mod_five_period]
    simp
  rw [hmod]
  constructor
  · intro h
    have hcases : r=0∨r=1∨r=2∨r=3 := by omega
    rcases hcases with h0|h1|h2|h3
    · simpa [r,h0] using h0
    · simp [h1] at h
    · simp [h2] at h
    · simp [h3] at h
  · intro h
    have heq : r=0 := h
    rw [heq]

private theorem mod_five_iff_dvd (K : Nat) :
    (2:Nat)^K%5=1 ↔ 5 ∣ (2^K-1) := by
  have hp : 0 < (2:Nat)^K := Nat.pow_pos (by decide)
  constructor
  · intro h
    apply Nat.dvd_of_mod_eq_zero
    omega
  · rintro ⟨m,hm⟩
    omega

/-- Exact multiplicative order of two modulo every positive fifth power. -/
theorem exact_power_five_order (t K : Nat) :
    (5^(t+1) ∣ 2^K-1) ↔ (4*5^t ∣ K) := by
  induction t generalizing K with
  | zero =>
      change (5 ∣ 2^K-1) ↔ (4 ∣ K)
      rw [←mod_five_iff_dvd]
      rw [one_mod_five_iff]
      exact Nat.dvd_iff_mod_eq_zero.symm
  | succ t ih =>
      constructor
      · intro hbig
        have hd : 5^(t+1) ∣ 5^(t+2) := by
          refine ⟨5,?_⟩
          rw [show t+2=t+1+1 by omega,Nat.pow_succ']
          ac_rfl
        have hsmall : 5^(t+1) ∣ 2^K-1 := by
          obtain ⟨x,hx⟩ := hd
          obtain ⟨y,hy⟩ := hbig
          refine ⟨x*y,?_⟩
          rw [hy,hx]
          ac_rfl
        obtain ⟨m,hm⟩ := (ih K).mp hsmall
        have hh : 5^(t+2) ∣ 2^(4*5^t*m)-1 := by
          simpa only [hm] using hbig
        obtain ⟨z,hz⟩ := (five_power_divides_iff t m).mp hh
        refine ⟨z,?_⟩
        rw [hm,hz,Nat.pow_succ']
        ac_rfl
      · rintro ⟨m,hm⟩
        have hlow : 5^(t+2) ∣ 2^(4*5^t*(5*m))-1 :=
          (five_power_divides_iff t (5*m)).mpr ⟨m,rfl⟩
        have hkm : K = 4*5^t*(5*m) := by
          rw [hm,Nat.pow_succ']
          ac_rfl
        simpa only [hkm,show t+1+1=t+2 by omega] using hlow

#print axioms exact_power_five_order
end BB6.Agent48.FiveAdic
