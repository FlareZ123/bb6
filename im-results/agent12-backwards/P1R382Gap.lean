import Std
namespace BB6.Agent12Affine

def W (q : Nat) : Nat := 2^(65536*q+366)
def S (q : Nat) : Nat := 7*W q-q-1

private theorem basic_pow_growth (q : Nat) : q+1 ≤ 2^q := by
  induction q with
  | zero => decide
  | succ q ih =>
    rw [Nat.pow_succ]
    omega

theorem W_growth (q : Nat) : 64*(q+1) ≤ W q := by
  have hq := basic_pow_growth q
  have he : q+6 ≤ 65536*q+366 := by omega
  have hp : (2:Nat)^(q+6) ≤ (2:Nat)^(65536*q+366) :=
    Nat.pow_le_pow_right (by decide) he
  have hpow : (2:Nat)^(q+6) = 64*(2:Nat)^q := by
    rw [Nat.pow_add]
    simp only [show (2:Nat)^6=64 by decide]
    omega
  unfold W
  rw [hpow] at hp
  omega

theorem S_shift (q:Nat) : S q+(q+1)=7*W q := by
  unfold S
  have h := W_growth q
  omega

private theorem lower_power (q:Nat) :
    14*2^(65536*q+381) = 458752*W q := by
  unfold W
  rw [show 65536*q+381=(65536*q+366)+15 by omega, Nat.pow_add]
  simp only [show (2:Nat)^15=32768 by decide]
  omega

private theorem upper_power (q:Nat) :
    14*2^(65536*q+382) = 917504*W q := by
  unfold W
  rw [show 65536*q+382=(65536*q+366)+16 by omega, Nat.pow_add]
  simp only [show (2:Nat)^16=65536 by decide]
  omega

/-- Uniform power-free band for all 31 symbolic even leaves. -/
theorem gap_band (q A C : Nat)
    (hAlo : 66048≤A) (hAhi : A≤130560) (hC : C≤129782) :
    14*2^(65536*q+381) < A*S q+C ∧
    A*S q+C < 14*2^(65536*q+382) := by
  have hlo := Nat.mul_le_mul_right (S q) hAlo
  have hhi := Nat.mul_le_mul_right (S q) hAhi
  have hw := W_growth q
  have hs := S_shift q
  rw [lower_power, upper_power]
  omega

private theorem no_power_in_gap (N v : Nat)
    (hlo : 14*2^(N-1)<v) (hhi : v<14*2^N) :
    ∀j:Nat, v≠14*2^j := by
  intro j heq
  by_cases hn:N=0
  · subst N
    simp at hlo
    omega
  by_cases hj:j<N
  · have he:j≤N-1 := by omega
    have hp:2^j≤2^(N-1) := Nat.pow_le_pow_right (by decide) he
    omega
  · have hp:2^N≤2^j := Nat.pow_le_pow_right (by decide) (by omega)
    omega

theorem no_power_leaf (q A C : Nat)
    (hAlo : 66048≤A) (hAhi : A≤130560) (hC : C≤129782) :
    ∀j:Nat, A*S q+C≠14*2^j := by
  obtain ⟨hlo,hhi⟩ := gap_band q A C hAlo hAhi hC
  exact no_power_in_gap (65536*q+382) _
    (by simpa [show 65536*q+382-1=65536*q+381 by omega] using hlo) hhi

#print axioms no_power_leaf
end BB6.Agent12Affine
