import Std
namespace BB6.Agent47P1

def r54X (q : Nat) : Nat := 2^(65536*q+38)
def r54S (q : Nat) : Nat := 7*r54X q - (q+1)

private theorem basic_pow_growth (q:Nat) : q+1 ≤ 2^q := by
  induction q with
  | zero => decide
  | succ q ih =>
      rw [Nat.pow_succ]
      omega

theorem r54X_growth (q:Nat) : 32*(q+1) ≤ r54X q := by
  have hq := basic_pow_growth q
  have he : q+5 ≤ 65536*q+38 := by omega
  have hp : (2:Nat)^(q+5) ≤ (2:Nat)^(65536*q+38) :=
    Nat.pow_le_pow_right (by decide) he
  have hpow : (2:Nat)^(q+5) = 32*(2:Nat)^q := by
    rw [Nat.pow_add]
    simp only [show (2:Nat)^5=32 by decide]
    omega
  unfold r54X
  rw [hpow] at hp
  omega

theorem r54S_shift (q:Nat) : r54S q+(q+1)=7*r54X q := by
  unfold r54S
  have h := r54X_growth q
  omega

private theorem r54power_lower (q:Nat) :
    14*2^(65536*q+53) = 458752*r54X q := by
  unfold r54X
  rw [show 65536*q+53=(65536*q+38)+15 by omega, Nat.pow_add]
  simp only [show (2:Nat)^15=32768 by decide]
  omega

private theorem r54power_upper (q:Nat) :
    14*2^(65536*q+54) = 917504*r54X q := by
  unfold r54X
  rw [show 65536*q+54=(65536*q+38)+16 by omega, Nat.pow_add]
  simp only [show (2:Nat)^16=65536 by decide]
  omega

private theorem no_14_power_between (e v:Nat)
    (hl:14*2^e<v) (hu:v<14*2^(e+1)) :
    ∀ j:Nat, v ≠ 14*2^j := by
  intro j heq
  have hlow : 2^e < 2^j := by omega
  have hupper : 2^j < 2^(e+1) := by omega
  have hjlo : e < j :=
    (Nat.pow_lt_pow_iff_right (by decide : 1<(2:Nat))).mp hlow
  have hjhi : j < e+1 :=
    (Nat.pow_lt_pow_iff_right (by decide : 1<(2:Nat))).mp hupper
  omega

private theorem r54_gap_generic (q A C:Nat)
    (hl:458752*r54X q<A*r54S q+C)
    (hu:A*r54S q+C<917504*r54X q) :
    ∀j:Nat, A*r54S q+C ≠14*2^j := by
  apply no_14_power_between (65536*q+53)
  · simpa only [r54power_lower] using hl
  · simpa only [show 65536*q+53+1=65536*q+54 by omega,
          r54power_upper] using hu

/-- All three exact even-counter cone leaves lie in the empty gap between
14*2^(n-1) and 14*2^n for n=65536q+54. -/
theorem r54_gap0 (q:Nat) :
    ∀j:Nat,122880*r54S q+122770 ≠14*2^j := by
  apply r54_gap_generic q 122880 122770
  · have hx := r54X_growth q
    have hs := r54S_shift q
    omega
  · have hx := r54X_growth q
    have hs := r54S_shift q
    omega

theorem r54_gap1 (q:Nat) :
    ∀j:Nat,81920*r54S q+81848 ≠14*2^j := by
  apply r54_gap_generic q 81920 81848
  · have hx := r54X_growth q
    have hs := r54S_shift q
    omega
  · have hx := r54X_growth q
    have hs := r54S_shift q
    omega

theorem r54_gap2 (q:Nat) :
    ∀j:Nat,73728*r54S q+73662 ≠14*2^j := by
  apply r54_gap_generic q 73728 73662
  · have hx := r54X_growth q
    have hs := r54S_shift q
    omega
  · have hx := r54X_growth q
    have hs := r54S_shift q
    omega

#print axioms r54_gap0
#print axioms r54_gap1
#print axioms r54_gap2
end BB6.Agent47P1
