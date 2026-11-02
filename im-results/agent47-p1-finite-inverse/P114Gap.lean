import Std
set_option maxRecDepth 8192
set_option maxHeartbeats 2000000
namespace BB6.Agent47P114

def w (q:Nat) : Nat := 2^(1024*q)
def u (q:Nat) : Nat := 112*w q-q

private theorem power_dominates (q:Nat) : q+1 ≤ 2^q := by
  induction q with
  | zero => decide
  | succ q ih =>
    rw [Nat.pow_succ]
    omega

theorem w_growth (q:Nat) : q+1≤w q := by
  have he : q≤1024*q := by omega
  have hp : (2:Nat)^q ≤ (2:Nat)^(1024*q) := Nat.pow_le_pow_right (by decide) he
  have hdominates := power_dominates q
  unfold w
  omega

theorem u_shift (q:Nat) : u q+q=112*w q := by
  unfold u
  have h:=w_growth q
  omega

theorem u_linear_lower (q:Nat) : 111*q+112 ≤ u q := by
  have h:=w_growth q
  have hs:=u_shift q
  omega

theorem u_lower (q:Nat) : 112≤u q := by
  have h:=u_linear_lower q
  omega

private theorem power_lower (q:Nat) : 14*2^(1024*q+13)=1024*(u q+q) := by
  rw [u_shift]
  unfold w
  rw [Nat.pow_add]
  simp only [show (2:Nat)^13=8192 by decide]
  omega

private theorem power_upper (q:Nat) : 14*2^(1024*q+14)=2048*(u q+q) := by
  rw [u_shift]
  unfold w
  rw [Nat.pow_add]
  simp only [show (2:Nat)^14=16384 by decide]
  omega

private theorem no_14_power_between (e v:Nat)
    (hl:14*2^e<v) (hu:v<14*2^(e+1)) :
    ∀ j:Nat, v ≠ 14*2^j := by
  intro j heq
  have hlow : 2^e < 2^j := by omega
  have hupper : 2^j < 2^(e+1) := by omega
  have hjlo : e<j :=
    (Nat.pow_lt_pow_iff_right (by decide : 1<(2:Nat))).mp hlow
  have hjhi : j<e+1 :=
    (Nat.pow_lt_pow_iff_right (by decide : 1<(2:Nat))).mp hupper
  omega

/-- Uniform forbidden 14-power interval for the fifteen symbolic n = 1024q+14
terminal leaves. It assumes only the coefficient band and blank-index growth. -/
theorem power_gap (q A C : Nat)
    (hA : 1074≤A) (hB : A≤1998) (hC:C≤58) :
    ∀ j:Nat, A*u q-C ≠ 14*2^j := by
  have hl := u_linear_lower q
  have hs:=u_shift q
  have ha1 : 1074*u q ≤ A*u q := Nat.mul_le_mul_right (u q) hA
  have ha2 : A*u q ≤ 1998*u q := Nat.mul_le_mul_right (u q) hB
  have hlow : 1024*(u q+q)<A*u q-C := by omega
  have hhigh : A*u q-C<2048*(u q+q) := by omega
  apply no_14_power_between (1024*q+13)
  · simpa only [power_lower] using hlow
  · simpa only [show 1024*q+13+1=1024*q+14 by omega,
         power_upper] using hhigh

#print axioms power_gap
end BB6.Agent47P114
