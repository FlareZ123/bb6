import Std
namespace BB6.Agent12General

def W (R q:Nat):Nat := 2^(65536*q+R-16)
def S (R q:Nat):Nat := 7*W R q-q-1

private theorem basic_pow_growth (q:Nat):q+1≤2^q := by
 induction q with
 | zero => decide
 | succ q ih => rw [Nat.pow_succ]; omega

theorem W_growth (R q:Nat) (hR:32≤R):64*(q+1)≤W R q := by
 have hq:=basic_pow_growth q
 have hExp:q+6≤65536*q+R-16:=by omega
 have hp:(2:Nat)^(q+6)≤(2:Nat)^(65536*q+R-16) :=
   Nat.pow_le_pow_right (by decide) hExp
 have hPow:(2:Nat)^(q+6)=64*(2:Nat)^q:=by
   rw [Nat.pow_add]
   simp only [show (2:Nat)^6=64 by decide]
   omega
 unfold W
 rw [hPow] at hp
 omega

theorem S_shift (R q:Nat) (hR:32≤R):S R q+(q+1)=7*W R q := by
 unfold S
 have h:=W_growth R q hR
 omega

theorem lower_power (R q:Nat) (hR:32≤R):
    14*2^(65536*q+R-1)=458752*W R q := by
 rw [show 65536*q+R-1=(65536*q+R-16)+15 by omega, Nat.pow_add]
 simp only [show (2:Nat)^15=32768 by decide]
 unfold W
 omega

theorem upper_power (R q:Nat) (hR:32≤R):
    14*2^(65536*q+R)=917504*W R q := by
 rw [show 65536*q+R=(65536*q+R-16)+16 by omega, Nat.pow_add]
 simp only [show (2:Nat)^16=65536 by decide]
 unfold W
 omega

theorem gap_band (R q A C:Nat) (hR:32≤R)
 (hAlo:66048≤A)(hAhi:A≤130560)(hC:C≤129782):
 14*2^(65536*q+R-1)<A*S R q+C ∧
 A*S R q+C<14*2^(65536*q+R) := by
 have hlo:=Nat.mul_le_mul_right (S R q) hAlo
 have hhi:=Nat.mul_le_mul_right (S R q) hAhi
 have hw:=W_growth R q hR
 have hs:=S_shift R q hR
 rw [lower_power R q hR,upper_power R q hR]
 omega

private theorem no_power_in_gap (N v:Nat)
 (hlo:14*2^(N-1)<v)(hhi:v<14*2^N):∀j:Nat,v≠14*2^j:=by
 intro j heq
 by_cases hn:N=0
 · subst N; simp at hlo; omega
 by_cases hj:j<N
 · have he:j≤N-1:=by omega
   have hp:2^j≤2^(N-1):=Nat.pow_le_pow_right (by decide) he
   omega
 · have hp:2^N≤2^j:=Nat.pow_le_pow_right (by decide) (by omega)
   omega

theorem no_power_leaf (R q A C:Nat) (hR:32≤R)
 (hAlo:66048≤A)(hAhi:A≤130560)(hC:C≤129782):
 ∀j:Nat,A*S R q+C≠14*2^j:=by
 obtain ⟨hl,hu⟩:=gap_band R q A C hR hAlo hAhi hC
 exact no_power_in_gap (65536*q+R) _ (by simpa using hl) hu

theorem root_identity (R q:Nat) (hR:32≤R) (hC:2*R+16≤131072):
 131072*S R q+(131072-2*R-16) =
 14*2^(65536*q+R)-2*(65536*q+R)-16 := by
 have hs:=S_shift R q hR
 have hp:=upper_power R q hR
 omega

#print axioms root_identity
#print axioms no_power_leaf
end BB6.Agent12General
