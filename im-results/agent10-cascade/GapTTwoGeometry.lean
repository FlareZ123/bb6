import GapTZeroGeometry
set_option maxHeartbeats 0
namespace CascadeGapTZero

/-- Sharper d upper interval makes the valuation-two image too small to
    lie in any exact odd first-reset parent band. -/
theorem strong_ttwo_upper (n s d a b c f g : Nat) (hn:20≤n)
  (hdhi:1000*d≤1977*s)
  (he0:8*d=8*s+a+(n-8)+5)
  (he1:2*a=8*s+b+(n-8))
  (he2:2*b=8*s+c+(n-8))
  (he3:2*c=8*s+f+(n-8))
  (he4:2*f=8*s+g+(n-8)) :
  8*(2*g+5)+54<81*s := by
  omega

/-- An exponent-two source odd ancestor would lie in the open interval
    (2^k,3*2^(k-1)), disjoint from all odd-image bands. -/
theorem t_two_no_band (k s g z l:Nat) (hs:s=2^k)
 (hlow:9*s+6*k+12<2*g+5)
 (hupper:8*(2*g+5)+54<81*s)
 (hnum:2*g+5=27*z)
 (hband:6*2^l+1≤4*z ∧ 4*z≤8*2^l-1) : False := by
  have hlo:s<4*z:=by omega
  have hhi:2*(4*z)+2<3*s:=by omega
  have hlo':2^k<4*z:=by rw [←hs];exact hlo
  have hhi':2*(4*z)+2<3*2^k:=by rw [←hs];exact hhi
  have hbandgap: ∀l, ¬(6*2^l+1≤4*z ∧ 4*z≤8*2^l-1) := by
    intro l0 ⟨ha,hb⟩
    by_cases hkl:l0+3≤k
    · have hp:2^(l0+3)≤2^k:=Nat.pow_le_pow_right (by decide:0<(2:Nat)) hkl
      rw [Nat.pow_add] at hp
      omega
    · have hp:2^k≤2^(l0+2):=Nat.pow_le_pow_right (by decide:0<(2:Nat)) (by omega)
      rw [Nat.pow_add] at hp
      omega
  exact hbandgap l hband

#print axioms strong_ttwo_upper
#print axioms t_two_no_band
end CascadeGapTZero
