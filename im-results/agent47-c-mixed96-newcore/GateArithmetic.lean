import SecondMod96
set_option maxHeartbeats 0
namespace NewCore

theorem target_mod_general (j m k r s p a b : Nat)
    (hj : j%48=r) (hm : (j+3*m)%96=s)
    (hr : r=1 ∨ r=17 ∨ r=25 ∨ r=41)
    (hm1 : 1≤m)
    (hp : (64*(j+3))%96=p)
    (ha : (2*j+3)%96=a)
    (hb : (p+96-s-5)%96=b)
    (heq : k+j+3*m+5=2^(2*m+2)*(j+3)) : k%96=b := by
  have hpmod : (2^(2*m+2)*(j+3))%96=p := by
    by_cases h1 : m=1
    · subst m
      have hx : (16*(j+3))%96=(64*(j+3))%96 := by
        rcases hr with hr|hr|hr|hr <;> omega
      change (16*(j+3))%96=p
      exact hx.trans hp
    · have hm2 : 2≤m := by omega
      rw [Nat.mul_mod, A41.pow_even_ge6_mod96 m hm2]
      omega
  have hktot : (k+j+3*m+5)%96=p := by rw [heq]; exact hpmod
  omega

theorem second_C5 (j m k : Nat)
    (hj : j%48=1) (hm : (j+3*m)%96=4)
    (heq : k+j+3*m+5=2^(2*m+2)*(j+3)) :
    (2*j+3)%96=5 ∧ k%96=55 := by
  have hp : (64*(j+3))%96=64 := by omega
  have ha : (2*j+3)%96=5 := by omega
  refine ⟨ha, ?_⟩
  exact target_mod_general j m k 1 4 64 5 55 hj hm (Or.inl rfl) (by omega) hp ha (by decide) heq

theorem second_C53 (j m k : Nat)
    (hj : j%48=25) (hm : (j+3*m)%96=52)
    (heq : k+j+3*m+5=2^(2*m+2)*(j+3)) :
    (2*j+3)%96=53 ∧ k%96=7 := by
  have hp : (64*(j+3))%96=64 := by omega
  have ha : (2*j+3)%96=53 := by omega
  refine ⟨ha, ?_⟩
  exact target_mod_general j m k 25 52 64 53 7 hj hm (Or.inr (Or.inr (Or.inl rfl))) (by omega) hp ha (by decide) heq

theorem second_D37 (j m k : Nat)
    (hj : j%48=17) (hm : (j+3*m)%96=68)
    (heq : k+j+3*m+5=2^(2*m+2)*(j+3)) :
    (2*j+3)%96=37 ∧ k%96=55 := by
  have hp : (64*(j+3))%96=32 := by omega
  have ha : (2*j+3)%96=37 := by omega
  refine ⟨ha, ?_⟩
  exact target_mod_general j m k 17 68 32 37 55 hj hm (Or.inr (Or.inl rfl)) (by omega) hp ha (by decide) heq

theorem second_D85 (j m k : Nat)
    (hj : j%48=41) (hm : (j+3*m)%96=20)
    (heq : k+j+3*m+5=2^(2*m+2)*(j+3)) :
    (2*j+3)%96=85 ∧ k%96=7 := by
  have hp : (64*(j+3))%96=32 := by omega
  have ha : (2*j+3)%96=85 := by omega
  refine ⟨ha, ?_⟩
  exact target_mod_general j m k 41 20 32 85 7 hj hm (Or.inr (Or.inr (Or.inr rfl))) (by omega) hp ha (by decide) heq

#print axioms second_C5
#print axioms second_C53
#print axioms second_D37
#print axioms second_D85
end NewCore
