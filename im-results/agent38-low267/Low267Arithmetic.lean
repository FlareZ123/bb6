import Std
import Lean.Elab.Tactic.Omega

namespace BB6.Agent38Low267

theorem pow_two_ne_odd_high (q n : Nat) : (2:Nat)^n ≠ 116*q+59 := by
  cases n with
  | zero => simp
  | succ n =>
    rw [Nat.pow_succ]
    omega

theorem no_zero_branch (q n : Nat) (hs : 928*q+472=2^n*8) : False := by
  have h : 2^n=116*q+59 := by omega
  exact pow_two_ne_odd_high q n h

theorem even_bounce_depth (q a k n : Nat)
    (ha : a%2=0)
    (hs : 928*q+472=2^(n+1)*(a+2))
    (hc : 2*k+a+7+3*n=1024*q+520) :
    a=232*q+116 ∧ k=396*q+197 := by
  have hnodd : n%2=1 := by omega
  have hnlt : n<2 := by
    by_cases hn : n<2
    · exact hn
    · exfalso
      have h4 : (2:Nat)^4 ∣ (2:Nat)^(n+2) := Nat.pow_dvd_pow 2 (by omega)
      rcases h4 with ⟨z,hz⟩
      obtain ⟨v,hv⟩ : ∃ v, a+2=2*v := ⟨a/2+1, by omega⟩
      have hpow : (2:Nat)^(n+2)=2^(n+1)*2 := by
        simpa only [show n+2=(n+1)+1 by omega] using (Nat.pow_succ 2 (n+1))
      have hp : 2^(n+1)*(a+2)=(2:Nat)^(n+2)*v := by
        rw [hv,hpow]
        ac_rfl
      have hsum4 : 16 ∣ 928*q+472 := by
        rw [hs,hp,hz]
        refine ⟨z*v, ?_⟩
        simp only [show (2:Nat)^4=16 by decide]
        ac_rfl
      rcases hsum4 with ⟨t,ht⟩
      omega
  have hn : n=1 := by omega
  subst n
  simp only [show (2:Nat)^(1+1)=4 by decide] at hs
  omega

theorem even_bounce_generic (q a k n : Nat)
    (ha2 : 2≤a) (ha : a%2=0) (hregion : a<2*k)
    (hs : 928*q+472=2^n*(2*(a-1)+6))
    (hc : (2*k-a+3)+(2*(a-1)+6)+3*n=1024*q+520) :
    a=232*q+116 ∧ k=396*q+197 := by
  have hs' : 928*q+472=2^(n+1)*(a+2) := by
    rw [show 2*(a-1)+6=2*(a+2) by omega] at hs
    rw [Nat.pow_succ]
    calc
      928*q+472=2^n*(2*(a+2)) := hs
      _=(2^n*2)*(a+2) := by ac_rfl
  have hc' : 2*k+a+7+3*n=1024*q+520 := by omega
  exact even_bounce_depth q a k n ha hs' hc'

#print axioms even_bounce_generic
end BB6.Agent38Low267
