import Std
import Lean.Elab.Tactic.Omega

namespace BB6.Agent38Low259

theorem pow_two_not_div_five (n : Nat) : (2:Nat)^n % 5 ≠ 0 := by
  induction n with
  | zero => decide
  | succ n ih =>
    have h : (2:Nat)^(n+1) % 5 = (((2:Nat)^n % 5)*2)%5 := by
      rw [Nat.pow_succ, Nat.mul_mod]
    rw [h]
    have hb := Nat.mod_lt ((2:Nat)^n) (by decide : 0<5)
    omega

theorem sum_even_bounce_depth (q a k n : Nat)
    (ha : a%2=0)
    (hs : 640*q+320=2^(n+1)*(a+2))
    (hc : 2*k+a+7+3*n=1024*q+512) :
    (a=160*q+78 ∧ k=432*q+212) ∨
    (a=40*q+18 ∧ k=492*q+239) := by
  have hnodd : n%2=1 := by omega
  have hnlt : n < 5 := by
    by_cases hn : n < 5
    · exact hn
    · exfalso
      have h7 : (2:Nat)^7 ∣ (2:Nat)^(n+2) := Nat.pow_dvd_pow 2 (by omega)
      rcases h7 with ⟨z,hz⟩
      obtain ⟨v,hv⟩ : ∃ v, a+2=2*v := ⟨a/2+1, by omega⟩
      have hpow : (2:Nat)^(n+2)=2^(n+1)*2 := by
        simpa only [show n+2=(n+1)+1 by omega] using (Nat.pow_succ 2 (n+1))
      have hp : 2^(n+1)*(a+2)=(2:Nat)^(n+2)*v := by
        rw [hv,hpow]
        ac_rfl
      have hsum7 : 128 ∣ 640*q+320 := by
        rw [hs,hp,hz]
        refine ⟨z*v, ?_⟩
        simp only [show (2:Nat)^7=128 by decide]
        ac_rfl
      rcases hsum7 with ⟨t,ht⟩
      omega
  have hn : n=1 ∨ n=3 := by omega
  rcases hn with h1 | h3
  · left
    subst n
    simp only [show (2:Nat)^(1+1)=4 by decide] at hs
    omega
  · right
    subst n
    simp only [show (2:Nat)^(3+1)=16 by decide] at hs
    omega

theorem generic_even_bounce_inverse (q a k n : Nat)
    (ha2 : 2 ≤ a) (ha : a%2=0) (hregion : a<2*k)
    (hs : 640*q+320=2^n*(2*(a-1)+6))
    (hc : (2*k-a+3)+(2*(a-1)+6)+3*n=1024*q+512) :
    (a=160*q+78 ∧ k=432*q+212) ∨
    (a=40*q+18 ∧ k=492*q+239) := by
  have hs' : 640*q+320=2^(n+1)*(a+2) := by
    rw [show 2*(a-1)+6=2*(a+2) by omega] at hs
    rw [Nat.pow_succ]
    calc
      640*q+320=2^n*(2*(a+2)) := hs
      _=(2^n*2)*(a+2) := by ac_rfl
  have hc' : 2*k+a+7+3*n=1024*q+512 := by omega
  exact sum_even_bounce_depth q a k n ha hs' hc'

theorem pow_no_zero_branch (q n : Nat)
    (h : 640*q+320=8*(2:Nat)^n) : False := by
  have hp : (2:Nat)^n %5 ≠0 := pow_two_not_div_five n
  let p := (2:Nat)^n
  change p%5≠0 at hp
  change 640*q+320=8*p at h
  have hz : p%5=0 := by omega
  exact hp hz

#print axioms pow_no_zero_branch
#print axioms generic_even_bounce_inverse
end BB6.Agent38Low259
