import BounceEvenExact
import Lean.Elab.Tactic.Omega

namespace BB6.Agent46

/-- Special even-bounce inverse lift for the exceptional low y=3 output. -/
theorem bounce_three_lift (k n:Nat) (hk:k%2=0) :
    (bounce k (invLiftC k n 3)).2=(bounce (invLiftK k n) 4).2 := by
  induction n generalizing k with
  | zero => simp [invLiftC,invLiftK]
  | succ n ih =>
      have hC:4≤invLiftC (2*k+4) n 3 := by
        have hh:=invLiftC_lower (2*k+4) n 3
        omega
      have hlow: ¬(2*k+5+invLiftC (2*k+4) n 3<4) := by omega
      have hodd:k%2≠1 := by omega
      have h4:2*k+5+invLiftC (2*k+4) n 3 ≠ 4 := by omega
      have h5:2*k+5+invLiftC (2*k+4) n 3 ≠ 5 := by omega
      have hhigh: ¬(2*k+5+invLiftC (2*k+4) n 3≤2*k+8) := by omega
      simp only [invLiftC,invLiftK]
      rw [bounce]
      simp only [if_neg hlow,if_neg hodd,if_neg h4,if_neg h5,if_neg hhigh]
      have hsub:2*k+5+invLiftC (2*k+4) n 3-(2*k+5)=
          invLiftC (2*k+4) n 3 := by omega
      rw [hsub]
      exact ih (2*k+4) (by omega)

private theorem invLiftK_even_three (K n:Nat) (hk:K%2=0) :
    (invLiftK K n)%2=0 := by
  induction n generalizing K with
  | zero => simpa [invLiftK] using hk
  | succ n ih => simpa only [invLiftK] using ih (2*K+4) (by omega)

/-- Any satisfying low-output equations have a genuine original even bounce. -/
theorem bounce_three_sufficient (K c x n:Nat) (hk:K%2=0)
   (hs:x+6=2^n*(2*K+8))
   (hc:c+(2*K+6)+3*n=x+8) :
    (bounce K c).2=some (x,3) := by
  have hpow:2^(n+1)*(K+4)=x+6 := by
    calc
      2^(n+1)*(K+4)=2^n*2*(K+4) := by rw [Nat.pow_succ]
      _=2^n*(2*(K+4)) := by ac_rfl
      _=2^n*(2*K+8) := by congr 1 <;> omega
      _=x+6 := hs.symm
  have hin:invLiftC K n 3=c := by
    have hh:=invLiftC_closed K n 3
    rw [hpow] at hh
    omega
  rw [←hin, bounce_three_lift K n hk]
  have heven:(invLiftK K n)%2=0 := invLiftK_even_three K n hk
  have hterm:2*(invLiftK K n)+2=x := by
    have hh:=invLiftK_closed K n
    have hS:2*(invLiftK K n)+8=2^n*(2*K+8) := by
      calc
        2*(invLiftK K n)+8=2*(2^n*(K+4)) := by omega
        _=2^n*(2*(K+4)) := by ac_rfl
        _=2^n*(2*K+8) := by congr 1 <;> omega
    omega
  have h4: ¬(4<4) := by decide
  have hodd : (invLiftK K n)%2≠1 := by omega
  simp [bounce,h4,hodd,hterm]

/-- Exact necessary equations also hold across arbitrarily many recursions. -/
theorem bounce_three_invariants (c:Nat) : ∀ K x:Nat,
  K%2=0 → (bounce K c).2=some (x,3) →
  ∃ n:Nat, x+6=2^n*(2*K+8) ∧ c+(2*K+6)+3*n=x+8 := by
  induction c using Nat.strongRecOn with
  | ind c ih =>
      intro K x hk hout
      rw [bounce.eq_1] at hout
      by_cases hc:c<4
      · simp [hc] at hout
      simp only [hc,ite_false,hk] at hout
      simp only [Nat.reduceEqDiff,ite_false] at hout
      have hodd:K%2≠1 := by omega
      by_cases hc4:c=4
      · simp only [hc4,ite_true,Option.some.injEq,Prod.mk.injEq] at hout
        cases hout with
        | intro hx hy =>
          subst x
          refine ⟨0,by simp,?_⟩
          simp
          omega
      simp only [hc4,ite_false] at hout
      by_cases hc5:c=5
      · simp [hc5] at hout
      simp only [hc5,ite_false] at hout
      by_cases hs:c≤2*K+8
      · simp only [hs,ite_true,Option.some.injEq,Prod.mk.injEq] at hout
        omega
      simp only [hs,ite_false] at hout
      have hlt:c-(2*K+5)<c := Nat.sub_lt (by omega) (by omega)
      have hk':(2*K+4)%2=0 := by omega
      obtain ⟨n,hsum,hcost⟩:=ih (c-(2*K+5)) hlt (2*K+4) x hk' hout
      refine ⟨n+1,?_,?_⟩
      · calc
          x+6=2^n*(2*(2*K+4)+8) := hsum
          _=2^n*(2*(2*K+8)) := by congr 1
          _=(2^n*2)*(2*K+8) := by ac_rfl
          _=2^(n+1)*(2*K+8) := by rw [Nat.pow_succ]
      · have hsub:c-(2*K+5)+(2*K+5)=c := by omega
        omega

/-- Exact source-compatible low y=3 even-bounce inverse, any depth. -/
theorem bounce_three_exact (K c x:Nat) (hk:K%2=0):
  (bounce K c).2=some (x,3) ↔
    ∃ n:Nat, x+6=2^n*(2*K+8) ∧ c+(2*K+6)+3*n=x+8 := by
  constructor
  · exact bounce_three_invariants c K x hk
  · rintro ⟨n,hs,hc⟩
    exact bounce_three_sufficient K c x n hk hs hc

#print axioms bounce_three_exact
end BB6.Agent46
