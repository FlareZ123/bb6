import BounceCalc
import Lean.Elab.Tactic.Omega

namespace BB6.Agent46

/-- Exact additive cost and counter-height parity for the previously exceptional
    y=3 even-middle bounce exit. The recursion depth n is unbounded. -/
theorem bounce_even_three_cost (c : Nat) :
    ∀ K x : Nat, K%2=0 → (bounce K c).2=some (x,3) →
      ∃n : Nat, c+2*K+4+3*n=x+6 ∧ (c+n)%2=0 := by
  induction c using Nat.strongRecOn with
  | ind c ih =>
      intro K x hK hout
      rw [bounce.eq_1] at hout
      by_cases hc : c<4
      · simp [hc] at hout
      simp only [hc,ite_false,hK] at hout
      simp only [Nat.reduceEqDiff,ite_false] at hout
      by_cases h4 : c=4
      · simp only [h4,ite_true,Option.some.injEq,Prod.mk.injEq] at hout
        refine ⟨0,?_,?_⟩
        · omega
        · omega
      simp only [h4,ite_false] at hout
      by_cases h5 : c=5
      · simp [h5] at hout
      simp only [h5,ite_false] at hout
      by_cases hd : c≤2*K+8
      · simp only [hd,ite_true,Option.some.injEq,Prod.mk.injEq] at hout
        omega
      simp only [hd,ite_false] at hout
      have hlt : c-(2*K+5)<c := Nat.sub_lt (by omega) (by omega)
      have hK' : (2*K+4)%2=0 := by omega
      obtain ⟨n, hcost, hpar⟩ :=
        ih (c-(2*K+5)) hlt (2*K+4) x hK' hout
      refine ⟨n+1,?_,?_⟩
      · have hsub : c-(2*K+5)+(2*K+5)=c := by omega
        omega
      · have hsub : c-(2*K+5)+(2*K+5)=c := by omega
        omega

/-- Even-middle bounce success always exits with y≥3. -/
theorem bounce_even_y_ge_three (c : Nat) :
    ∀ K x y : Nat, K%2=0 → (bounce K c).2=some (x,y) → 3≤y := by
  induction c using Nat.strongRecOn with
  | ind c ih =>
      intro K x y hK hout
      rw [bounce.eq_1] at hout
      by_cases hc : c<4
      · simp [hc] at hout
      simp only [hc,ite_false,hK] at hout
      simp only [Nat.reduceEqDiff,ite_false] at hout
      by_cases h4 : c=4
      · simp only [h4,ite_true,Option.some.injEq,Prod.mk.injEq] at hout
        omega
      simp only [h4,ite_false] at hout
      by_cases h5 : c=5
      · simp [h5] at hout
      simp only [h5,ite_false] at hout
      by_cases hd : c≤2*K+8
      · simp only [hd,ite_true,Option.some.injEq,Prod.mk.injEq] at hout
        omega
      simp only [hd,ite_false] at hout
      have hlt : c-(2*K+5)<c := Nat.sub_lt (by omega) (by omega)
      exact ih (c-(2*K+5)) hlt (2*K+4) x y (by omega) hout

#print axioms bounce_even_y_ge_three
#print axioms bounce_even_three_cost
end BB6.Agent46
