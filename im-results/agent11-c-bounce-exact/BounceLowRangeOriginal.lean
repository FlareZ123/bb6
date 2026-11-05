import BounceEvenThreeOriginal
import Lean.Elab.Tactic.Omega

namespace BB6.Agent46

/-- Every successful odd-middle bounce has right output at least four,
    at any recursion depth. -/
theorem bounce_odd_min_four (c:Nat):∀ K x y:Nat,
    K%2=1 → (bounce K c).2=some (x,y) → 4≤y := by
  induction c using Nat.strongRecOn with
  | ind c ih =>
      intro K x y hk hout
      rw [bounce.eq_1] at hout
      by_cases hc:c<4
      · simp [hc] at hout
      simp only [hc,ite_false,hk,ite_true] at hout
      by_cases hsmall:c≤2*K+6
      · simp only [hsmall,ite_true,Option.some.injEq,Prod.mk.injEq] at hout
        omega
      simp only [hsmall,ite_false] at hout
      have hlt:c-(2*K+3)<c := Nat.sub_lt (by omega) (by omega)
      have hk':(2*K+3)%2=1 := by omega
      exact ih (c-(2*K+3)) hlt (2*K+3) x y hk' hout

/-- The even-middle bounce has the exceptional right output three,
    or else right output at least five; four is impossible. -/
theorem bounce_even_three_or_high (c:Nat):∀ K x y:Nat,
    K%2=0 → (bounce K c).2=some (x,y) → y=3 ∨ 5≤y := by
  induction c using Nat.strongRecOn with
  | ind c ih =>
      intro K x y hk hout
      rw [bounce.eq_1] at hout
      by_cases hc:c<4
      · simp [hc] at hout
      simp only [hc,ite_false,hk] at hout
      simp only [Nat.reduceEqDiff,ite_false] at hout
      by_cases hc4:c=4
      · simp only [hc4,ite_true,Option.some.injEq,Prod.mk.injEq] at hout
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
      exact ih (c-(2*K+5)) hlt (2*K+4) x y hk' hout

#print axioms bounce_odd_min_four
#print axioms bounce_even_three_or_high
end BB6.Agent46
