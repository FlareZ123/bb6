import BounceCalc
import Lean.Elab.Tactic.Omega

namespace BB6.Agent46

/-- For an odd bounce, a successful output simultaneously determines
    a power-of-two sum and an exact cumulative counter cost. -/
theorem bounce_odd_output_invariants (c : Nat) :
    ∀ k x y : Nat, k%2=1 → (bounce k c).2=some (x,y) →
      ∃ n : Nat, x+y = 2^n * (2*k+6) ∧
        c + (2*k+6) + 3*n = x+2*y := by
  induction c using Nat.strongRecOn with
  | ind c ih =>
    intro k x y hk hout
    rw [bounce.eq_1] at hout
    by_cases hc : c<4
    · simp [hc] at hout
    simp only [hc, ite_false, hk, ite_true] at hout
    by_cases hd : c≤2*k+6
    · simp only [hd, ite_true, Option.some.injEq,
        Prod.mk.injEq] at hout
      rcases hout with ⟨hx,hy⟩
      subst x
      subst y
      refine ⟨0, ?_, ?_⟩
      · simp
        omega
      · simp
        omega
    · simp only [hd, ite_false] at hout
      have hbig : 2*k+6 < c := by omega
      have hlt : c-(2*k+3) < c := Nat.sub_lt (by omega) (by omega)
      have hk' : (2*k+3)%2=1 := by omega
      obtain ⟨n, hsum, hcost⟩ :=
        ih (c-(2*k+3)) hlt (2*k+3) x y hk' hout
      refine ⟨n+1, ?_, ?_⟩
      · calc
          x+y = 2^n * (2*(2*k+3)+6) := hsum
          _ = 2^n * (2 * (2*k+6)) := by congr 1
          _ = (2^n * 2) * (2*k+6) := by rw [Nat.mul_assoc]
          _ = 2^(n+1) * (2*k+6) := by rw [Nat.pow_succ]
      · have hsub : c-(2*k+3)+(2*k+3)=c := by omega
        omega

/-- The even-bounce cost and sum law, including arbitrarily deep
    recursion. The exceptional c=4 exit has y=3 and is excluded. -/
theorem bounce_even_output_invariants (c : Nat) :
    ∀ k x y : Nat, k%2=0 → 4≤y → (bounce k c).2=some (x,y) →
      ∃ n : Nat, x+y+1 = 2^n * (2*k+8) ∧
        c + (2*k+8) + 3*n = x+2*y+2 := by
  induction c using Nat.strongRecOn with
  | ind c ih =>
    intro k x y hk hy hout
    rw [bounce.eq_1] at hout
    by_cases hc : c<4
    · simp [hc] at hout
    simp only [hc, ite_false, hk] at hout
    simp only [Nat.reduceEqDiff, ite_false] at hout
    by_cases hc4 : c=4
    · simp only [hc4, ite_true, Option.some.injEq,
        Prod.mk.injEq] at hout
      omega
    simp only [hc4, ite_false] at hout
    by_cases hc5 : c=5
    · simp [hc5] at hout
    simp only [hc5, ite_false] at hout
    by_cases hd : c≤2*k+8
    · simp only [hd, ite_true, Option.some.injEq,
        Prod.mk.injEq] at hout
      rcases hout with ⟨hx,hy'⟩
      subst x
      subst y
      refine ⟨0, ?_, ?_⟩
      · simp
        omega
      · simp
        omega
    · simp only [hd, ite_false] at hout
      have hbig : 2*k+8<c := by omega
      have hlt : c-(2*k+5)<c := Nat.sub_lt (by omega) (by omega)
      have hk' : (2*k+4)%2=0 := by omega
      obtain ⟨n, hsum, hcost⟩ :=
        ih (c-(2*k+5)) hlt (2*k+4) x y hk' hy hout
      refine ⟨n+1, ?_, ?_⟩
      · calc
          x+y+1 = 2^n * (2*(2*k+4)+8) := hsum
          _ = 2^n * (2*(2*k+8)) := by congr 1
          _ = (2^n*2)*(2*k+8) := by rw [Nat.mul_assoc]
          _ = 2^(n+1)*(2*k+8) := by rw [Nat.pow_succ]
      · have hsub : c-(2*k+5)+(2*k+5)=c := by omega
        omega

#print axioms bounce_odd_output_invariants
#print axioms bounce_even_output_invariants
end BB6.Agent46
