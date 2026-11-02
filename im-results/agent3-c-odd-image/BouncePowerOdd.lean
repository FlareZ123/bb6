import Agent3CImage
import Lean.Elab.Tactic.Omega
namespace BB6.Agent3
open BB6.Agent46

theorem bounce_odd_sum_power (c k x y : Nat)
    (hk : k%2=1) (h : (bounce k c).2=some (x,y)) :
    ∃ n : Nat, x+y = 2^n * (2*k+6) := by
  induction c using Nat.strongRecOn generalizing k x y with
  | ind c ih =>
    by_cases hlow : c<4
    · simp [bounce,hlow] at h
    · by_cases hsmall : c≤2*k+6
      · have heq : (x,y)=(2*k+6-c,c) := by
          have hh:=h
          rw [bounce] at hh
          simp only [if_neg hlow,if_pos hk,if_pos hsmall] at hh
          exact Option.some.inj hh.symm
        cases Prod.mk.inj heq with
        | intro hx hyEq =>
          subst x; subst y
          refine ⟨0, ?_⟩
          simp
          omega
      · have hlt : c-(2*k+3)<c := by omega
        have hh : (bounce (2*k+3) (c-(2*k+3))).2=some (x,y) := by
          have hc:=h
          rw [bounce] at hc
          simpa only [if_neg hlow,if_pos hk,if_neg hsmall] using hc
        obtain ⟨n,hn⟩ := ih _ hlt (2*k+3) x y (by omega) hh
        refine ⟨n+1, ?_⟩
        calc
          x+y = 2^n * (2*(2*k+3)+6) := hn
          _ = 2^n * (2*(2*k+6)) := by congr 1
          _ = 2^(n+1) * (2*k+6) := by
            simp [Nat.pow_succ, Nat.mul_assoc]

#print axioms bounce_odd_sum_power
end BB6.Agent3
