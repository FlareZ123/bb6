import BouncePowerOdd
import Lean.Elab.Tactic.Omega
namespace BB6.Agent3
open BB6.Agent46

theorem bounce_even_sum_power (c k x y : Nat)
    (hk : k%2=0) (h : (bounce k c).2=some (x,y)) (hy:4≤y) :
    ∃ n : Nat, x+y+1 = 2^n * (2*k+8) := by
  induction c using Nat.strongRecOn generalizing k x y with
  | ind c ih =>
    by_cases hlow : c<4
    · simp [bounce,hlow] at h
    · by_cases h4 : c=4
      · subst c
        have heq : (x,y)=(2*k+2,3) := by
          have hh:=h
          rw [bounce] at hh
          simp only [if_neg hlow,if_neg (by omega : ¬ k%2=1),if_pos rfl] at hh
          exact Option.some.inj hh.symm
        cases Prod.mk.inj heq with
        | intro hx hyEq =>
          subst x;subst y
          omega
      · by_cases h5 : c=5
        · simp [bounce,hlow,hk,h4,h5] at h
        · by_cases hsmall : c≤2*k+8
          · have heq : (x,y)=(2*k+8-c,c-1) := by
              have hh:=h
              rw [bounce] at hh
              simp only [if_neg hlow,if_neg (by omega : ¬ k%2=1),if_neg h4,if_neg h5,if_pos hsmall] at hh
              exact Option.some.inj hh.symm
            cases Prod.mk.inj heq with
            | intro hx hyEq =>
              subst x;subst y
              refine ⟨0,?_⟩
              simp
              omega
          · have hlt : c-(2*k+5)<c := by omega
            have hh : (bounce (2*k+4) (c-(2*k+5))).2=some (x,y) := by
              have hc:=h
              rw [bounce] at hc
              simpa only [if_neg hlow,if_neg (by omega : ¬ k%2=1),if_neg h4,if_neg h5,if_neg hsmall] using hc
            obtain ⟨n,hn⟩ := ih _ hlt (2*k+4) x y (by omega) hh hy
            refine ⟨n+1, ?_⟩
            calc
              x+y+1 = 2^n * (2*(2*k+4)+8) := hn
              _ = 2^n * (2*(2*k+8)) := by congr 1
              _ = 2^(n+1) * (2*k+8) := by
                simp [Nat.pow_succ, Nat.mul_assoc]

#print axioms bounce_even_sum_power
end BB6.Agent3
