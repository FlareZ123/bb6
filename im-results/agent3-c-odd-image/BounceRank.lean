import Agent3CImage
import Lean.Elab.Tactic.Omega
namespace BB6.Agent3
open BB6.Agent46

/-- All successful bounces strictly grow a linear input/output potential. -/
theorem bounce_rank (c k x y : Nat)
    (hb : (bounce k c).2=some (x,y)) :
    c+2*k+4 ≤ x+2*y := by
  induction c using Nat.strongRecOn generalizing k x y with
  | ind c ih =>
    by_cases hlow : c<4
    · simp [bounce,hlow] at hb
    · by_cases hk : k%2=1
      · by_cases hsmall : c≤2*k+6
        · have heq : (x,y)=(2*k+6-c,c) := by
            have hh:=hb
            rw [bounce] at hh
            simp only [if_neg hlow,if_pos hk,if_pos hsmall] at hh
            exact Option.some.inj hh.symm
          cases Prod.mk.inj heq with
          | intro hx hy =>
            subst x; subst y
            omega
        · have hlt : c-(2*k+3)<c := by omega
          have hh : (bounce (2*k+3) (c-(2*k+3))).2=some (x,y) := by
            have hc:=hb
            rw [bounce] at hc
            simpa only [if_neg hlow,if_pos hk,if_neg hsmall] using hc
          have hi := ih _ hlt (2*k+3) x y hh
          omega
      · by_cases h4 : c=4
        · subst c
          have heq : (x,y)=(2*k+2,3) := by
            have hh:=hb
            rw [bounce] at hh
            simp only [if_neg hlow,if_neg hk,if_pos rfl] at hh
            exact Option.some.inj hh.symm
          cases Prod.mk.inj heq with
          | intro hx hy =>
            subst x;subst y
            omega
        · by_cases h5 : c=5
          · simp [bounce,hlow,hk,h4,h5] at hb
          · by_cases hsmall : c≤2*k+8
            · have heq : (x,y)=(2*k+8-c,c-1) := by
                have hh:=hb
                rw [bounce] at hh
                simp only [if_neg hlow,if_neg hk,if_neg h4,if_neg h5,if_pos hsmall] at hh
                exact Option.some.inj hh.symm
              cases Prod.mk.inj heq with
              | intro hx hy =>
                subst x;subst y
                omega
            · have hlt : c-(2*k+5)<c := by omega
              have hh : (bounce (2*k+4) (c-(2*k+5))).2=some (x,y) := by
                have hc:=hb
                rw [bounce] at hc
                simpa only [if_neg hlow,if_neg hk,if_neg h4,if_neg h5,if_neg hsmall] using hc
              have hi := ih _ hlt (2*k+4) x y hh
              omega

#print axioms bounce_rank
end BB6.Agent3
