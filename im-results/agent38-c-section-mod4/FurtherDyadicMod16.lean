import SectionMod8Predecessor
import DyadicResidualCriterion
import Lean.Elab.Tactic.Omega

namespace BB6Agent38
open BB6.Agent46

/-- A second independent depth class is unreachable in the one-left-counter
    halting basin: all depths congruent eight modulo sixteen. -/
theorem dyadic_one_depth_eight_mod16_excluded (k depth time : Nat)
    (hk : 4≤k)
    (hlevel : 2*k-3=haltLevel 4 depth)
    (hdepth : depth%16=8)
    (hr : BB6.Agent8Section.run secNext time (some (5,1))=some (1,k)) : False := by
  have hc := haltLevel_closed 4 depth
  have hrel : 2*k+3*depth+8=2^(depth+1)*8 := by omega
  have hdiv : 16 ∣ 2^(depth+1)*8 := by
    have h2 : 2 ∣ 2^(depth+1) := by
      change 2^1 ∣ 2^(depth+1)
      exact Nat.pow_dvd_pow 2 (by omega)
    rcases h2 with ⟨t,ht⟩
    refine ⟨t,?_⟩
    rw [ht]
    omega
  have hmod : (2*k+3*depth+8)%16=0 := by
    rw [hrel]
    exact Nat.mod_eq_zero_of_dvd hdiv
  have hk8 : k%8=0 := by omega
  exact blank_section_no_one8 time 1 k (by decide) hk8 hr

/-- A further whole depth-index class outside the original blank orbit:
    odd target a≡1 mod4, odd stopping level depth, and
    a+3*depth+4 ≡ 0 mod16. -/
theorem dyadic_odd_depth_mod16_excluded (a k depth time : Nat)
    (ha3 : 3≤a) (ha4 : a%4=1)
    (hdepth : depth%2=1)
    (hregion : a<2*k)
    (hlevel : 2*k-a+3=haltLevel (a-1) depth)
    (hindex : (a+3*depth+4)%16=0)
    (hr : BB6.Agent8Section.run secNext time (some (5,1))=some (a,k)) : False := by
  have hc := haltLevel_closed (a-1) depth
  have hsub : a-1+4=a+3 := by omega
  rw [hsub] at hc
  have hrel : 2*k+a+3*depth+4=2^(depth+1)*(a+3) := by omega
  have hdiv : 16 ∣ 2^(depth+1)*(a+3) := by
    by_cases h1 : depth=1
    · subst depth
      have h4 : 4 ∣ a+3 := Nat.dvd_of_mod_eq_zero (by omega)
      rcases h4 with ⟨t,ht⟩
      refine ⟨t,?_⟩
      rw [ht]
      change 4*(4*t)=16*t
      omega
    · have hge : 3≤depth := by omega
      have hp : 16 ∣ 2^(depth+1) := by
        change 2^4 ∣ 2^(depth+1)
        exact Nat.pow_dvd_pow 2 (by omega)
      rcases hp with ⟨t,ht⟩
      refine ⟨t*(a+3),?_⟩
      rw [ht]
      ac_rfl
  have hmod : (2*k+a+3*depth+4)%16=0 := by
    rw [hrel]
    exact Nat.mod_eq_zero_of_dvd hdiv
  have hk8 : k%8=0 := by omega
  exact blank_section_no_one8 time a k ha4 hk8 hr

/-- Exact blank-origin Machine C stopping iff a return reaches one of the
    remaining dyadic stopping input families after two-step mod8 pruning. -/
theorem blank_halts_iff_mod16_residual :
    BB6.CReachBridge.RunHalts ↔
      ∃ time a k : Nat,
        BB6.Agent8Section.run secNext time (some (5,1))=some (a,k) ∧
        ((a=1 ∧ 4≤k ∧
            ∃ depth, 2*k-3=haltLevel 4 depth ∧ depth%8≠2 ∧ depth%16≠8) ∨
         (3≤a ∧ a%2=1 ∧ a<2*k ∧
            ∃ depth, 2*k-a+3=haltLevel (a-1) depth ∧ depth%2=1 ∧
              a%8≠(3*depth)%8 ∧
              (a%4≠1 ∨ (a+3*depth+4)%16≠0))) := by
  rw [blank_halts_iff_mod8_residual]
  constructor
  · rintro ⟨time,a,k,hr,ht⟩
    refine ⟨time,a,k,hr,?_⟩
    rcases ht with ⟨ha,hk,depth,hlevel,h8⟩ |
      ⟨ha,hao,hrange,depth,hlevel,hodd,h8⟩
    · left
      refine ⟨ha,hk,depth,hlevel,h8,?_⟩
      intro h16
      subst a
      exact dyadic_one_depth_eight_mod16_excluded k depth time hk hlevel h16 hr
    · right
      refine ⟨ha,hao,hrange,depth,hlevel,hodd,h8,?_⟩
      by_cases h4 : a%4=1
      · right
        intro h16
        exact dyadic_odd_depth_mod16_excluded a k depth time ha h4 hodd
          hrange hlevel h16 hr
      · exact Or.inl h4
  · rintro ⟨time,a,k,hr,ht⟩
    refine ⟨time,a,k,hr,?_⟩
    rcases ht with ⟨ha,hk,depth,hlevel,h8,_⟩ |
      ⟨ha,hao,hrange,depth,hlevel,hodd,h8,_⟩
    · exact Or.inl ⟨ha,hk,depth,hlevel,h8⟩
    · exact Or.inr ⟨ha,hao,hrange,depth,hlevel,hodd,h8⟩

#print axioms dyadic_one_depth_eight_mod16_excluded
#print axioms dyadic_odd_depth_mod16_excluded
#print axioms blank_halts_iff_mod16_residual

end BB6Agent38
