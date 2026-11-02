import GatewayRefinement
import GateArithmeticEight
import SectionMod8

namespace Agent20Gate
open BB6.Agent46

/-- Every low-branch exponent m=4 mod 8 is excluded from the authentic
    blank-origin section orbit using the source-verified infinite inverse cone. -/
theorem low_family_four_unreachable (m k t : Nat)
    (he : k+3*m+4=2^(2*m+3)) (hm : m%8=4) :
    BB6.Agent8Section.run secNext t (some (5,1)) ≠ some (1,k) := by
  intro hr
  have hkMod := low_m_four_mod_eight m k he hm
  have hs : secNext (1,k)=none :=
    (BB6.Agent15.section_halts_iff_parametric 1 k).mpr
      (Or.inr (Or.inl ⟨rfl,m,he⟩))
  have hkFour : 4≤k := by
    rcases (BB6.Agent15.section_halts_iff_diophantine 1 k).mp hs with h0|h1|h2
    · omega
    · exact h1.2.1
    · omega
  have hkEight : 8≤k := by omega
  let v := k/8-1
  have hy : 8*(v+1)=k := by dsimp [v]; omega
  have htarget : BB6.Agent8Section.run secNext t (some (5,1)) =
      some (4*0+1,8*(v+1)) := by
    simpa only [Nat.zero_mul,Nat.zero_add,hy] using hr
  exact BB6.Agent15.blank_no_one_eight_family t 0 v htarget

/-- Every higher-branch parameter pair m even, j+3m=3 mod 8 is excluded. -/
theorem high_family_eight_unreachable (j m k t : Nat)
    (he : k+j+3*m+5=2^(2*m+2)*(j+3))
    (hm : m%2=0) (hj : (j+3*m)%8=3) :
    BB6.Agent8Section.run secNext t (some (5,1)) ≠ some (2*j+3,k) := by
  intro hr
  have ⟨hjOdd,hkMod⟩ := high_m_even_mod_eight j m k he hm hj
  have hs : secNext (2*j+3,k)=none :=
    (BB6.Agent15.section_halts_iff_parametric (2*j+3) k).mpr
      (Or.inr (Or.inr ⟨j,m,rfl,he⟩))
  have hLow : 2*j+3<2*k := by
    rcases (BB6.Agent15.section_halts_iff_diophantine (2*j+3) k).mp hs with h0|h1|h2
    · omega
    · omega
    · exact h2.2.2.1
  have hkEight : 8≤k := by omega
  let u := (j+1)/2
  let v := k/8-1
  have hx : 4*u+1=2*j+3 := by dsimp [u]; omega
  have hy : 8*(v+1)=k := by dsimp [v]; omega
  have htarget : BB6.Agent8Section.run secNext t (some (5,1)) =
      some (4*u+1,8*(v+1)) := by
    rw [hx,hy]
    exact hr
  exact BB6.Agent15.blank_no_one_eight_family t u v htarget

/-- Exact four-sector removal from the Machine C blank-halting criterion.
    The surviving infinite parameter families are unresolved. -/
theorem blank_halts_iff_refined_eight :
    BB6.CReachBridge.RunHalts ↔
      ∃ t a k,
        BB6.Agent8Section.run secNext t (some (5,1))=some (a,k) ∧
        ((a=1 ∧ ∃ m, m%4≠1 ∧ m%8≠4 ∧ k+3*m+4=2^(2*m+3)) ∨
         (∃ j m, a=2*j+3 ∧ (j+m)%4≠0 ∧
           (m%2≠0 ∨ (j+3*m)%8≠3) ∧
           k+j+3*m+5=2^(2*m+2)*(j+3))) := by
  constructor
  · intro h
    obtain ⟨t,a,k,hr,hgate⟩ := blank_halts_iff_refined.mp h
    refine ⟨t,a,k,hr,?_⟩
    rcases hgate with ⟨ha,m,hm4,he⟩ | ⟨j,m,ha,hm4,he⟩
    · subst a
      refine Or.inl ⟨rfl,m,hm4,?_,he⟩
      intro hm8
      exact low_family_four_unreachable m k t he hm8 hr
    · subst a
      refine Or.inr ⟨j,m,rfl,hm4,?_,he⟩
      by_cases hm2 : m%2=0
      · right
        intro hj8
        exact high_family_eight_unreachable j m k t he hm2 hj8 hr
      · exact Or.inl hm2
  · rintro ⟨t,a,k,hr,hgate⟩
    apply blank_halts_iff_refined.mpr
    refine ⟨t,a,k,hr,?_⟩
    rcases hgate with ⟨ha,m,hm4,_,he⟩ | ⟨j,m,ha,hm4,_,he⟩
    · exact Or.inl ⟨ha,m,hm4,he⟩
    · exact Or.inr ⟨j,m,ha,hm4,he⟩

#print axioms low_family_four_unreachable
#print axioms high_family_eight_unreachable
#print axioms blank_halts_iff_refined_eight
end Agent20Gate
