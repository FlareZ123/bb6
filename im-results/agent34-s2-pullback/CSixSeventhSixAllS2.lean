import CSixSeventhSixAll
import CSixSeventhS2Pullback
import Lean.Elab.Tactic.Omega

set_option maxRecDepth 8192
set_option maxHeartbeats 1000000

namespace BB6.Agent34S2Pullback

/-- The latest six-all high predicate with both S2 and complementary q-even
    high-stop cylinders removed. The low branch is unchanged. -/
def highAllowedAllS2Q (j m : Nat) : Prop :=
  BB6.Agent11SixAll.highAllowed j m ∧
  ¬(j%512=319 ∧ (3*m+102921)%131072=(185*j)%131072) ∧
  ¬(j%512=319 ∧ (171*m+355585)%1048576=(49*j)%1048576)

/-- Exact original-source blank-halting iff after adding the two new
    all-time high-stop root exclusions to the latest six-all criterion. -/
theorem blank_halts_iff_six_both_s2q :
    BB6.CReachBridge.RunHalts ↔
      (∃ m, BB6.Agent11SixAll.lowAllowed m ∧
        BB6.Agent11SixForced.sixForcedRootDecision
          1 (2^(2*m+3)-(3*m+4))=true) ∨
      (∃ j m, highAllowedAllS2Q j m ∧
        BB6.Agent11SixForced.sixForcedRootDecision
          (2*j+3) (highK j m)=true) := by
  rw [BB6.Agent11SixAll.blank_halts_iff_six_both]
  constructor
  · rintro (hlow | ⟨j,m,hprior,hroot⟩)
    · exact Or.inl hlow
    · let k := highK j m
      have hreach : BB6.Agent3.CReach (2*j+3) k :=
        (BB6.Agent11SixForced.sixForcedRootDecision_iff
          (2*j+3) k).mp hroot
      have hnotS2 :
          ¬(j%512=319 ∧
            (3*m+102921)%131072=(185*j)%131072) := by
        rintro ⟨hj,hcong⟩
        have hm := (s2_parameter_pullback_iff j m).1 ⟨hj,hcong⟩
        exact s2_high_parameter_not_CReach j m hj hm.2 hreach
      have hnotQ :
          ¬(j%512=319 ∧
            (171*m+355585)%1048576=(49*j)%1048576) := by
        rintro ⟨hj,hcong⟩
        have hm := (q_even_parameter_pullback_iff j m).1 ⟨hj,hcong⟩
        exact q_even_high_parameter_not_CReach j m hj hm.2 hreach
      exact Or.inr ⟨j,m,⟨hprior,hnotS2,hnotQ⟩,hroot⟩
  · rintro (hlow | ⟨j,m,⟨hprior,_,_⟩,hroot⟩)
    · exact Or.inl hlow
    · exact Or.inr ⟨j,m,hprior,hroot⟩

#print axioms highAllowedAllS2Q
#print axioms blank_halts_iff_six_both_s2q

end BB6.Agent34S2Pullback
