import CSixthSixSevenPullback
import CFifthSixSevenLatest
import Lean.Elab.Tactic.Omega

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace BB6.Agent12SevenSixthLatest

def highAllowedA12Four (j m : Nat) : Prop :=
  BB6.Agent12SevenFifthLatest.highAllowedA12Three j m ∧
  ¬(j%512=319 ∧ (3*m+71*j+57097)%65536=0)

theorem blank_halts_iff_after_a12_four :
    BB6.CReachBridge.RunHalts ↔
      (∃ m, BB6.Agent11SixAll.lowAllowed m ∧
        BB6.Agent11SixForced.sixForcedRootDecision 1
          (2^(2*m+3)-(3*m+4))=true) ∨
      (∃ j m, highAllowedA12Four j m ∧
        BB6.Agent11SixForced.sixForcedRootDecision (2*j+3)
          (2^(2*m+2)*(j+3)-(j+3*m+5))=true) := by
  rw [BB6.Agent12SevenFifthLatest.blank_halts_iff_after_a12_three]
  constructor
  · rintro (hlow | ⟨j,m,hprior,hroot⟩)
    · exact Or.inl hlow
    · let k := (2:Nat)^(2*m+2)*(j+3)-(j+3*m+5)
      have hreach : BB6.Agent3.CReach (2*j+3) k :=
        (BB6.Agent11SixForced.sixForcedRootDecision_iff
          (2*j+3) k).mp hroot
      have hnot :
          ¬(j%512=319 ∧ (3*m+71*j+57097)%65536=0) := by
        rintro ⟨hjmod,hcong⟩
        obtain ⟨time,hrun⟩ := hreach
        exact
          BB6.Agent12SevenSixthPullback.blank_ne_parameter_congruence_a12_sixth
            j m time hjmod hcong (by simpa [k] using hrun)
      exact Or.inr ⟨j,m,⟨hprior,hnot⟩,hroot⟩
  · rintro (hlow | ⟨j,m,⟨hprior,_⟩,hroot⟩)
    · exact Or.inl hlow
    · exact Or.inr ⟨j,m,hprior,hroot⟩

theorem sixth_disjoint_third_a12 (j m : Nat)
    (h6 : (3*m+71*j+57097)%65536=0) :
    (3*m+71*j+17161)%65536≠0 := by
  intro h3
  omega

theorem sixth_disjoint_fourth_a12 (j m : Nat)
    (hj : j%512=319)
    (h6 : (3*m+71*j+57097)%65536=0) :
    (3*m+7*j+20169)%32768≠0 := by
  intro h4
  have hdiv : 32768 ∣ 65536 := by decide
  have h6small : (3*m+71*j+57097)%32768=0 := by
    calc
      (3*m+71*j+57097)%32768 =
          ((3*m+71*j+57097)%65536)%32768 := by
        symm
        exact Nat.mod_mod_of_dvd _ hdiv
      _ = 0 := by rw [h6]
  omega

theorem sixth_disjoint_fifth_a12 (j m : Nat)
    (hj : j%512=319)
    (h6 : (3*m+71*j+57097)%65536=0) :
    (3*m+7*j+24265)%32768≠0 := by
  intro h5
  have hdiv : 32768 ∣ 65536 := by decide
  have h6small : (3*m+71*j+57097)%32768=0 := by
    calc
      (3*m+71*j+57097)%32768 =
          ((3*m+71*j+57097)%65536)%32768 := by
        symm
        exact Nat.mod_mod_of_dvd _ hdiv
      _ = 0 := by rw [h6]
  omega

#print axioms blank_halts_iff_after_a12_four
#print axioms sixth_disjoint_third_a12
#print axioms sixth_disjoint_fourth_a12
#print axioms sixth_disjoint_fifth_a12

end BB6.Agent12SevenSixthLatest
