import CThreeAltSource
import Lean.Elab.Tactic.Omega

namespace BB6.Agent4Three
open BB6.Agent46

/-- Each forbidden target has a real direct section predecessor. -/
theorem first_edge_witness_alt (s t : Nat) :
    secNext (8*s+16*t+15,8*t+5)=some (8*s+5,16*t+12) := by
  apply (section_preimage_all_iff (8*s+16*t+15) (8*t+5)
    (8*s+5) (16*t+12)).mpr
  have ha0 : 8*s+16*t+15 ≠ 0 := by omega
  have ha1 : 8*s+16*t+15 ≠ 1 := by omega
  have hk0 : 8*t+5 ≠ 0 := by omega
  have hlow : 2*(8*t+5)≤8*s+16*t+15 := by omega
  simp only [sectionPreimageAll,if_neg ha0,if_neg ha1,
    if_neg hk0,if_pos hlow]
  constructor <;> omega

/-- The second predecessor is a genuine original bounce at depth zero. -/
theorem second_edge_witness_alt (s t : Nat) :
    secNext (4*s+12*t+8,2*s+10*t+5)=
      some (8*s+16*t+15,8*t+5) := by
  apply (section_preimage_all_iff (4*s+12*t+8) (2*s+10*t+5)
    (8*s+16*t+15) (8*t+5)).mpr
  have ha0 : 4*s+12*t+8 ≠ 0 := by omega
  have ha1 : 4*s+12*t+8 ≠ 1 := by omega
  have hk0 : 2*s+10*t+5 ≠ 0 := by omega
  have hlow : ¬(2*(2*s+10*t+5)≤4*s+12*t+8) := by omega
  have heven : (4*s+12*t+8)%2=0 := by omega
  simp only [sectionPreimageAll,if_neg ha0,if_neg ha1,
    if_neg hk0,if_neg hlow,if_pos heven]
  refine ⟨by omega,0,?_,?_⟩
  · simp
    omega
  · simp
    omega

/-- These original section targets have exactly two ancestry levels. -/
theorem exactly_two_not_three_alt (s t : Nat)
    (hparity : s%2=t%2) :
    (∃ a k b l, secNext (b,l)=some (a,k) ∧
      secNext (a,k)=some (8*s+5,16*t+12)) ∧
    (∀ u v b l a k, ¬ (secNext (u,v)=some (b,l) ∧
      secNext (b,l)=some (a,k) ∧
      secNext (a,k)=some (8*s+5,16*t+12))) := by
  constructor
  · exact ⟨8*s+16*t+15,8*t+5,4*s+12*t+8,2*s+10*t+5,
      second_edge_witness_alt s t,first_edge_witness_alt s t⟩
  · intro u v b l a k ⟨h3,h2,h1⟩
    exact no_three_edges_alt u v b l a k s t hparity h3 h2 h1

/-- The two disjoint cylinders occupy exactly two of 512 residue cells. -/
theorem alt_two_sector_count :
    ((List.range 16).flatMap fun x =>
      (List.range 32).filter fun y =>
        ((x%16==5 && y%32==12) || (x%16==13 && y%32==28))).length=2 := by
  decide

#print axioms first_edge_witness_alt
#print axioms second_edge_witness_alt
#print axioms exactly_two_not_three_alt
#print axioms alt_two_sector_count
end BB6.Agent4Three
