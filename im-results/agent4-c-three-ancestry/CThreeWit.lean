import CThreeGenericSource
import Lean.Elab.Tactic.Omega

namespace BB6.Agent4Three
open BB6.Agent46

/-- Each forbidden target has a real direct section predecessor. -/
theorem first_edge_witness (s t : Nat) :
    secNext (8*s+16*t+19,8*t+9)=some (8*s+1,16*t+20) := by
  apply (section_preimage_all_iff (8*s+16*t+19) (8*t+9)
    (8*s+1) (16*t+20)).mpr
  have ha0 : 8*s+16*t+19 ≠ 0 := by omega
  have ha1 : 8*s+16*t+19 ≠ 1 := by omega
  have hk0 : 8*t+9 ≠ 0 := by omega
  have hlow : 2*(8*t+9)≤8*s+16*t+19 := by omega
  simp only [sectionPreimageAll,if_neg ha0,if_neg ha1,
    if_neg hk0,if_pos hlow]
  constructor <;> omega

/-- The second predecessor is a genuine original bounce at depth zero. -/
theorem second_edge_witness (s t : Nat) :
    secNext (4*s+12*t+12,2*s+10*t+9)=
      some (8*s+16*t+19,8*t+9) := by
  apply (section_preimage_all_iff (4*s+12*t+12) (2*s+10*t+9)
    (8*s+16*t+19) (8*t+9)).mpr
  have ha0 : 4*s+12*t+12 ≠ 0 := by omega
  have ha1 : 4*s+12*t+12 ≠ 1 := by omega
  have hk0 : 2*s+10*t+9 ≠ 0 := by omega
  have hlow : ¬(2*(2*s+10*t+9)≤4*s+12*t+12) := by omega
  have heven : (4*s+12*t+12)%2=0 := by omega
  simp only [sectionPreimageAll,if_neg ha0,if_neg ha1,
    if_neg hk0,if_neg hlow,if_pos heven]
  refine ⟨by omega,0,?_,?_⟩
  · simp
    omega
  · simp
    omega

/-- These original section targets have exactly two ancestry levels. -/
theorem exactly_two_not_three_generic (s t : Nat)
    (hparity : s%2=t%2) :
    (∃ a k b l, secNext (b,l)=some (a,k) ∧
      secNext (a,k)=some (8*s+1,16*t+20)) ∧
    (∀ u v b l a k, ¬ (secNext (u,v)=some (b,l) ∧
      secNext (b,l)=some (a,k) ∧
      secNext (a,k)=some (8*s+1,16*t+20))) := by
  constructor
  · exact ⟨8*s+16*t+19,8*t+9,4*s+12*t+12,2*s+10*t+9,
      second_edge_witness s t,first_edge_witness s t⟩
  · intro u v b l a k ⟨h3,h2,h1⟩
    exact no_three_edges_generic u v b l a k s t hparity h3 h2 h1

/-- The two disjoint cylinders occupy exactly two of 512 residue cells. -/
theorem two_sector_count :
    ((List.range 16).flatMap fun x =>
      (List.range 32).filter fun y =>
        ((x%16==9 && y%32==4) || (x%16==1 && y%32==20))).length=2 := by
  decide

#print axioms first_edge_witness
#print axioms second_edge_witness
#print axioms exactly_two_not_three_generic
#print axioms two_sector_count
end BB6.Agent4Three
