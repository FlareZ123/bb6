import M0EvenEvenSumZero
import Lean.Elab.Tactic.Omega

namespace BB6.Agent11SmallBoundaryZero
open BB6.Agent46

/-- No genuine original Machine C section transition has right output zero. -/
theorem no_section_output_y0 (a k x : Nat)
    (h : secNext (a,k)=some (x,0)) : False := by
  have hpre := (section_preimage_all_iff a k x 0).mp h
  unfold sectionPreimageAll at hpre
  split_ifs at hpre <;> omega

/-- Every original section transition into right counter two has the
    unique source (x+2,0). -/
theorem section_y2_unique_parent (a k x : Nat)
    (h : secNext (a,k)=some (x,2)) :
    a=x+2 ∧ k=0 := by
  have hpre := (section_preimage_all_iff a k x 2).mp h
  unfold sectionPreimageAll at hpre
  split_ifs at hpre <;> omega

/-- No state with right counter zero lies on the genuine blank-origin
    section orbit. -/
theorem blank_no_right_zero (x : Nat) :
    ¬ BB6.Agent3.CReach x 0 := by
  intro hr
  rcases hr with ⟨time,h⟩
  cases time with
  | zero =>
      simp [BB6.Agent8Section.run] at h
      omega
  | succ t =>
      cases hp : BB6.Agent8Section.run secNext t (some (5,1)) with
      | none =>
          simp [BB6.Agent8Section.run,hp] at h
      | some p =>
          rcases p with ⟨a,k⟩
          have hstep : secNext (a,k)=some (x,0) := by
            simpa [BB6.Agent8Section.run,hp] using h
          exact no_section_output_y0 a k x hstep

/-- No state with right counter two lies on the genuine blank-origin
    section orbit: its unique predecessor would have right counter zero. -/
theorem blank_no_right_two (x : Nat) :
    ¬ BB6.Agent3.CReach x 2 := by
  intro hr
  rcases hr with ⟨time,h⟩
  cases time with
  | zero =>
      simp [BB6.Agent8Section.run] at h
      omega
  | succ t =>
      cases hp : BB6.Agent8Section.run secNext t (some (5,1)) with
      | none =>
          simp [BB6.Agent8Section.run,hp] at h
      | some p =>
          rcases p with ⟨a,k⟩
          have hstep : secNext (a,k)=some (x,2) := by
            simpa [BB6.Agent8Section.run,hp] using h
          obtain ⟨ha,hk⟩ := section_y2_unique_parent a k x hstep
          have hprev : BB6.Agent3.CReach (x+2) 0 := by
            refine ⟨t,?_⟩
            simpa [ha,hk] using hp
          exact blank_no_right_zero (x+2) hprev

#print axioms no_section_output_y0
#print axioms section_y2_unique_parent
#print axioms blank_no_right_zero
#print axioms blank_no_right_two
end BB6.Agent11SmallBoundaryZero
