import Agent15RayReach
import Lean.Elab.Tactic.Omega

namespace BB6.Agent15Rays
open BB6.Agent46

/-- A two-parameter missing-image rectangle of the genuine blank section. -/
theorem blank_no_two_four_mod8 (u v : Nat) :
    ¬ BB6.Agent3.CReach (4*u+2) (8*v+12) := by
  intro hr
  have hpar (a k : Nat)
      (h : secNext (a,k)=some (4*u+2,8*v+12)) :
      a=4*u+8*v+12 ∧ k=4*v+5 := by
    obtain ⟨ha,hk⟩ := even_right_direct_source a k (4*u+2) (8*v+12)
      (by omega) (by omega) (Or.inr (by omega)) h
    omega
  have hp : BB6.Agent3.CReach (4*u+8*v+12) (4*v+5) :=
    parent_one (x:=4*u+2) (y:=8*v+12)
      (u:=4*u+8*v+12) (v:=4*v+5) (by omega) hpar hr
  rcases hp with ⟨time,ht⟩
  cases time with
  | zero => simp [BB6.Agent8Section.run] at ht
  | succ n =>
      have hi := BB6.Agent3.blank_section_odd_image n
        (4*u+8*v+12) (4*v+5) ht (by omega) (by omega)
      omega

/-- Exact all-start depth bound: no two or more section returns lead to this rectangle. -/
theorem all_start_no_two_four_after_two (u v time : Nat)
    (start : Nat × Nat) :
    BB6.Agent8Section.run secNext (time+2) (some start) ≠
      some (4*u+2,8*v+12) := by
  intro ht
  have hf : time+2=(time+1)+1 := by omega
  rw [hf] at ht
  change (BB6.Agent8Section.run secNext (time+1) (some start)).bind secNext =
    some (4*u+2,8*v+12) at ht
  cases hp : BB6.Agent8Section.run secNext (time+1) (some start) with
  | none => rw [hp] at ht; simp at ht
  | some p =>
      rcases p with ⟨a,k⟩
      have hedge : secNext (a,k)=some (4*u+2,8*v+12) := by
        simpa only [hp, Option.bind_some] using ht
      obtain ⟨ha,hk⟩ := even_right_direct_source a k (4*u+2) (8*v+12)
        (by omega) (by omega) (Or.inr (by omega)) hedge
      have hA : a=4*u+8*v+12 := by omega
      have hK : k=4*v+5 := by omega
      have hstate : BB6.Agent8Section.run secNext (time+1) (some start)=
          some (4*u+8*v+12,4*v+5) := by
        simpa only [hA,hK] using hp
      cases hs : BB6.Agent8Section.run secNext time (some start) with
      | none => simp [BB6.Agent8Section.run,hs] at hstate
      | some st =>
          rcases st with ⟨p,q⟩
          have he : secNext (p,q)=some (4*u+8*v+12,4*v+5) := by
            simpa [BB6.Agent8Section.run,hs] using hstate
          have hm := BB6.Agent3.section_odd_image p q (4*u+8*v+12) (4*v+5)
            he (by omega) (by omega)
          omega

/-- The unique incoming edge exists for every pair u,v, so the bound is sharp. -/
theorem two_four_one_step_witness (u v : Nat) :
    secNext (4*u+8*v+12,4*v+5)=some (4*u+2,8*v+12) := by
  apply (section_preimage_all_iff (4*u+8*v+12) (4*v+5)
    (4*u+2) (8*v+12)).mpr
  have ha0 : 4*u+8*v+12≠0 := by omega
  have ha1 : 4*u+8*v+12≠1 := by omega
  have hk0 : 4*v+5≠0 := by omega
  have hreg : 2*(4*v+5)≤4*u+8*v+12 := by omega
  simp only [sectionPreimageAll,if_neg ha0,if_neg ha1,
    if_neg hk0,if_pos hreg]
  constructor <;> omega

#print axioms blank_no_two_four_mod8
#print axioms all_start_no_two_four_after_two
#print axioms two_four_one_step_witness
end BB6.Agent15Rays
