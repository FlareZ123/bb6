import OddTowerResidualAll
import ThirdStageOddDepth
import Lean.Elab.Tactic.Omega

set_option maxRecDepth 8192
namespace BB6.Agent19Special

/-- First new two-step source predecessor obstruction. The unique
    predecessors terminate at the original forbidden odd-special image. -/
theorem blank_no_special_a (u v : Nat) (hv : 1≤v) :
    ¬ BB6.Agent3.CReach (16*u+1) (64*v+10) := by
  intro hr
  have h1 : BB6.Agent3.CReach (16*u+64*v+9) (32*v+4) := by
    have hh := (BB6.Agent46.six_even_right_blank_reach_iff
      (16*u+1) (64*v+10)
      (by omega) (by omega) (by omega) (by omega)).mp hr
    have heq : ((16*u+1)+(64*v+10)-2, ((64*v+10)-2)/2) =
      (16*u+64*v+9,32*v+4) := by
      apply Prod.ext <;> omega
    rw [heq] at hh
    exact hh
  have h2 : BB6.Agent3.CReach (16*u+96*v+11) (16*v+1) := by
    have hh := (BB6.Agent46.six_even_right_blank_reach_iff
      (16*u+64*v+9) (32*v+4)
      (by omega) (by omega) (by omega) (by omega)).mp h1
    have heq : ((16*u+64*v+9)+(32*v+4)-2, ((32*v+4)-2)/2) =
      (16*u+96*v+11,16*v+1) := by
      apply Prod.ext <;> omega
    rw [heq] at hh
    exact hh
  rcases h2 with ⟨t,ht⟩
  exact (BB6Agent38.blank_section_no_odd_special t
    (16*u+96*v+11) (16*v+1)
    (by omega) (by omega) (by omega) (by omega)) ht

/-- Second new two-step source predecessor obstruction, including v=0. -/
theorem blank_no_special_b (u v : Nat) :
    ¬ BB6.Agent3.CReach (16*u+9) (64*v+42) := by
  intro hr
  have h1 : BB6.Agent3.CReach (16*u+64*v+49) (32*v+20) := by
    have hh := (BB6.Agent46.six_even_right_blank_reach_iff
      (16*u+9) (64*v+42)
      (by omega) (by omega) (by omega) (by omega)).mp hr
    have heq : ((16*u+9)+(64*v+42)-2, ((64*v+42)-2)/2) =
      (16*u+64*v+49,32*v+20) := by
      apply Prod.ext <;> omega
    rw [heq] at hh
    exact hh
  have h2 : BB6.Agent3.CReach (16*u+96*v+67) (16*v+9) := by
    have hh := (BB6.Agent46.six_even_right_blank_reach_iff
      (16*u+64*v+49) (32*v+20)
      (by omega) (by omega) (by omega) (by omega)).mp h1
    have heq : ((16*u+64*v+49)+(32*v+20)-2, ((32*v+20)-2)/2) =
      (16*u+96*v+67,16*v+9) := by
      apply Prod.ext <;> omega
    rw [heq] at hh
    exact hh
  rcases h2 with ⟨t,ht⟩
  exact (BB6Agent38.blank_section_no_odd_special t
    (16*u+96*v+67) (16*v+9)
    (by omega) (by omega) (by omega) (by omega)) ht

#print axioms blank_no_special_a
#print axioms blank_no_special_b
end BB6.Agent19Special
