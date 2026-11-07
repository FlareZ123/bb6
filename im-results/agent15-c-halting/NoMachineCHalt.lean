import BlankParam
import M192GeneralBound
import SmallSecondFamily
import M8M16Composition
import CLine
import Lean.Elab.Tactic.Omega

namespace BB6.Agent15

/--
This module records the remaining exact halting families for Machine C.
It does not prove nonhalting. The former blanket M192 inference from k≥8
was withdrawn because the backward invariant also requires lowCore residues.
-/
theorem blank_halt_requires_residual_families :
    BB6.CReachBridge.RunHalts →
      (∃ m k, 1≤m ∧ 8≤k ∧
        k+3*m+4=2^(2*m+3) ∧ CReach 1 k) ∨
      (∃ j m k, (j≠0 ∨ m≠0) ∧ 10≤k ∧
        k+j+3*m+5=2^(2*m+2)*(j+3) ∧ CReach (2*j+3) k) := by
  intro hhalt
  obtain ⟨time,a,k,hr,hparam⟩ :=
    (blank_halts_iff_two_parametric_families).mp hhalt
  rcases hparam with hfirst | hsecond
  · rcases hfirst with ⟨ha,hm⟩
    subst a
    rcases hm with ⟨m,heq⟩
    by_cases hm0 : m=0
    · subst m
      have hk : k=4 := by omega
      subst k
      have hline : BB6CLine.Reach (1,4,0) :=
        section_reach_embeds ⟨time,hr⟩
      exact False.elim (BB6CLine.special_unreachable hline)
    · have hmpos : 1≤m := by omega
      left
      exact ⟨m,k,hmpos,first_stop_k_ge8 m k hmpos heq,heq,⟨time,hr⟩⟩
  · rcases hsecond with ⟨j,m,ha,heq⟩
    subst a
    by_cases hjm0 : j=0 ∧ m=0
    · rcases hjm0 with ⟨rfl,rfl⟩
      have hk : k=7 := by omega
      subst k
      have hline : BB6CLine.Reach (3,7,0) :=
        section_reach_embeds ⟨time,hr⟩
      exact False.elim (source_no_3_7 hline)
    · have hjm : j≠0 ∨ m≠0 := by
        by_cases hj : j=0
        · right
          omega
        · left
          exact hj
      right
      exact ⟨j,m,k,hjm,second_stop_k_ge10_except_00 j m k hjm heq,
        heq,⟨time,hr⟩⟩

/-- The M192 lowCore invariant covers no state in the first stop family. -/
theorem first_stop_family_not_covered_by_M192 (k : Nat) :
    ¬ lowCore ((1+192)%192) (k%192) :=
  first_stop_family_outside_lowCore k

/-- The second-family point (j,m,k)=(0,1,40) is also outside lowCore. -/
theorem second_stop_example_not_covered_by_M192 :
    ¬ lowCore ((3+192)%192) (40%192) :=
  second_stop_example_outside_lowCore

#print axioms blank_halt_requires_residual_families

end BB6.Agent15