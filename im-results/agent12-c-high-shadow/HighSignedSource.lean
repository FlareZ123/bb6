import HighSigned
import AffineConeLowStop
import Lean.Elab.Tactic.Omega

namespace BB6.Agent12SignedCone
open BB6.Agent12HighShadow

private theorem sourceParent : ParentContract BB6.Agent3.CReach := by
  intro x y v hx hy hval hgt hr
  obtain ⟨a,k,hp,he⟩ := BB6.Agent11M0SumZeroVerified.cReach_parent_of_left_gt5 x y hx hr
  exact ⟨a,k,hp,BB6.Agent13AffineCone.parent_equations a k x y v hy hval hgt
    ((BB6.Agent46.complete_section_inverse a k x y (by omega)).mp he)⟩

theorem high_signed_excluded (f j m k : Nat) (h : highExcluded f j m=true)
    (hstop : k+j+3*m+5=2^(2*m+2)*(j+3)) : ¬BB6.Agent3.CReach (2*j+3) k :=
  highExcluded_sound _ sourceParent BB6.Agent13TwoParent.odd_forbidden_image f j m k h hstop

theorem high_adaptive_excluded (f r j m k : Nat) (h : adaptiveExcluded f r j m=true)
    (hstop : k+j+3*m+5=2^(2*m+2)*(j+3)) : ¬BB6.Agent3.CReach (2*j+3) k :=
  adaptiveExcluded_sound _ sourceParent BB6.Agent13TwoParent.odd_forbidden_image f r j m k h hstop


/-- A full two-dimensional parameter lattice of high stopping states is excluded.
    The coupled parity condition is exactly the precision-10 lift lattice. -/
theorem branching_lattice_source (a c k : Nat) (hpar : a%2=c%2)
    (hstop : k+(40+512*a)+3*(5+512*c)+5=
      2^(2*(5+512*c)+2)*((40+512*a)+3)) :
    ¬BB6.Agent3.CReach (2*(40+512*a)+3) k := by
  apply high_adaptive_excluded 2 10 (40+512*a) (5+512*c) k
  · apply adaptive_lattice_lift 2 10 40 5 (512*a) (512*c)
    · refine ⟨a, ?_⟩
      norm_num
    · refine ⟨(a+3*c)/2, ?_⟩
      omega
    · exact branching_diagonal 0
  · exact hstop

/-- The previously recorded diagonal is a special case of the full lattice. -/
theorem branching_diagonal_source (t k : Nat)
    (hstop : k+(40+512*t)+3*(5+512*t)+5=
      2^(2*(5+512*t)+2)*((40+512*t)+3)) :
    ¬BB6.Agent3.CReach (2*(40+512*t)+3) k :=
  branching_lattice_source t t k rfl hstop

#print axioms high_signed_excluded
#print axioms high_adaptive_excluded
#print axioms branching_diagonal_source
end BB6.Agent12SignedCone
