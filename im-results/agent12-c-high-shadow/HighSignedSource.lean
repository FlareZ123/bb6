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

theorem branching_diagonal_source (t k : Nat)
    (hstop : k+(40+512*t)+3*(5+512*t)+5=
      2^(2*(5+512*t)+2)*((40+512*t)+3)) :
    ¬BB6.Agent3.CReach (2*(40+512*t)+3) k :=
  high_adaptive_excluded 2 10 _ _ k (branching_diagonal t) hstop

#print axioms high_signed_excluded
#print axioms high_adaptive_excluded
#print axioms branching_diagonal_source
end BB6.Agent12SignedCone
