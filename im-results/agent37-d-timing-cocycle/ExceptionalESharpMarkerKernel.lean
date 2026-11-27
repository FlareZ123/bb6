import Lean.Elab.Tactic.Omega
import ExceptionalEMarkerResidual
import EOneModNineMarker

set_option maxRecDepth 8192
set_option maxHeartbeats 26000000

namespace BB6.Agent37ESharpMarkerKernel

open CryptidBoundary BB6.BoundaryPadding BB6.Padding
open BB6.Agent31PacketSource

/-- The E2 marker boundary admits source-connected regular return except
    possibly at k≡4 or 7 modulo 9 and Q≡0 or 1 modulo 3.
    A full k≡1 mod9 family is closed by a single E packet step followed
    by the all-A marker source theorem, uniformly in Q. -/
theorem marked_regular_or_nine_kernel (k Q : Nat) :
    (∃ T a q b,
      ObsEq (run T (BB6.Agent37EMarkerResidual.marked k Q))
        (BB6.Agent2BoundaryBZero.regularSection a q b)) ∨
    ((k % 9 = 4 ∨ k % 9 = 7) ∧ Q % 3 ≠ 2) := by
  rcases BB6.Agent37EMarkerResidual.marked_regular_or_residual k Q
      with hreg | hbad
  · exact Or.inl hreg
  · rcases hbad with ⟨hk3,hQ⟩
    by_cases hk9 : k % 9 = 1
    · let u := k / 9
      have hku : k = 9*u+1 := by dsimp [u];omega
      obtain ⟨T,a,q,b,hreg⟩ :=
        BB6.Agent37EOneModNineMarker.marked_one_mod_nine_regular u Q
      exact Or.inl ⟨T,a,q,b,by simpa only [hku] using hreg⟩
    · have hmod : k % 9 = 4 ∨ k % 9 = 7 := by omega
      exact Or.inr ⟨hmod,hQ⟩

/-- Unconditional source-valid reduction of all E-sector input sections
    L(3k+4,q,1) with q>0. The sole unresolved output family now obeys
    simultaneously k'≡4 or 7 mod9 and Q≡0 or 1 mod3. All other
    residue classes are routed back to a DRegular physical section. -/
theorem every_E_regular_or_nine_kernel (k q : Nat) (hq : 1 ≤ q) :
    (∃ T a q' b,
      ObsEq
        (run T (DRegularSource.sourceSection ⟨3*k+4,q,1⟩))
        (BB6.Agent2BoundaryBZero.regularSection a q' b)) ∨
    (∃ T k' Q,
      (k' % 9 = 4 ∨ k' % 9 = 7) ∧ Q % 3 ≠ 2 ∧
      ObsEq
        (run T (DRegularSource.sourceSection ⟨3*k+4,q,1⟩))
        (BB6.Agent37EMarkerResidual.marked k' Q)) := by
  rcases BB6.Agent37EUniversalDichotomy.every_E_regular_or_marked_reset
    k q hq with hreg | hmark
  · exact Or.inl hreg
  · rcases hmark with ⟨T,k',Q,hfirst⟩
    rcases marked_regular_or_nine_kernel k' Q with hreg | hres
    · rcases hreg with ⟨S,a,q',b,hsecond⟩
      exact Or.inl ⟨T+S,a,q',b,
        source_chain T S
          (DRegularSource.sourceSection ⟨3*k+4,q,1⟩)
          (BB6.Agent37EMarkerResidual.marked k' Q)
          (BB6.Agent2BoundaryBZero.regularSection a q' b)
          hfirst hsecond⟩
    · exact Or.inr ⟨T,k',Q,hres.1,hres.2,hfirst⟩

#print axioms marked_regular_or_nine_kernel
#print axioms every_E_regular_or_nine_kernel

end BB6.Agent37ESharpMarkerKernel
