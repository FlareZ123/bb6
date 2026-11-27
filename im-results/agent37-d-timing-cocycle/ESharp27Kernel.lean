import Lean.Elab.Tactic.Omega
import ExceptionalESharpMarkerKernel
import EKernel27AClosures

set_option maxRecDepth 8192
set_option maxHeartbeats 24000000

namespace BB6.Agent37ESharp27Kernel

open CryptidBoundary BB6.BoundaryPadding BB6.Padding
open BB6.Agent31PacketSource

/-- The only unresolved marker input residue classes after two independent
    all-parameter E/E/A and E/B/A source-route certificates are
    k in {4,7,13,16} mod27, Q in {0,1} mod3. -/
theorem marked_regular_or_27_kernel (k Q : Nat) :
    (∃ T a q b,
      ObsEq
        (run T (BB6.Agent37EMarkerResidual.marked k Q))
        (BB6.Agent2BoundaryBZero.regularSection a q b)) ∨
    ((k % 27 = 4 ∨ k % 27 = 7 ∨
      k % 27 = 13 ∨ k % 27 = 16) ∧ Q % 3 ≠ 2) := by
  rcases BB6.Agent37ESharpMarkerKernel.marked_regular_or_nine_kernel
      k Q with hreg | hbad
  · exact Or.inl hreg
  · rcases hbad with ⟨hk9,hQ⟩
    by_cases hk22 : k % 27 = 22
    · let u := k / 27
      have hku : k = 27*u+22 := by dsimp [u]; omega
      obtain ⟨T,a,q,b,hreg⟩ :=
        BB6.Agent37EKernel27AClosures.marked_22_mod_27_regular u Q
      exact Or.inl ⟨T,a,q,b,by simpa only [hku] using hreg⟩
    · by_cases hk25 : k % 27 = 25
      · let u := k / 27
        have hku : k = 27*u+25 := by dsimp [u]; omega
        obtain ⟨T,a,q,b,hreg⟩ :=
          BB6.Agent37EKernel27AClosures.marked_25_mod_27_regular u Q
        exact Or.inl ⟨T,a,q,b,by simpa only [hku] using hreg⟩
      · have hmod :
          k % 27 = 4 ∨ k % 27 = 7 ∨
          k % 27 = 13 ∨ k % 27 = 16 := by omega
        exact Or.inr ⟨hmod,hQ⟩

/-- Unconditional source reduction of the full exceptional E family,
    with no restrictions on the initial unary index k or q>=1.
    The remaining marked E2 source section has only four possible
    mod27 unary residues and two mod3 internal length residues. -/
theorem every_E_regular_or_27_kernel (k q : Nat) (hq : 1 ≤ q) :
    (∃ T a q' b,
      ObsEq
        (run T (DRegularSource.sourceSection ⟨3*k+4,q,1⟩))
        (BB6.Agent2BoundaryBZero.regularSection a q' b)) ∨
    (∃ T k' Q,
      (k' % 27 = 4 ∨ k' % 27 = 7 ∨
       k' % 27 = 13 ∨ k' % 27 = 16) ∧
      Q % 3 ≠ 2 ∧
      ObsEq
        (run T (DRegularSource.sourceSection ⟨3*k+4,q,1⟩))
        (BB6.Agent37EMarkerResidual.marked k' Q)) := by
  rcases BB6.Agent37EUniversalDichotomy.every_E_regular_or_marked_reset
      k q hq with hreg | hmarker
  · exact Or.inl hreg
  · rcases hmarker with ⟨T,k',Q,hfirst⟩
    rcases marked_regular_or_27_kernel k' Q with hreg | hbad
    · rcases hreg with ⟨S,a,q',b,hsecond⟩
      exact Or.inl ⟨T+S,a,q',b,
        source_chain T S
          (DRegularSource.sourceSection ⟨3*k+4,q,1⟩)
          (BB6.Agent37EMarkerResidual.marked k' Q)
          (BB6.Agent2BoundaryBZero.regularSection a q' b)
          hfirst hsecond⟩
    · exact Or.inr ⟨T,k',Q,hbad.1,hbad.2,hfirst⟩

#print axioms marked_regular_or_27_kernel
#print axioms every_E_regular_or_27_kernel

end BB6.Agent37ESharp27Kernel
