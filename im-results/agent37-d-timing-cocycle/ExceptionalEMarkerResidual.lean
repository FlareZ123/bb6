import Lean.Elab.Tactic.Omega
import ExceptionalEUniversalDichotomy
import MarkerOneSource

set_option maxRecDepth 8192
set_option maxHeartbeats 25000000

namespace BB6.Agent37EMarkerResidual

open CryptidBoundary BB6.BoundaryPadding BB6.Padding
open BB6.Agent31PacketSource

def marked (k Q : Nat) : Cfg :=
  packet (8*k+5) 0 (2*Q+6) BB6.Agent2PacketP2Reset.marker

/-- The p≡1 marker normalizer closes Q≡2, regardless of the unary
    index. At other Q, both B-zero (k≡0) and A-marker (k≡2)
    close source-exactly. Only the simultaneous k≡1, Q≢2
    residue is left as a changed-marker obligation. -/
theorem marked_regular_or_residual (k Q : Nat) :
    (∃ T a q b,
      ObsEq (run T (marked k Q))
        (BB6.Agent2BoundaryBZero.regularSection a q b)) ∨
    (k % 3 = 1 ∧ Q % 3 ≠ 2) := by
  by_cases hQ : Q % 3 = 2
  · let c : BB6.Agent31PacketRank.Packet := ⟨8*k+5,0,2*Q+6⟩
    have ha : c.a ≥ 4 := by dsimp [c];omega
    have hp : c.p % 3 = 1 := by dsimp [c]; omega
    obtain ⟨T,a,r,b,hreg⟩ :=
      BB6.Agent35MarkerOne.all_marker_one_regular c ha hp
    exact Or.inl ⟨T,a,r,b,by simpa [marked,c,
      BB6.Agent35MarkerOne.marker] using hreg⟩
  · by_cases hka : k % 3 = 0
    · let kb : Nat := (8*k+5-2)/3
      have ha : 8*k+5=3*kb+2 := by dsimp [kb];omega
      have hrun := BB6.Agent35MarkerOne.b_zero_regular kb (2*Q+6)
      have hs : run (12*kb*kb+49*kb+40) (marked k Q) =
          BB6.Agent2BoundaryBZero.regularSection
            (8*kb+9+(2*Q+6)) 3 2 := by
        simpa [marked,BB6.Agent35MarkerOne.marker,ha] using hrun
      exact Or.inl ⟨12*kb*kb+49*kb+40,
        8*kb+9+(2*Q+6),3,2,by rw [hs]; exact BB6.Padding.cfgEq_refl _⟩
    · by_cases hkc : k % 3 = 2
      · let ka : Nat := (8*k+5-3)/3
        have ha : 8*k+5=3*ka+3 := by dsimp [ka];omega
        obtain ⟨T,a,r,b,hreg⟩ :=
          BB6.Agent35MarkerOne.a_marker_regular ka 0 (2*Q+6)
        exact Or.inl ⟨T,a,r,b,by simpa [marked,
          BB6.Agent35MarkerOne.marker,ha] using hreg⟩
      · exact Or.inr ⟨by omega,hQ⟩

/-- Entire original source E exceptional family, all unary lengths
    and all positive alternating-stack lengths, reduces to:
    (1) a finite physical regular-section reentry; or
    (2) the much smaller marked-packet cylinder with k'≡1 mod3
        and Q≢2 mod3.
    There are NO hypotheses restricting the starting k/q residues.
    The theorem makes no claim of termination/nontermination of case 2. -/
theorem every_E_regular_or_small_marker (k q : Nat) (hq : 1 ≤ q) :
    (∃ T a q' b,
      ObsEq
        (run T (DRegularSource.sourceSection ⟨3*k+4,q,1⟩))
        (BB6.Agent2BoundaryBZero.regularSection a q' b)) ∨
    (∃ T k' Q,
      k' % 3 = 1 ∧ Q % 3 ≠ 2 ∧
      ObsEq
        (run T (DRegularSource.sourceSection ⟨3*k+4,q,1⟩))
        (marked k' Q)) := by
  rcases BB6.Agent37EUniversalDichotomy.every_E_regular_or_marked_reset
      k q hq with hreg | hmarker
  · exact Or.inl hreg
  · rcases hmarker with ⟨T,k',Q,hfirst⟩
    rcases marked_regular_or_residual k' Q with hreg | hbad
    · rcases hreg with ⟨S,a,q',b,hsecond⟩
      exact Or.inl ⟨T+S,a,q',b,
        source_chain T S
          (DRegularSource.sourceSection ⟨3*k+4,q,1⟩)
          (marked k' Q)
          (BB6.Agent2BoundaryBZero.regularSection a q' b)
          hfirst hsecond⟩
    · exact Or.inr ⟨T,k',Q,hbad.1,hbad.2,hfirst⟩

#print axioms marked_regular_or_residual
#print axioms every_E_regular_or_small_marker

end BB6.Agent37EMarkerResidual
