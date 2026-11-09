import Lean.Elab.Tactic.Omega
import FullFFirstEvent

namespace BB6.Agent2ESeamFRoot
open CryptidBoundary
open BB6.SourceSeamFrame

/-- Positive physically blank-left F/0 return existence for the original
    six-state source is independent of the unary parameter k in an E-index
    initial section, for every arbitrary finite right tail. Every such
    section starts in F/0 at time zero; the positive-time condition is
    essential to remove that trivial initial section. -/
theorem positive_F_return_iff (ys : List Bool) (k h : Nat) :
    (∃ j : Nat, 0 < j ∧
      physicalReturn (run j (fStart k ys))) ↔
    (∃ j : Nat, 0 < j ∧
      physicalReturn (run j (fStart h ys))) := by
  rcases all_prepared_F_first_events ys with ⟨t,ht⟩ | hnone
  · constructor
    · intro _
      refine ⟨prefixTime h+(t+8*h+2),?_,(ht h).1⟩
      unfold prefixTime
      omega
    · intro _
      refine ⟨prefixTime k+(t+8*k+2),?_,(ht k).1⟩
      unfold prefixTime
      omega
  · constructor
    · rintro ⟨j,hpos,hret⟩
      exact False.elim ((hnone k j hpos).1 hret)
    · rintro ⟨j,hpos,hret⟩
      exact False.elim ((hnone h j hpos).1 hret)

#print axioms positive_F_return_iff
end BB6.Agent2ESeamFRoot
