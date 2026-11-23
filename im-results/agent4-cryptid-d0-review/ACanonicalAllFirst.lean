import Lean.Elab.Tactic.Omega
import ACanonicalOneTailFirst
import ACanonicalDoubleTailFirst
import ACanonicalTwoTailFirst

/-!
# Complete canonical A-section first-return theorem, all tail residues

For EVERY three-state grammar parameter k,q,b≥0 with positive alternating
pair count q+1, the actual D-start six-state machine has an exact positive
first physical F/0 return to another canonical grammar section. No fixed
finite bound, simulation truncation, code-pattern hypothesis, or explicit
right padding remains. The proof splits the three possible b mod 3
cases and invokes the stronger branch-specific all-parameter source results.
-/

set_option maxHeartbeats 10000000
set_option maxRecDepth 4096
set_option linter.unusedSimpArgs false

namespace BB6.Agent4ACanonicalAllFirst

open CryptidBoundary
open BB6.BoundaryPadding
open BB6.Padding
open BB6.BoundaryPadding
open BB6.CryptidELowCanonicalFirst
open BB6.Agent4ACanonicalOneTail
open BB6.Agent4ACanonicalDoubleTail
open BB6.Agent4ACanonicalTwoTail
open BB6.Agent4AImplicitOne
open BB6.Agent4AImplicitCode
open BB6.CryptidA1100CodeFirst

/-- Uniform first-physical-return existence and canonical successor
for EVERY A-residue regular source with at least one 01 pair.
Specific time and next-section parameters are given by its b mod 3
branch (the previous three files derive the closed exact formulas). -/
theorem all_A_positive_first (k q b : Nat) :
    ∃ (n : Nat) (out : DRegular.L),
      ObsEq
        (run n (DRegularSource.sourceSection ⟨3*k+3,q+1,b⟩))
        (DRegularSource.sourceSection out) ∧
      ∀ t, 0<t → t<n →
        ¬BlankLeftF
          (run t (DRegularSource.sourceSection ⟨3*k+3,q+1,b⟩)) := by
  let r : Nat := b/3
  have hr : b=3*r ∨ b=3*r+1 ∨ b=3*r+2 := by
    dsimp [r]
    omega
  rcases hr with hb | hb | hb
  · rw [hb]
    refine ⟨oneCost k (tokens0 q r),
      ⟨8*k+13+2*q+8*r,0,0⟩, ?_, ?_⟩
    · rw [(canonical_A_one_first k q r).1]
      exact cfgEq_refl _
    · intro t htpos ht hblank
      exact ((canonical_A_one_first k q r).2 t htpos ht) hblank.1
  · rw [hb]
    refine ⟨codeTime k (tokens0 q r),
      ⟨8*k+7+2*q+8*r,1,5⟩, ?_, ?_⟩
    · exact (canonical_A_double_first k q r).1
    · exact (canonical_A_double_first k q r).2
  · rw [hb]
    refine ⟨codeCost k (tokens q r),
      ⟨8*k+19+2*q+8*r,0,0⟩, ?_, ?_⟩
    · exact (canonical_A_two_first k q r).1
    · intro t htpos ht hblank
      exact ((canonical_A_two_first k q r).2 t htpos ht) hblank.1

#print axioms all_A_positive_first

end BB6.Agent4ACanonicalAllFirst
