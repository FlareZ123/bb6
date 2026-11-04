import Lean.Elab.Tactic.Omega
import FiveReturn
import BlankSixthExceptional

set_option maxHeartbeats 100000000
set_option maxRecDepth 55000

namespace BB6.Agent36SixthBlank
open CryptidBoundary BB6.BoundaryPadding BB6.Agent36SixthPacket

private theorem t6_mod27 : BB6.Agent25SixthRoot.t6 % 27 = 23 := by decide

private theorem entry_as_source (v : Nat) :
    entry v = DRegularSource.sourceSection ⟨9*(27*v+23)+7,4,1⟩ := by
  have hn : 9*(27*v+23)+7-2=3*(81*v+70)+2 := by omega
  simp [entry, DRegularSource.sourceSection, hn,
    oppairs, pairs, List.append_assoc]

private theorem exit_as_source (v : Nat) :
    regularExit v = DRegularSource.sourceSection ⟨32768*v+28577,3,2⟩ := by
  have hn : 32768*v+28577 = 2+(32768*v+28577-2) := by omega
  simp [regularExit, DRegularSource.sourceSection, init,
    hn, List.replicate_add, List.append_assoc]

/-- A source-verified original blank root, past the sixth exceptional E
    input, returns to canonical regular language after five designated
    physical F/0 checkpoints. -/
theorem blank_sixth_reentry :
    ∃ v : Nat,
      ObsEq
        (run (BB6.Agent25SixthRoot.sixthExceptionTime + fiveCost v) blank)
        (DRegularSource.sourceSection ⟨32768*v+28577,3,2⟩) := by
  let v := BB6.Agent25SixthRoot.t6 / 27
  have ht : BB6.Agent25SixthRoot.t6 = 27*v+23 := by
    dsimp [v]
    have h := t6_mod27
    omega
  have hroot : ObsEq
      (run BB6.Agent25SixthRoot.sixthExceptionTime blank)
      (entry v) := by
    rw [entry_as_source]
    simpa only [ht] using BB6.Agent25SixthRoot.sixthException_original
  refine ⟨v,?_⟩
  have hf : ObsEq (run (fiveCost v) (entry v))
      (DRegularSource.sourceSection ⟨32768*v+28577,3,2⟩) := by
    rw [←exit_as_source]
    exact five_return v
  exact source_chain BB6.Agent25SixthRoot.sixthExceptionTime
    (fiveCost v) blank (entry v)
    (DRegularSource.sourceSection ⟨32768*v+28577,3,2⟩) hroot hf

#print axioms t6_mod27
#print axioms blank_sixth_reentry
end BB6.Agent36SixthBlank
