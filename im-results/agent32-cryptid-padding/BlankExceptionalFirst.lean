import Lean.Elab.Tactic.Omega
import BlankExceptional
import PhysicalReturnObs

set_option maxHeartbeats 100000000
set_option maxRecDepth 50000

namespace BB6.Agent32BlankExceptionalFirst

open CryptidBoundary BB6.BoundaryPadding BB6.Padding
open BB6.Agent32PhysicalObs

/-- The D-start six-state machine, from its genuine completely blank
    initial tape, has an explicitly identified strict first physical F/0
    return after the 8394-section certified regular prefix. The witness k
    is the exact source-reachable E-(10)^5-1100 family parameter.

    It excludes EVERY earlier F-on-zero time with physically blank left
    half-tape, including syntactically nonempty all-zero padding. -/
theorem blank_after_8394_first_exceptional_E :
    ∃ k : Nat,
      ObsEq
        (run
          ((36 + DRegular.accumulated 8394 BB6.BlankRegular8394.seed9) +
            BB6.Agent32EAll.duration k 5) blank)
        (BB6.Agent32EAll.output k 5 []) ∧
      ∀ u, 0<u → u<BB6.Agent32EAll.duration k 5 →
        ¬BB6.Agent32EDoubleFirst.PhysicalF0
          (run
            ((36 + DRegular.accumulated 8394 BB6.BlankRegular8394.seed9) + u)
            blank) := by
  rcases BB6.BlankExceptional.exceptional_section with ⟨k,hsource⟩
  refine ⟨k,?_,?_⟩
  · have hmacro : ObsEq
        (run (BB6.Agent32EAll.duration k 5)
          (BB6.Agent32EAll.start k 5 []))
        (BB6.Agent32EAll.output k 5 []) := by
      rw [(BB6.Agent32EDoubleFirst.all_e_double_first_return k 5 []).1]
      exact cfgEq_refl _
    exact source_chain
      (36 + DRegular.accumulated 8394 BB6.BlankRegular8394.seed9)
      (BB6.Agent32EAll.duration k 5)
      blank (BB6.Agent32EAll.start k 5 [])
      (BB6.Agent32EAll.output k 5 []) hsource hmacro
  · intro u hpos hbound hret
    have heq : ObsEq
        (run u
          (run (36 + DRegular.accumulated 8394 BB6.BlankRegular8394.seed9)
            blank))
        (run u (BB6.Agent32EAll.start k 5 [])) :=
      source_congr u hsource
    rw [run_add] at hret
    exact (BB6.Agent32EDoubleFirst.all_e_double_first_return k 5 []).2
      u hpos hbound ((physicalF0_congr heq).mp hret)

#print axioms blank_after_8394_first_exceptional_E

end BB6.Agent32BlankExceptionalFirst
