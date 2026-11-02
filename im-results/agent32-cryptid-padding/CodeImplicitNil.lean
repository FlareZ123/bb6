import Lean.Elab.Tactic.Omega
import ABridgeCode
import SixOnes

set_option maxHeartbeats 5000000

namespace BB6.Agent32Code

open BB6.Agent35

/-- Entire encoded word is consumed, then the first implicit blank is
    closed exactly by the original machine. Any Boolean token word. -/
theorem code_then_implicit_nil (m : Nat) (ws : List Bool) :
    CryptidBoundary.run
      (CryptidA.wordCost m ws +
        (2*(m+CryptidA.wordInc ws)+6))
      (aBoundary m (CryptidA.wordCode ws)) =
    (⟨[], false,
      List.replicate (2*(m+CryptidA.wordInc ws)+5) true, 5⟩ :
      CryptidBoundary.Cfg) := by
  rw [CryptidBoundary.run_add]
  have hc := BB6.Agent35.a_code_return m ws ([] : List Bool)
  simp only [List.append_nil] at hc
  rw [hc]
  apply BB6.Agent35.toA_finish
  rw [BB6.Agent35.toA_run, BB6.Agent35.toA_aBoundary]
  simpa [CryptidA.finish] using
    (CryptidA.a_close_nil (m+CryptidA.wordInc ws))

/-- Every mixture of 10 and 111 packet symbols closes on an implicit
    blank, with an exact universal primitive-step formula. -/
theorem full_A_code_implicit_nil (k : Nat) (ws : List Bool) :
    CryptidBoundary.run
      ((12*k*k+41*k+32) +
        (CryptidA.wordCost (4*k+3) ws +
         (2*((4*k+3)+CryptidA.wordInc ws)+6)))
      (CryptidBoundary.init
        (List.replicate (3*k+1) true ++
          false :: CryptidA.wordCode ws)) =
    (⟨[], false,
       List.replicate (2*((4*k+3)+CryptidA.wordInc ws)+5) true, 5⟩ :
       CryptidBoundary.Cfg) := by
  rw [CryptidBoundary.run_add, CryptidBoundary.prefix_A]
  change CryptidBoundary.run _ (aBoundary (4*k+3) (CryptidA.wordCode ws)) = _
  exact code_then_implicit_nil (4*k+3) ws

#print axioms code_then_implicit_nil
#print axioms full_A_code_implicit_nil
end BB6.Agent32Code
