import ABridgeEGeneral
import Lean.Elab.Tactic.Omega

set_option maxHeartbeats 5000000

namespace BB6.Agent36
open CryptidBoundary

/-- The A-boundary 110 gate reaches the E-pairs family for any q, not only
    the q=0 1100 suffix previously covered by Agent35. -/
theorem a_gate_any_pairs (m q : Nat) (ys : List Bool) :
    run (2*m+4*q+18)
      (BB6.Agent35.aBoundary (m+1)
        ([true,true,false] ++ (pairs q ++ (false::ys)))) =
      ⟨[],false,List.replicate (2*m+3) true ++
        (false :: List.replicate (2*q+6) true ++ ys), 5⟩ := by
  have ht : 2*m+4*q+18 = 3+(2*m+4*q+15) := by omega
  rw [ht,run_add,a_gate_to_E]
  change run (2*m+4*q+15) (ePairs m q ys) = _
  exact ePairs_run m q ys

/-- All A packet words, followed by 110 (10)^q 0 and arbitrary right tape,
    return in an exact source-certified number of primitive six-state steps. -/
theorem full_A_code_E_pairs (k q : Nat) (ws ys : List Bool) :
    run
      ((12*k*k+41*k+32) +
        (CryptidA.wordCost (4*k+3) ws +
          (2*((4*k+3)+CryptidA.wordInc ws)+4*q+16)))
      (init (List.replicate (3*k+1) true ++
        false :: (CryptidA.wordCode ws ++
          ([true,true,false] ++ (pairs q ++ (false::ys)))))) =
      ⟨[],false,
        List.replicate (2*((4*k+3)+CryptidA.wordInc ws)+1) true ++
          (false :: List.replicate (2*q+6) true ++ ys),5⟩ := by
  rw [run_add,prefix_A]
  change run
    (CryptidA.wordCost (4*k+3) ws +
      (2*((4*k+3)+CryptidA.wordInc ws)+4*q+16))
    (BB6.Agent35.aBoundary (4*k+3)
      (CryptidA.wordCode ws ++
        ([true,true,false] ++ (pairs q ++ (false::ys))))) = _
  rw [run_add,BB6.Agent35.a_code_return]
  have ht :
    2*((4*k+3)+CryptidA.wordInc ws)+4*q+16 =
      2*((4*k+2)+CryptidA.wordInc ws)+4*q+18 := by omega
  rw [ht]
  have harg :
    4*k+3+CryptidA.wordInc ws =
      (4*k+2+CryptidA.wordInc ws)+1 := by omega
  rw [harg,a_gate_any_pairs]
  congr 1

#print axioms a_gate_any_pairs
#print axioms full_A_code_E_pairs
end BB6.Agent36
