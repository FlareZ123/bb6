import Lean.Elab.Tactic.Omega
import ABridgeCode
import CryptidPairs

namespace BB6.Agent35

/-- Original A boundary with right 1100 reduces in three primitive steps
    to an E boundary with a zero on the right. -/
theorem a_double_to_E (m : Nat) (ys : List Bool) :
    CryptidBoundary.run 3 (aBoundary (m+1)
      ([true,true,false,false] ++ ys)) =
    CryptidBoundary.ePairs m 0 ys := by
  simp [aBoundary, CryptidBoundary.ePairs, CryptidBoundary.run,
        CryptidBoundary.step, CryptidBoundary.goR,
        CryptidBoundary.pairs]

/-- The E return closes this entire A-boundary family for every m and suffix. -/
theorem a_double_return (m : Nat) (ys : List Bool) :
    CryptidBoundary.run (2*m+18) (aBoundary (m+1)
      ([true,true,false,false] ++ ys)) =
    ⟨[], false, List.replicate (2*m+3) true ++
      (false :: List.replicate 6 true ++ ys), 5⟩ := by
  have ht : 2*m+18 = 3+(2*m+15) := by omega
  rw [ht, CryptidBoundary.run_add, a_double_to_E]
  simpa using CryptidBoundary.ePairs_run m 0 ys

/-- Complete original-machine F-to-F return after arbitrary coded A packets
    and the formerly unclassified 1100 delimiter. -/
theorem full_A_code_double (k : Nat) (ws ys : List Bool) :
    CryptidBoundary.run
      ((12*k*k+41*k+32)+
        (CryptidA.wordCost (4*k+3) ws+
          (2*((4*k+3)+CryptidA.wordInc ws)+16)))
      (CryptidBoundary.init
        (List.replicate (3*k+1) true ++
         false :: (CryptidA.wordCode ws ++
           ([true,true,false,false] ++ ys)))) =
      ⟨[],false,
        List.replicate (2*((4*k+3)+CryptidA.wordInc ws)+1) true ++
          (false :: List.replicate 6 true ++ ys),5⟩ := by
  rw [CryptidBoundary.run_add, CryptidBoundary.prefix_A]
  change CryptidBoundary.run
    (CryptidA.wordCost (4*k+3) ws+
      (2*((4*k+3)+CryptidA.wordInc ws)+16))
    (aBoundary (4*k+3)
      (CryptidA.wordCode ws ++ ([true,true,false,false] ++ ys))) = _
  rw [CryptidBoundary.run_add, a_code_return]
  have ht : 2*((4*k+3)+CryptidA.wordInc ws)+16 =
      2*((4*k+2+CryptidA.wordInc ws))+18 := by omega
  rw [ht]
  have harg : 4*k+3+CryptidA.wordInc ws =
       (4*k+2+CryptidA.wordInc ws)+1 := by omega
  rw [harg, a_double_return]
  congr 1

#print axioms a_double_to_E
#print axioms a_double_return
#print axioms full_A_code_double
end BB6.Agent35
