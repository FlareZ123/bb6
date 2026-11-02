import AExtraBranches
import CryptidTriplePairs
import Lean.Elab.Tactic.Omega

set_option maxHeartbeats 5000000
namespace BB6.Agent36

open CryptidBoundary

/-- Single universal source-level A-to-E bridge after reading 110,
    without constraining any bit of the remaining right tape. -/
def afterA110 (m : Nat) (ys : List Bool) : Cfg :=
  ⟨false::false::pairs (m+2) ++ [true,true],false,ys,4⟩

theorem a_gate_to_E (m : Nat) (ys : List Bool) :
  run 3 (BB6.Agent35.aBoundary (m+1) ([true,true,false] ++ ys)) =
    afterA110 m ys := by
  simp [BB6.Agent35.aBoundary, afterA110,run,step,
    goR,goL,pairs]

/-- Exact A-to-F return through ANY E q-pair triple-one gate. -/
theorem a_gate_triple_pairs (m q : Nat) (ys : List Bool) :
  run (2*m+6*q+22)
    (BB6.Agent35.aBoundary (m+1)
      ([true,true,false] ++ (pairs q ++ ([true,true,true] ++ ys)))) =
    ⟨[],false,List.replicate (2*m+3) true ++
      (oppairs (q+2) ++ (false::ys)),5⟩ := by
  have ht : 2*m+6*q+22 = 3+(2*m+6*q+19) := by omega
  rw [ht,run_add,a_gate_to_E]
  change run (2*m+6*q+19) (eTriplePairs m q ys) = _
  rw [eTriplePairs_run]

/-- Arbitrary A-side encoded prefix followed by 110 (10)^q 111 and
    arbitrary continuation: universally exact original machine steps. -/
theorem full_A_code_E_triple (k q : Nat) (ws ys : List Bool) :
  run
    ((12*k*k+41*k+32) +
      (CryptidA.wordCost (4*k+3) ws +
        (2*((4*k+3)+CryptidA.wordInc ws)+6*q+20)))
    (init (List.replicate (3*k+1) true ++
      false :: (CryptidA.wordCode ws ++
        ([true,true,false] ++ (pairs q ++ ([true,true,true] ++ ys)))))) =
    ⟨[],false,
      List.replicate (2*((4*k+3)+CryptidA.wordInc ws)+1) true ++
        (oppairs (q+2) ++ (false::ys)),5⟩ := by
  rw [run_add,prefix_A]
  change run
    (CryptidA.wordCost (4*k+3) ws +
      (2*((4*k+3)+CryptidA.wordInc ws)+6*q+20))
    (BB6.Agent35.aBoundary (4*k+3)
      (CryptidA.wordCode ws ++
        ([true,true,false] ++ (pairs q ++ ([true,true,true] ++ ys))))) = _
  rw [run_add,BB6.Agent35.a_code_return]
  have ht :
    2*((4*k+3)+CryptidA.wordInc ws)+6*q+20 =
    2*((4*k+2)+CryptidA.wordInc ws)+6*q+22 := by omega
  rw [ht]
  have harg :
    4*k+3+CryptidA.wordInc ws =
    (4*k+2+CryptidA.wordInc ws)+1 := by omega
  rw [harg,a_gate_triple_pairs]
  congr 1
  omega

#print axioms a_gate_to_E
#print axioms a_gate_triple_pairs
#print axioms full_A_code_E_triple
end BB6.Agent36
