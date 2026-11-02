import AExtraBranches
import CryptidSix
import Lean.Elab.Tactic.Omega

namespace BB6.Agent36

/-- Turning an A-boundary 1101111110 into the E six-ones boundary. -/
theorem a_six_to_E (m : Nat) (ys : List Bool) :
  CryptidBoundary.run 3
    (BB6.Agent35.aBoundary (m+1)
      ([true,true,false] ++ (List.replicate 6 true ++ (false :: ys)))) =
    CryptidBoundary.eSix (m+2) ys := by
  simp [BB6.Agent35.aBoundary, CryptidBoundary.eSix,
    CryptidBoundary.run, CryptidBoundary.step,
    CryptidBoundary.goR, CryptidBoundary.goL,
    CryptidBoundary.pairs, List.append_assoc]

/-- An all-parameter return on the A-side single-zero six-ones gate. -/
theorem a_six_return (m : Nat) (ys : List Bool) :
    CryptidBoundary.run (2*m+26)
      (BB6.Agent35.aBoundary (m+1)
        ([true,true,false] ++ (List.replicate 6 true ++ (false::ys)))) =
      ⟨[], false, List.replicate (2*m+7) true ++
        (CryptidBoundary.packetSix ++ ys), 5⟩ := by
  have ht : 2*m+26 = 3+(2*(m+2)+19) := by omega
  rw [ht, CryptidBoundary.run_add, a_six_to_E,
    CryptidBoundary.eSix_run]
  rw [show 2*(m+2)+3=2*m+7 by omega]

/-- Original six-state machine: arbitrary coded A packets followed by
    the 1101111110 gate, without restricting the remaining suffix. -/
theorem full_A_code_six (k : Nat) (ws ys : List Bool) :
  CryptidBoundary.run
    ((12*k*k+41*k+32) +
      (CryptidA.wordCost (4*k+3) ws +
        (2*((4*k+3)+CryptidA.wordInc ws)+24)))
    (CryptidBoundary.init
      (List.replicate (3*k+1) true ++ false ::
       (CryptidA.wordCode ws ++ ([true,true,false] ++
         (List.replicate 6 true ++ (false::ys)))))) =
    ⟨[], false,
      List.replicate (2*((4*k+3)+CryptidA.wordInc ws)+5) true ++
        (CryptidBoundary.packetSix ++ ys), 5⟩ := by
  rw [CryptidBoundary.run_add, CryptidBoundary.prefix_A]
  change CryptidBoundary.run
    (CryptidA.wordCost (4*k+3) ws +
      (2*((4*k+3)+CryptidA.wordInc ws)+24))
    (BB6.Agent35.aBoundary (4*k+3)
      (CryptidA.wordCode ws ++ ([true,true,false] ++
        (List.replicate 6 true ++ (false::ys))))) = _
  rw [CryptidBoundary.run_add, BB6.Agent35.a_code_return]
  have ht : 2*((4*k+3)+CryptidA.wordInc ws)+24 =
    2*((4*k+2)+CryptidA.wordInc ws)+26 := by omega
  rw [ht]
  have harg : 4*k+3+CryptidA.wordInc ws =
    (4*k+2+CryptidA.wordInc ws)+1 := by omega
  rw [harg, a_six_return]
  congr 1

/-- Exact all-natural trace pattern for previously uncovered D-family roots. -/
theorem full_A_six (k q r : Nat) (ys : List Bool) :
    CryptidBoundary.run
      (12*k*k+49*k+62+4*q+12*r*r+(24*k+55+6*q)*r)
      (CryptidBoundary.init
        (List.replicate (3*k+1) true ++
          false :: (CryptidBoundary.pairs q ++
            (List.replicate (3*r+2) true ++
              (false :: List.replicate 6 true ++ (false::ys)))))) =
      ⟨[], false, List.replicate (8*k+11+2*q+8*r) true ++
        (CryptidBoundary.packetSix ++ ys), 5⟩ := by
  have h := full_A_code_six k (tokens q r) ys
  have ht :
    (12*k*k+41*k+32) +
      (CryptidA.wordCost (4*k+3) (tokens q r) +
        (2*((4*k+3)+CryptidA.wordInc (tokens q r))+24)) =
      12*k*k+49*k+62+4*q+12*r*r+(24*k+55+6*q)*r := by
    rw [cost_tokens, inc_tokens]
    simp only [Nat.add_mul]
    omega
  have hc :
    2*((4*k+3)+CryptidA.wordInc (tokens q r))+5 =
    8*k+11+2*q+8*r := by
    rw [inc_tokens]
    omega
  have hx (ys : List Bool) :
    CryptidA.wordCode (tokens q r) ++
      ([true,true,false] ++ (List.replicate 6 true ++ (false::ys))) =
    CryptidBoundary.pairs q ++
      (List.replicate (3*r+2) true ++
        (false :: List.replicate 6 true ++ (false::ys))) := by
    rw [code_tokens]
    have hp : List.replicate (3*r+2) true =
      List.replicate (3*r) true ++ [true,true] := by
      rw [← List.replicate_append_replicate]
      rfl
    rw [hp]
    simp only [List.append_assoc, List.cons_append, List.nil_append]
  rw [ht, hc, hx] at h
  exact h

#print axioms a_six_to_E
#print axioms a_six_return
#print axioms full_A_code_six
#print axioms full_A_six
end BB6.Agent36
