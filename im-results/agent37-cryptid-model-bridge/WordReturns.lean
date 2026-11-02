import Lean.Elab.Tactic.Omega
import TokenCode
import CompleteAReturn

namespace BB6.CryptidBridge

/-- Closing a completely arbitrary interleaving of pair and triple symbols
    from the A boundary, using Agent25's source-verified word transducer. -/
theorem a_word_close (m : Nat) (ws : List Bool) (ys : List Bool) :
    CryptidA.run
      (CryptidA.wordCost m ws + (2*(m+CryptidA.wordInc ws)+6))
      (CryptidA.ab m (CryptidA.wordCode ws ++ (false :: ys))) =
    CryptidA.finish (2*(m+CryptidA.wordInc ws)+5) ys := by
  rw [CryptidA.run_add, CryptidA.consume_code]
  change CryptidA.run (2*(m+CryptidA.wordInc ws)+6)
    (CryptidA.start (m+CryptidA.wordInc ws) ys) = _
  exact CryptidA.close_double_zero _ _

/-- Transfer the complete arbitrary word return to Agent31's raw machine
    including its different explicit-frozen halt-state convention. -/
theorem boundary_a_word_close (m : Nat) (ws : List Bool) (ys : List Bool) :
    CryptidBoundary.run
      (CryptidA.wordCost m ws + (2*(m+CryptidA.wordInc ws)+6))
      (embed (CryptidA.ab m
        (CryptidA.wordCode ws ++ (false :: ys)))) =
    embed (CryptidA.finish (2*(m+CryptidA.wordInc ws)+5) ys) := by
  apply transfer_f0
  · simp [CryptidA.ab]
  · exact a_word_close m ws ys
  · rfl
  · rfl

/-- A complete F-to-F return of the genuine six-state machine, for every
    binary word ws encoding any sequence of 10 and 111 tokens. -/
theorem complete_A_word (k : Nat) (ws : List Bool) (ys : List Bool) :
    CryptidBoundary.run
      ((12*k*k+41*k+32) +
       (CryptidA.wordCost (4*k+3) ws +
        (2*((4*k+3)+CryptidA.wordInc ws)+6)))
      (CryptidBoundary.init
        (List.replicate (3*k+1) true ++
         false :: (CryptidA.wordCode ws ++ (false :: ys)))) =
    embed (CryptidA.finish
      (2*((4*k+3)+CryptidA.wordInc ws)+5) ys) := by
  rw [CryptidBoundary.run_add]
  rw [CryptidBoundary.prefix_A]
  change CryptidBoundary.run
    (CryptidA.wordCost (4*k+3) ws +
      (2*((4*k+3)+CryptidA.wordInc ws)+6))
    (CryptidBoundary.preA (4*k+3)
      (CryptidA.wordCode ws ++ (false::ys))) = _
  rw [preA_embed_ab]
  exact boundary_a_word_close (4*k+3) ws ys

#print axioms a_word_close
#print axioms boundary_a_word_close
#print axioms complete_A_word

end BB6.CryptidBridge
