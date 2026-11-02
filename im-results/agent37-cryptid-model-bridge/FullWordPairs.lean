import DoubleOnePairs
import Lean.Elab.Tactic.Omega

set_option maxRecDepth 4096
set_option maxHeartbeats 500000

namespace BB6.CryptidBridge

/-- A complete original-machine F-to-F return over an arbitrary token word,
    followed by the entire `110(10)^q0` family. The result retains a right
    `0 1^(2q+6)` packet, uniformly in the unrestricted suffix. -/
theorem complete_A_word_two_one_pairs (k q : Nat) (ws ys : List Bool) :
    CryptidBoundary.run
      ((12*k*k+41*k+32) +
        (CryptidA.wordCost (4*k+3) ws +
          (2*((4*k+3)+CryptidA.wordInc ws)+16+4*q)))
      (CryptidBoundary.init
        (List.replicate (3*k+1) true ++
         false :: (CryptidA.wordCode ws ++
           ([true,true,false] ++ (CryptidBoundary.pairs q ++ (false::ys)))))) =
    ⟨[],false,
      List.replicate
        (2*((4*k+3)+CryptidA.wordInc ws)+1) true ++
        (false :: List.replicate (2*q+6) true ++ ys),5⟩ := by
  rw [CryptidBoundary.run_add, CryptidBoundary.prefix_A]
  change CryptidBoundary.run
    (CryptidA.wordCost (4*k+3) ws +
      (2*((4*k+3)+CryptidA.wordInc ws)+16+4*q))
    (CryptidBoundary.preA (4*k+3)
      (CryptidA.wordCode ws ++ ([true,true,false] ++ (CryptidBoundary.pairs q ++ (false::ys))))) = _
  rw [preA_embed_ab]
  rw [CryptidBoundary.run_add]
  -- Transport Agent25's universal arbitrary-word ingestion before the new branch.
  have hi : CryptidBoundary.run (CryptidA.wordCost (4*k+3) ws)
      (embed (CryptidA.ab (4*k+3)
        (CryptidA.wordCode ws ++ ([true,true,false] ++ (CryptidBoundary.pairs q ++ (false::ys)))))) =
      embed (CryptidA.ab ((4*k+3)+CryptidA.wordInc ws)
        ([true,true,false] ++ (CryptidBoundary.pairs q ++ (false::ys)))) := by
    apply transfer_nonF
    · simp [CryptidA.ab]
    · exact CryptidA.consume_code (4*k+3) ws ([true,true,false] ++ (CryptidBoundary.pairs q ++ (false::ys)))
    · simp [CryptidA.ab]
  rw [hi]
  rw [←preA_embed_ab]
  have hparam : 2 ≤ ((4*k+3)+CryptidA.wordInc ws) := by omega
  obtain ⟨u, hu⟩ : ∃ u, ((4*k+3)+CryptidA.wordInc ws) = u+2 := by
    exact ⟨((4*k+3)+CryptidA.wordInc ws)-2,by omega⟩
  rw [hu]
  exact two_one_pairs_return u q ys

#print axioms complete_A_word_two_one_pairs
end BB6.CryptidBridge
