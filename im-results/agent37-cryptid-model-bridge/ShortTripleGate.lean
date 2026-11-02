import WordReturns
import CryptidThree
import Lean.Elab.Tactic.Omega

namespace BB6.CryptidBridge

/-- The A boundary already closes after the six-cell prefix 110111.
    After three primitive steps it is exactly Agent32's universal E-three state. -/
theorem short_three_to_E (m : Nat) (ys : List Bool) :
    CryptidBoundary.run 3
      (CryptidBoundary.preA m
        ([true,true,false] ++ ([true,true,true] ++ ys))) =
    CryptidBoundary.eThree (m+1) ys := by
  simp [CryptidBoundary.preA, CryptidBoundary.eThree,
    CryptidBoundary.run,CryptidBoundary.step,
    CryptidBoundary.goL,CryptidBoundary.goR,
    CryptidBoundary.pairs,List.append_assoc]

/-- Every 110111 A boundary closes, leaving the entire trailing suffix intact.
    This applies to every natural m, not only the m=4k+3 family. -/
theorem short_three_return (m : Nat) (ys : List Bool) :
    CryptidBoundary.run (2*m+24)
      (CryptidBoundary.preA m
        ([true,true,false] ++ ([true,true,true] ++ ys))) =
    ⟨[],false,
      List.replicate (2*m+5) true ++
        (CryptidBoundary.packetThree ++ ys),5⟩ := by
  have ht : 2*m+24 = 3+(2*(m+1)+19) := by omega
  rw [ht,CryptidBoundary.run_add,short_three_to_E,
      CryptidBoundary.eThree_run]
  rw [show 2*(m+1)+3=2*m+5 by omega]

/-- Genuine six-state F-to-F return after any interleaved 10/111 code word
    and the short 110111 gate. The 4-bit tail of the earlier A-six gate
    is now an arbitrary, untouched right suffix. -/
theorem complete_A_word_short_three (k : Nat) (ws ys : List Bool) :
    CryptidBoundary.run
      ((12*k*k+41*k+32) +
        (CryptidA.wordCost (4*k+3) ws +
          (2*((4*k+3)+CryptidA.wordInc ws)+24)))
      (CryptidBoundary.init
        (List.replicate (3*k+1) true ++
         false :: (CryptidA.wordCode ws ++
           ([true,true,false] ++ ([true,true,true] ++ ys))))) =
    ⟨[],false,
      List.replicate (2*((4*k+3)+CryptidA.wordInc ws)+5) true ++
        (CryptidBoundary.packetThree ++ ys),5⟩ := by
  rw [CryptidBoundary.run_add,CryptidBoundary.prefix_A]
  change CryptidBoundary.run
    (CryptidA.wordCost (4*k+3) ws +
      (2*((4*k+3)+CryptidA.wordInc ws)+24))
    (CryptidBoundary.preA (4*k+3)
      (CryptidA.wordCode ws ++
        ([true,true,false] ++ ([true,true,true] ++ ys)))) = _
  rw [preA_embed_ab]
  rw [CryptidBoundary.run_add]
  have hi : CryptidBoundary.run (CryptidA.wordCost (4*k+3) ws)
      (embed (CryptidA.ab (4*k+3)
        (CryptidA.wordCode ws ++
          ([true,true,false] ++ ([true,true,true] ++ ys))))) =
      embed (CryptidA.ab ((4*k+3)+CryptidA.wordInc ws)
        ([true,true,false] ++ ([true,true,true] ++ ys))) := by
    apply transfer_nonF
    · simp [CryptidA.ab]
    · exact CryptidA.consume_code (4*k+3) ws
        ([true,true,false] ++ ([true,true,true] ++ ys))
    · simp [CryptidA.ab]
  rw [hi]
  rw [←preA_embed_ab]
  exact short_three_return ((4*k+3)+CryptidA.wordInc ws) ys

#print axioms short_three_to_E
#print axioms short_three_return
#print axioms complete_A_word_short_three
end BB6.CryptidBridge
