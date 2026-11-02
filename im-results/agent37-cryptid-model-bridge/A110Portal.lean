import ShortTripleGate
import EZeroPair
import Lean.Elab.Tactic.Omega

namespace BB6.CryptidBridge

/-- The exact E-boundary configuration reached from any A-boundary right
    prefix 110, for all left-stack sizes and arbitrary remaining right tape. -/
def eAfter110 (m : Nat) (ys : List Bool) : CryptidBoundary.Cfg :=
  ⟨false::false::CryptidBoundary.pairs (m+1) ++ [true,true],
    false,ys,4⟩

/-- Unconditional three-step source-level A→E bridge, with no restriction
    whatsoever on the suffix following the three marker bits. -/
theorem a110_to_E (m : Nat) (ys : List Bool) :
    CryptidBoundary.run 3
      (CryptidBoundary.preA m ([true,true,false] ++ ys)) =
    eAfter110 m ys := by
  simp [CryptidBoundary.preA,eAfter110,CryptidBoundary.run,
    CryptidBoundary.step,CryptidBoundary.goL,CryptidBoundary.goR,
    CryptidBoundary.pairs]

/-- Any exact source E-boundary run is automatically an A-boundary run,
    with three additional steps. This is a reusable proof-transfer rule. -/
theorem lift_A110 (m t : Nat) (ys : List Bool)
    (out : CryptidBoundary.Cfg)
    (h : CryptidBoundary.run t (eAfter110 m ys) = out) :
    CryptidBoundary.run (3+t)
      (CryptidBoundary.preA m ([true,true,false] ++ ys)) = out := by
  rw [CryptidBoundary.run_add,a110_to_E]
  exact h

/-- The once-exceptional E-on-1100 is reached from A-on-1101100. -/
theorem a_1101100_to_eZero (m : Nat) (ys : List Bool) :
    CryptidBoundary.run 3
      (CryptidBoundary.preA (m+2)
        ([true,true,false] ++ ([true,true,false,false] ++ ys))) =
    BB6.Agent32EZero.eZero m ys := by
  rw [a110_to_E]
  simp [eAfter110,BB6.Agent32EZero.eZero,
    show (m+2)+1=m+3 by omega]

/-- A productive A-boundary branch for all m≥2 and arbitrary tail. -/
theorem a_1101100_return (m : Nat) (ys : List Bool) :
    CryptidBoundary.run (2*m+66)
      (CryptidBoundary.preA (m+2)
        ([true,true,false] ++ ([true,true,false,false] ++ ys))) =
    ⟨[],false,
      List.replicate (2*m+3) true ++
        (BB6.Agent32EZero.packetZero ++ ys),5⟩ := by
  have ht : 2*m+66=3+(2*m+63) := by omega
  rw [ht,CryptidBoundary.run_add,a_1101100_to_eZero,
    BB6.Agent32EZero.eZero_run]

/-- All-word F-to-F A return for the once-exceptional 1101100 branch.
    This is the exact original source machine, including frozen halting. -/
theorem complete_A_word_1101100 (k : Nat) (ws ys : List Bool) :
    CryptidBoundary.run
      ((12*k*k+41*k+32) +
        (CryptidA.wordCost (4*k+3) ws +
          (2*((4*k+3)+CryptidA.wordInc ws)+62)))
      (CryptidBoundary.init
        (List.replicate (3*k+1) true ++
         false :: (CryptidA.wordCode ws ++
           ([true,true,false] ++ ([true,true,false,false] ++ ys))))) =
    ⟨[],false,
      List.replicate (2*((4*k+1)+CryptidA.wordInc ws)+3) true ++
        (BB6.Agent32EZero.packetZero ++ ys),5⟩ := by
  rw [CryptidBoundary.run_add,CryptidBoundary.prefix_A]
  change CryptidBoundary.run
    (CryptidA.wordCost (4*k+3) ws +
      (2*((4*k+3)+CryptidA.wordInc ws)+62))
    (CryptidBoundary.preA (4*k+3)
      (CryptidA.wordCode ws ++
        ([true,true,false] ++ ([true,true,false,false] ++ ys)))) = _
  rw [preA_embed_ab]
  rw [CryptidBoundary.run_add]
  have hi : CryptidBoundary.run (CryptidA.wordCost (4*k+3) ws)
      (embed (CryptidA.ab (4*k+3)
        (CryptidA.wordCode ws ++
          ([true,true,false] ++ ([true,true,false,false] ++ ys))))) =
      embed (CryptidA.ab ((4*k+3)+CryptidA.wordInc ws)
        ([true,true,false] ++ ([true,true,false,false] ++ ys))) := by
    apply transfer_nonF
    · simp [CryptidA.ab]
    · exact CryptidA.consume_code (4*k+3) ws
        ([true,true,false] ++ ([true,true,false,false] ++ ys))
    · simp [CryptidA.ab]
  rw [hi]
  rw [←preA_embed_ab]
  have ht : 2*((4*k+3)+CryptidA.wordInc ws)+62 =
      2*((4*k+1)+CryptidA.wordInc ws)+66 := by omega
  rw [ht]
  have hm : (4*k+3)+CryptidA.wordInc ws =
      ((4*k+1)+CryptidA.wordInc ws)+2 := by omega
  rw [hm]
  exact a_1101100_return ((4*k+1)+CryptidA.wordInc ws) ys

#print axioms a110_to_E
#print axioms lift_A110
#print axioms a_1101100_return
#print axioms complete_A_word_1101100
end BB6.CryptidBridge
