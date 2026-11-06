import Lean.Elab.Tactic.Omega
import EZeroPair
import ABridgeCode

namespace BB6.Agent26EOnePair

open CryptidBoundary
open BB6.Agent32EZero

set_option maxHeartbeats 10000000
set_option maxRecDepth 4096
set_option linter.unusedSimpArgs false

/-- One 111 token followed by four 10 tokens. -/
def fourCloseCode : List Bool := [true,false,false,false,false]

def afterFirst : List Bool :=
  [true,true,true,true,false,true,false,true,false,true,false]

theorem packet0 (ys : List Bool) :
    packetZero ++ false :: ys = false :: (afterFirst ++ false :: ys) := by
  rfl

theorem afterFirst_code :
    afterFirst = CryptidA.wordCode fourCloseCode := by
  rfl

private theorem e_to_a_section (t : Nat) (ys : List Bool) :
    (⟨[],false,List.replicate (8*(3*t)+3) true ++
      (packetZero ++ false :: ys),5⟩ : Cfg) =
    init (List.replicate (3*(8*t)+1) true ++
      false :: (CryptidA.wordCode fourCloseCode ++ false :: ys)) := by
  rw [packet0,← afterFirst_code]
  have hp : List.replicate (8*(3*t)+3) true =
      true :: true :: List.replicate (3*(8*t)+1) true := by
    have hn : 8*(3*t)+3=2+(3*(8*t)+1) := by omega
    rw [hn]
    calc
      _ = List.replicate 2 true ++ List.replicate (3*(8*t)+1) true := by
        rw [List.replicate_append_replicate]
      _ = _ := by rfl
  rw [hp]
  rfl

/-- The one-pair exceptional E entry with k=3t has a second return
    on the original D machine through universal A code, for every
    arbitrary suffix beyond the three explicit padding zeros. -/
theorem e_two_A (t : Nat) (ys : List Bool) :
    run ((12*(3*t)*(3*t)+49*(3*t)+96)+
      ((12*(8*t)*(8*t)+41*(8*t)+32)+
        (CryptidA.wordCost (4*(8*t)+3) fourCloseCode +
          (2*((4*(8*t)+3)+CryptidA.wordInc fourCloseCode)+6))))
      (init (List.replicate (3*(3*t)+2) true ++
        false :: ([true,true,false,false,false] ++ ys))) =
      ⟨[],false,List.replicate
        (2*((4*(8*t)+3)+CryptidA.wordInc fourCloseCode)+5) true ++ ys,5⟩ := by
  rw [run_add]
  change run _ (run (12*(3*t)*(3*t)+49*(3*t)+96)
    (init (List.replicate (3*(3*t)+2) true ++
      false :: ([true,true,false,false] ++ false::ys)))) = _
  rw [full_E_zero_pairs (3*t) (false::ys)]
  rw [e_to_a_section]
  exact BB6.Agent35.full_A_code (8*t) fourCloseCode ys

#print axioms e_two_A

end BB6.Agent26EOnePair
