import Lean.Elab.Tactic.Omega
import EOnePairTwoReturnsA
import EFourAlternating

namespace BB6.Agent26EOnePair

open CryptidBoundary
open BB6.Agent32EZero
open BB6.Agent26EFour

set_option maxHeartbeats 10000000
set_option maxRecDepth 4096
set_option linter.unusedSimpArgs false

private theorem e_to_b_section (t : Nat) (ys : List Bool) :
    (⟨[],false,List.replicate (8*(3*t+1)+3) true ++
      (packetZero ++ false :: ys),5⟩ : Cfg) =
    init (List.replicate (3*(8*t+3)) true ++
      false :: (afterFirst ++ false :: ys)) := by
  rw [packet0]
  have hp : List.replicate (8*(3*t+1)+3) true =
      true :: true :: List.replicate (3*(8*t+3)) true := by
    have hn : 8*(3*t+1)+3=2+3*(8*t+3) := by omega
    rw [hn]
    calc
      _ = List.replicate 2 true ++ List.replicate (3*(8*t+3)) true := by
        rw [List.replicate_append_replicate]
      _ = _ := by rfl
  rw [hp]
  rfl

theorem e_two_B (t : Nat) (ys : List Bool) :
    run ((12*(3*t+1)*(3*t+1)+49*(3*t+1)+96)+
      (12*(8*t+3)*(8*t+3)+49*(8*t+3)+40))
      (init (List.replicate (3*(3*t+1)+2) true ++
        false :: ([true,true,false,false,false] ++ ys))) =
      ⟨[],false,List.replicate (8*(8*t+3)+9) true ++
        (afterFirst ++ false :: ys),5⟩ := by
  rw [run_add]
  change run _ (run (12*(3*t+1)*(3*t+1)+49*(3*t+1)+96)
    (init (List.replicate (3*(3*t+1)+2) true ++
      false :: ([true,true,false,false] ++ false::ys)))) = _
  rw [full_E_zero_pairs (3*t+1) (false::ys)]
  rw [e_to_b_section]
  exact full_B (8*t+3) (afterFirst ++ false::ys)

private theorem e_to_e_section (t : Nat) (ys : List Bool) :
    (⟨[],false,List.replicate (8*(3*t+2)+3) true ++
      (packetZero ++ false :: ys),5⟩ : Cfg) =
    init (List.replicate (3*(8*t+5)+2) true ++
      false :: (fourWord ++ false :: ys)) := by
  rw [packet0]
  have hp : List.replicate (8*(3*t+2)+3) true =
      true :: true :: List.replicate (3*(8*t+5)+2) true := by
    have hn : 8*(3*t+2)+3=2+(3*(8*t+5)+2) := by omega
    rw [hn]
    calc
      _ = List.replicate 2 true ++ List.replicate (3*(8*t+5)+2) true := by
        rw [List.replicate_append_replicate]
      _ = _ := by rfl
  rw [hp]
  rfl

theorem e_two_E (t : Nat) (ys : List Bool) :
    run ((12*(3*t+2)*(3*t+2)+49*(3*t+2)+96)+
      (12*(8*t+5)*(8*t+5)+49*(8*t+5)+58))
      (init (List.replicate (3*(3*t+2)+2) true ++
        false :: ([true,true,false,false,false] ++ ys))) =
      ⟨[],false,List.replicate (8*(8*t+5)+9) true ++
        (sixPairsZero ++ false :: ys),5⟩ := by
  rw [run_add]
  change run _ (run (12*(3*t+2)*(3*t+2)+49*(3*t+2)+96)
    (init (List.replicate (3*(3*t+2)+2) true ++
      false :: ([true,true,false,false] ++ false::ys)))) = _
  rw [full_E_zero_pairs (3*t+2) (false::ys)]
  rw [e_to_e_section]
  exact full_E_four (8*t+5) (false::ys)

#print axioms e_two_B
#print axioms e_two_E

end BB6.Agent26EOnePair
