import Lean.Elab.Tactic.Omega
import E1111First
import E1101010111First

namespace BB6.Agent26EThenEFirst

open CryptidBoundary
open BB6.Agent26EFour
open BB6.Agent26EFourFirst
open BB6.Agent26E1101010111
open BB6.Agent26E1101010111First
open BB6.Agent26EThenB

set_option maxHeartbeats 12000000
set_option maxRecDepth 4096

/-- Every positive-time physical F/0 encounter in this two-return interval
    is one of the two displayed exact return endpoints. -/
theorem e_then_e_two_first_returns (t q : Nat) (ys : List Bool) :
    let durationE := 12*(3*t+1)*(3*t+1)+49*(3*t+1)+80+4*q
    let durationNext := 12*(8*t+3)*(8*t+3)+49*(8*t+3)+58
    let initial := init (List.replicate (3*(3*t+1)+2) true ++
        false :: (pairs q ++ wordE ys))
    run (durationE+durationNext) initial =
      ⟨[],false,
        [true,true,true,true] ++
          (List.replicate (2*((4*(8*t+3)+1)+1)) true ++
            restTail (List.replicate (2*q+2) true ++ tail ys)),5⟩
    ∧ (∀ s, 0<s → s<durationE → ¬ Physical (run s initial))
    ∧ (∀ s, durationE<s → s<durationE+durationNext →
         ¬ Physical (run s initial)) := by
  dsimp
  constructor
  · exact e_then_e t q ys
  constructor
  · exact (full_E_1101010111_first_return (3*t+1) q ys).2
  · intro s hafter hbefore hphys
    have heq :=
      (full_E_1101010111_first_return (3*t+1) q ys).1
    have htime : s =
        (12*(3*t+1)*(3*t+1)+49*(3*t+1)+80+4*q) +
          (s-(12*(3*t+1)*(3*t+1)+49*(3*t+1)+80+4*q)) := by
      omega
    have hspos :
        0<s-(12*(3*t+1)*(3*t+1)+49*(3*t+1)+80+4*q) := by
      omega
    have hsbound :
        s-(12*(3*t+1)*(3*t+1)+49*(3*t+1)+80+4*q) <
          12*(8*t+3)*(8*t+3)+49*(8*t+3)+58 := by omega
    rw [htime,run_add,heq,next_e] at hphys
    exact
      ((full_E_four_first_return (8*t+3)
          (List.replicate (2*q+2) true ++ tail ys)).2
        (s-(12*(3*t+1)*(3*t+1)+49*(3*t+1)+80+4*q))
        hspos hsbound) hphys.1

#print axioms e_then_e_two_first_returns

end BB6.Agent26EThenEFirst
