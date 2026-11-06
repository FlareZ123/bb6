import Lean.Elab.Tactic.Omega
import EDouble
import E1101010111ThenA
import ABridgeCode
import BoundaryPadding

namespace BB6.Agent26EDoubleThenAZero

open CryptidBoundary
open BB6.BoundaryPadding

set_option maxHeartbeats 10000000
set_option maxRecDepth 4096
set_option linter.unusedSimpArgs false

def tripleTokens (u : Nat) : List Bool := List.replicate (2*u+2) true

private theorem first_to_A (t u : Nat) (ys : List Bool) :
    (⟨[],false,List.replicate (8*(3*t+2)+5) true ++
      (false :: List.replicate (2*((3*u+1)+1)+2) true ++
        (false :: List.replicate 6 true ++ ys)),5⟩ : Cfg) =
    init (List.replicate (3*(8*t+6)+1) true ++
      false :: (CryptidA.wordCode (tripleTokens u) ++
        false :: (List.replicate 6 true ++ ys))) := by
  rw [BB6.Agent26EThenA.tripleCode]
  have hn : 2*((3*u+1)+1)+2=3*(2*u+2) := by omega
  rw [hn]
  have hp : List.replicate (8*(3*t+2)+5) true =
      true :: true :: List.replicate (3*(8*t+6)+1) true := by
    have hnum : 8*(3*t+2)+5=2+(3*(8*t+6)+1) := by omega
    rw [hnum]
    calc
      _ = List.replicate 2 true ++
          List.replicate (3*(8*t+6)+1) true := by
            rw [List.replicate_append_replicate]
      _ = _ := by rfl
  rw [hp]
  rfl

/-- k=3t+2, L exceptional q=3u+3: exact second F/0 return is unary
    on an implicit blank, and preserves an arbitrary suffix after six ones. -/
theorem double_q0_then_A (t u : Nat) (ys : List Bool) :
    let ke := 3*t+2
    let ka := 8*t+6
    let ws := tripleTokens u
    let base := 4*ka+3
    let m := base+CryptidA.wordInc ws
    let timeE := 12*ke*ke+49*ke+64+4*(3*u+1)
    let timeA := (12*ka*ka+41*ka+32) +
      (CryptidA.wordCost base ws+(2*m+6))
    run (timeE+timeA)
      (init (List.replicate (3*ke+2) true ++
        false :: (pairs (3*u+2) ++
          ([true,true,false,false] ++ ys)))) =
      ⟨[],false,List.replicate (2*m+5) true ++
        (List.replicate 6 true ++ ys),5⟩ := by
  dsimp
  rw [run_add,BB6.Agent35.full_E_double (3*t+2) (3*u+1) ys]
  rw [first_to_A]
  exact BB6.Agent35.full_A_code (8*t+6)
    (tripleTokens u) (List.replicate 6 true ++ ys)

#print axioms double_q0_then_A

end BB6.Agent26EDoubleThenAZero
