import Lean.Elab.Tactic.Omega
import E1101010111ThenA

namespace BB6.Agent26EThenAFive

open CryptidBoundary
open BB6.Agent26E1101010111
open BB6.Agent26EThenB

set_option maxHeartbeats 10000000
set_option maxRecDepth 4096
set_option linter.unusedSimpArgs false

def fiveTokens (u : Nat) : List Bool :=
  List.replicate (2*u+3) true ++ List.replicate 5 false

theorem tripleFiveCode (r : Nat) :
    CryptidA.wordCode (List.replicate r true ++ List.replicate 5 false) =
      List.replicate (3*r) true ++
        [true,false,true,false,true,false,true,false,true,false] := by
  induction r with
  | zero => rfl
  | succ r ih =>
    change ([true,true,true] ++
      CryptidA.wordCode (List.replicate r true ++ List.replicate 5 false)) =
        List.replicate (3*(r+1)) true ++
          [true,false,true,false,true,false,true,false,true,false]
    rw [ih]
    have hn : 3*(r+1)=3+3*r := by omega
    rw [hn]
    rw [←List.replicate_append_replicate]
    rfl

private theorem e_to_a_five_section (t u : Nat) (ys : List Bool) :
    (⟨[],false,
      List.replicate (8*(3*t+2)+5) true ++ bWord (3*u+2) (false::ys),5⟩ : Cfg) =
    init (List.replicate (3*(8*t+6)+1) true ++
      false :: (CryptidA.wordCode (fiveTokens u) ++ false::ys)) := by
  rw [bWord_shape]
  rw [show fiveTokens u =
      List.replicate (2*u+3) true ++ List.replicate 5 false by rfl]
  rw [tripleFiveCode]
  have hp : List.replicate (8*(3*t+2)+5) true =
      true :: true :: List.replicate (3*(8*t+6)+1) true := by
    have hn : 8*(3*t+2)+5=2+(3*(8*t+6)+1) := by omega
    rw [hn]
    calc
      _ = List.replicate 2 true ++ List.replicate (3*(8*t+6)+1) true := by
        rw [List.replicate_append_replicate]
      _ = _ := by rfl
  have hq : List.replicate (2*(3*u+2)+6) true =
      List.replicate (3*(2*u+3)) true ++ [true] := by
    have hn : 2*(3*u+2)+6=3*(2*u+3)+1 := by omega
    rw [hn]
    rw [←List.replicate_append_replicate]
    rfl
  rw [hp,hq]
  simp [BB6.Agent26EThenB.tail, CryptidBoundary.init, List.append_assoc]

theorem e_then_a_five (t u : Nat) (ys : List Bool) :
    let ke := 3*t+2
    let qe := 3*u+2
    let ka := 8*t+6
    let ws := fiveTokens u
    let m := 4*ka+3
    let timeE := 12*ke*ke+49*ke+80+4*qe
    let timeA := (12*ka*ka+41*ka+32) +
      (CryptidA.wordCost m ws+(2*(m+CryptidA.wordInc ws)+6))
    run (timeE+timeA)
      (init (List.replicate (3*ke+2) true ++
        false :: (pairs qe ++ wordE (false::ys)))) =
      ⟨[],false,List.replicate (2*(m+CryptidA.wordInc ws)+5) true ++ ys,5⟩ := by
  dsimp
  rw [run_add, full_E_1101010111_pairs (3*t+2) (3*u+2) (false::ys)]
  rw [e_to_a_five_section]
  exact BB6.Agent35.full_A_code (8*t+6) (fiveTokens u) ys

#print axioms tripleFiveCode
#print axioms e_then_a_five

end BB6.Agent26EThenAFive
