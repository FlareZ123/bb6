import Lean.Elab.Tactic.Omega
import E1101010111ThenA
import A110101Closure

namespace BB6.Agent26EThenAQ1

open CryptidBoundary
open BB6.Agent26E1101010111
open BB6.Agent26EThenB

set_option maxHeartbeats 10000000
set_option maxRecDepth 4096
set_option linter.unusedSimpArgs false

def tripleTokens (u : Nat) : List Bool :=
  List.replicate (2*u+2) true

def tenTerminal (ys : List Bool) : List Bool :=
  [true,true,false,true,false,true,false,true,false,true,false,false] ++ ys

private theorem e_to_a_three_section (t u : Nat) (ys : List Bool) :
    (⟨[],false,List.replicate (8*(3*t+2)+5) true ++
      bWord (3*u+1) (false::ys),5⟩ : Cfg) =
    init (List.replicate (3*(8*t+6)+1) true ++
      false :: (CryptidA.wordCode (tripleTokens u) ++ tenTerminal ys)) := by
  rw [bWord_shape]
  rw [show tripleTokens u = List.replicate (2*u+2) true by rfl]
  rw [BB6.Agent26EThenA.tripleCode]
  have hp : List.replicate (8*(3*t+2)+5) true =
      true :: true :: List.replicate (3*(8*t+6)+1) true := by
    have hn : 8*(3*t+2)+5=2+(3*(8*t+6)+1) := by omega
    rw [hn]
    calc
      _ = List.replicate 2 true ++ List.replicate (3*(8*t+6)+1) true := by
        rw [List.replicate_append_replicate]
      _ = _ := by rfl
  have hq : List.replicate (2*(3*u+1)+6) true =
      List.replicate (3*(2*u+2)) true ++ [true,true] := by
    have hn : 2*(3*u+1)+6=3*(2*u+2)+2 := by omega
    rw [hn]
    rw [←List.replicate_append_replicate]
    rfl
  rw [hp,hq]
  simp [BB6.Agent26EThenB.tail, tenTerminal, CryptidBoundary.init, List.append_assoc]

/-- All t,u,suffixes after an explicit zero, q=3u+1: E return is
    followed by an A-code run ending at a guarded A terminal. -/
theorem e_then_a_q1 (t u : Nat) (ys : List Bool) :
    let ke := 3*t+2
    let qe := 3*u+1
    let ka := 8*t+6
    let ws := tripleTokens u
    let base := 4*ka+3
    let m := base+CryptidA.wordInc ws
    let timeE := 12*ke*ke+49*ke+80+4*qe
    let timeA := (12*ka*ka+41*ka+32) +
      (CryptidA.wordCost base ws+(2*(m-1)+34))
    run (timeE+timeA)
      (init (List.replicate (3*ke+2) true ++
        false :: (pairs qe ++ wordE (false::ys)))) =
      ⟨[],false,List.replicate (2*(m-1)+3) true ++
        (false :: List.replicate 14 true ++ ys),5⟩ := by
  dsimp
  rw [run_add, full_E_1101010111_pairs (3*t+2) (3*u+1) (false::ys)]
  rw [e_to_a_three_section]
  rw [run_add, prefix_A]
  change run (CryptidA.wordCost (4*(8*t+6)+3) (tripleTokens u) +
    (2*((4*(8*t+6)+3+CryptidA.wordInc (tripleTokens u))-1)+34))
    (⟨false :: pairs (4*(8*t+6)+3) ++ [true,true], false,
      CryptidA.wordCode (tripleTokens u) ++ tenTerminal ys,0⟩ : Cfg) = _
  change run (CryptidA.wordCost (4*(8*t+6)+3) (tripleTokens u) +
    (2*((4*(8*t+6)+3+CryptidA.wordInc (tripleTokens u))-1)+34))
    (BB6.Agent35.aBoundary (4*(8*t+6)+3)
      (CryptidA.wordCode (tripleTokens u) ++ tenTerminal ys)) = _
  rw [run_add, BB6.Agent35.a_code_return]
  have hm : ((4*(8*t+6)+3+CryptidA.wordInc (tripleTokens u))-1)+1 =
      (4*(8*t+6)+3+CryptidA.wordInc (tripleTokens u)) := by omega
  have hs := BB6.Agent26A110101.a_ten_return
      ((4*(8*t+6)+3+CryptidA.wordInc (tripleTokens u))-1) ys
  rw [hm] at hs
  change run (2*((4*(8*t+6)+3+CryptidA.wordInc (tripleTokens u))-1)+34)
    (aBoundary (4*(8*t+6)+3+CryptidA.wordInc (tripleTokens u)) (tenTerminal ys)) = _
  simpa [tenTerminal] using hs

#print axioms e_then_a_q1

end BB6.Agent26EThenAQ1
