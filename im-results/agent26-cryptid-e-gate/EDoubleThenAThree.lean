import Lean.Elab.Tactic.Omega
import EDouble
import A110111
import E1101010111ThenA
import ABridgeCode

namespace BB6.Agent26EDoubleThenA

open CryptidBoundary

set_option maxHeartbeats 10000000
set_option maxRecDepth 4096
set_option linter.unusedSimpArgs false

def tripleTokens (u : Nat) : List Bool :=
  List.replicate (2*u+2) true

private theorem a_terminal (m : Nat) (ys : List Bool) (hm : 3 ≤ m) :
    run (2*m+24)
      (BB6.Agent35.aBoundary m
        ([true,true,false,true,true,true] ++ ys)) =
      ⟨[],false,List.replicate (2*m+5) true ++
        ([false,true,false,true,false] ++ ys),5⟩ := by
  have h := a110111_run (m-3) ys
  have hadd : m-3+3=m := by omega
  rw [hadd] at h
  change run (2*m+24)
    (aBoundary m ([true,true,false,true,true,true] ++ ys)) = _
  exact h

/-- An arbitrary finite 10/111 A-code prefix followed by 110111
    has an explicit original-source F/0 return for every suffix. -/
theorem a_code_110111 (ka : Nat) (ws ys : List Bool) :
    let base := 4*ka+3
    let m := base+CryptidA.wordInc ws
    run ((12*ka*ka+41*ka+32) +
      (CryptidA.wordCost base ws+(2*m+24)))
      (init (List.replicate (3*ka+1) true ++
        false :: (CryptidA.wordCode ws ++
          ([true,true,false,true,true,true] ++ ys)))) =
      ⟨[],false,List.replicate (2*m+5) true ++
        ([false,true,false,true,false] ++ ys),5⟩ := by
  dsimp
  rw [run_add,prefix_A]
  change run
    (CryptidA.wordCost (4*ka+3) ws +
       (2*(4*ka+3+CryptidA.wordInc ws)+24))
    (BB6.Agent35.aBoundary (4*ka+3)
      (CryptidA.wordCode ws ++
        ([true,true,false,true,true,true] ++ ys))) = _
  rw [run_add,BB6.Agent35.a_code_return]
  apply a_terminal
  omega

private theorem first_to_A (t u : Nat) (ys : List Bool) :
    (⟨[],false,List.replicate (8*(3*t+2)+5) true ++
      (false :: List.replicate (2*((3*u+2)+1)+2) true ++
        (false :: List.replicate 6 true ++ ys)),5⟩ : Cfg) =
    init (List.replicate (3*(8*t+6)+1) true ++
      false :: (CryptidA.wordCode (tripleTokens u) ++
        ([true,true,false,true,true,true] ++
          ([true,true,true] ++ ys)))) := by
  unfold tripleTokens
  rw [BB6.Agent26EThenA.tripleCode]
  have hn : 2*((3*u+2)+1)+2=3*(2*u+2)+2 := by omega
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
  simp [tripleTokens,CryptidBoundary.init,List.append_assoc]

/-- For k=3t+2 and L exception q=3u+4, second return recovers
    exactly an L word, including arbitrary tail beyond the sixth one. -/
theorem double_q1_then_A (t u : Nat) (ys : List Bool) :
    let ke := 3*t+2
    let ka := 8*t+6
    let ws := tripleTokens u
    let base := 4*ka+3
    let m := base+CryptidA.wordInc ws
    let timeE := 12*ke*ke+49*ke+64+4*(3*u+2)
    let timeA := (12*ka*ka+41*ka+32) +
      (CryptidA.wordCost base ws+(2*m+24))
    run (timeE+timeA)
      (init (List.replicate (3*ke+2) true ++
        false :: (pairs (3*u+3) ++
          ([true,true,false,false] ++ ys)))) =
      ⟨[],false,List.replicate (2*m+5) true ++
        ([false,true,false,true,false,true,true,true] ++ ys),5⟩ := by
  dsimp
  rw [show 3*u+3=(3*u+2)+1 by omega]
  rw [run_add,BB6.Agent35.full_E_double (3*t+2) (3*u+2) ys]
  rw [first_to_A]
  exact a_code_110111 (8*t+6) (tripleTokens u)
    ([true,true,true] ++ ys)

#print axioms a_code_110111
#print axioms double_q1_then_A

end BB6.Agent26EDoubleThenA
