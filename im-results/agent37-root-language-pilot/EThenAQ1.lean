import Lean.Elab.Tactic.Omega
import EThenAGuarded
import A110101Closure

namespace BB6.Agent37EThenAQ1

open CryptidBoundary
open BB6.Agent26E1101010111
open BB6.Agent26EThenB

set_option maxHeartbeats 10000000
set_option maxRecDepth 4096
set_option linter.unusedSimpArgs false

/-- A forced zero immediately after the corrected E marker completes the
    all-natural A terminal pattern 110101010100 at q=3u+1. -/
theorem guarded_suffix_q1 (u : Nat) (ys : List Bool) :
    List.replicate (2*(3*u+1)+6) true ++ tail (false::ys) =
    CryptidA.wordCode (List.replicate (2*u+2) true) ++
      ([true,true,false,true,false,true,false,true,false,true,false,false] ++ ys) := by
  rw [BB6.Agent26EThenA.tripleCode]
  have hn : 2*(3*u+1)+6 = 3*(2*u+2)+2 := by omega
  rw [hn, ← List.replicate_append_replicate]
  simp [tail, List.replicate_succ, List.append_assoc]

/-- A complete source F/0 section after the first E return, retaining the
    extra zero required by the corrected guarded A theorem. -/
theorem e_to_a_q1 (t u : Nat) (ys : List Bool) :
    (⟨[],false,List.replicate (8*(3*t+2)+5) true ++
      bWord (3*u+1) (false::ys),5⟩ : Cfg) =
    init (List.replicate (3*(8*t+6)+1) true ++
      false :: (CryptidA.wordCode (List.replicate (2*u+2) true) ++
        ([true,true,false,true,false,true,false,true,false,true,false,false] ++ ys))) := by
  rw [bWord_shape, guarded_suffix_q1]
  have hrep : List.replicate (8*(3*t+2)+5) true =
      true :: true :: List.replicate (3*(8*t+6)+1) true := by
    have hn : 8*(3*t+2)+5=2+(3*(8*t+6)+1) := by omega
    rw [hn]
    calc
      _ = List.replicate 2 true ++
            List.replicate (3*(8*t+6)+1) true := by
              rw [List.replicate_append_replicate]
      _ = _ := by rfl
  rw [hrep]
  rfl

/-- For k=3t+2 and q=3u+1, all input suffixes prefixed with 0
    have two exact F/0 returns.  The guard is essential. -/
theorem e_then_a_guarded_q1 (t u : Nat) (ys : List Bool) :
    let ke := 3*t+2
    let qe := 3*u+1
    let ka := 8*t+6
    let ws := List.replicate (2*u+2) true
    let m := 4*ka+3
    let mclose := 4*ka+2+CryptidA.wordInc ws
    let timeE := 12*ke*ke+49*ke+80+4*qe
    let timeA := (12*ka*ka+41*ka+32) +
      (CryptidA.wordCost m ws+(2*mclose+34))
    run (timeE+timeA)
      (init (List.replicate (3*ke+2) true ++
        false :: (pairs qe ++ wordE (false::ys)))) =
      ⟨[],false,List.replicate (2*mclose+3) true ++
          (false :: List.replicate 14 true ++ ys),5⟩ := by
  dsimp
  rw [run_add, full_E_1101010111_pairs (3*t+2) (3*u+1) (false::ys)]
  rw [e_to_a_q1]
  rw [run_add, prefix_A]
  change run
    (CryptidA.wordCost (4*(8*t+6)+3) (List.replicate (2*u+2) true) +
      (2*(4*(8*t+6)+2+CryptidA.wordInc (List.replicate (2*u+2) true))+34))
    (BB6.Agent35.aBoundary (4*(8*t+6)+3)
      (CryptidA.wordCode (List.replicate (2*u+2) true) ++
        ([true,true,false,true,false,true,false,true,false,true,false,false] ++ ys))) = _
  rw [run_add, BB6.Agent35.a_code_return]
  have hm : 4*(8*t+6)+3+CryptidA.wordInc (List.replicate (2*u+2) true) =
    (4*(8*t+6)+2+CryptidA.wordInc (List.replicate (2*u+2) true))+1 := by omega
  rw [hm]
  exact BB6.Agent26A110101.a_ten_return
    (4*(8*t+6)+2+CryptidA.wordInc (List.replicate (2*u+2) true)) ys

#print axioms guarded_suffix_q1
#print axioms e_to_a_q1
#print axioms e_then_a_guarded_q1

end BB6.Agent37EThenAQ1
