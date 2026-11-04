import Lean.Elab.Tactic.Omega
import CryptidPairs
import A1100

namespace BB6.Agent26A110101

open CryptidBoundary

set_option maxHeartbeats 10000000
set_option maxRecDepth 4096

/-- Uniform eight-symbol terminal, irrespective of the remaining stack. -/
theorem a_eight_start (m : Nat) (ys : List Bool) :
    run 27 (aBoundary m
       ([true,true,false,true,false,true,true,true] ++ ys)) =
      sweepD m ([true,true,false,true,false,true,false,true,false] ++ ys) := by
  simp [aBoundary, sweepD, run, step, goL, goR, pairs]

theorem a_eight_return (m : Nat) (ys : List Bool) :
    run (2*m+30) (aBoundary m
       ([true,true,false,true,false,true,true,true] ++ ys)) =
      ⟨[], false, List.replicate (2*m+5) true ++
        ([false,true,false,true,false,true,false] ++ ys), 5⟩ := by
  have ht : 2*m+30 = 27+(2*m+3) := by omega
  rw [ht, run_add, a_eight_start, sweepD_run]
  have hp :
      List.replicate (2*m+3) true ++
        ([true,true,false,true,false,true,false,true,false] ++ ys) =
      List.replicate (2*m+5) true ++
        ([false,true,false,true,false,true,false] ++ ys) := by
    calc
      _ = (List.replicate (2*m+3) true ++ List.replicate 2 true) ++
            ([false,true,false,true,false,true,false] ++ ys) := by
              simp [List.append_assoc]
      _ = List.replicate ((2*m+3)+2) true ++
            ([false,true,false,true,false,true,false] ++ ys) := by
              rw [List.replicate_append_replicate]
      _ = _ := by rw [show 2*m+3+2=2*m+5 by omega]
  exact congrArg (fun z : List Bool => Cfg.mk [] false z 5) hp

/-- Ten-symbol terminal with a 14-one intermediate output. The source
    stack has length m+1, making this statement valid for every m≥0. -/
theorem a_ten_start (m : Nat) (ys : List Bool) :
    run 31 (aBoundary (m+1)
       ([true,true,false,true,false,true,false,true,false,true] ++ ys)) =
      sweepB m (false :: List.replicate 14 true ++ ys) := by
  cases m with
  | zero => simp [aBoundary, sweepB, run, step, goL, goR, pairs, List.replicate]
  | succ m => simp [aBoundary, sweepB, run, step, goL, goR, pairs, List.replicate]

theorem a_ten_return (m : Nat) (ys : List Bool) :
    run (2*m+34) (aBoundary (m+1)
       ([true,true,false,true,false,true,false,true,false,true] ++ ys)) =
      ⟨[], false, List.replicate (2*m+3) true ++
        (false :: List.replicate 14 true ++ ys), 5⟩ := by
  have ht : 2*m+34 = 31+(2*m+3) := by omega
  rw [ht, run_add, a_ten_start, sweepB_run]

#print axioms a_eight_return
#print axioms a_ten_return
end BB6.Agent26A110101
