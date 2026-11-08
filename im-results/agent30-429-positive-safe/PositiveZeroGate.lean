import PhysicalSafe
import Lean.Elab.Tactic.Omega

set_option maxRecDepth 8192
set_option maxHeartbeats 30000000

namespace BB429PositiveZeroGate
open BB429OddExcursion BB429SourceE1Return
open BB429FinishScanEDelta BB429JuncHeadExcursion
open BB429W4CZeroSafe BB429PositiveSafe

private theorem ones_add (m n : Nat) : ones (m+n) = ones m ++ ones n := by
  induction m with
  | zero => simp [ones]
  | succ m ih => simp [ones, Nat.succ_add, List.replicate_succ]

private theorem pairs01_succ_append (n : Nat) :
    pairs01 n ++ [false,true] = pairs01 (n+1) := by
  induction n with
  | zero => rfl
  | succ n ih =>
      change false :: true :: (pairs01 n ++ [false,true]) =
        false :: true :: pairs01 (n+1)
      rw [ih]

private theorem ones_three_left (n : Nat) (rest : List Bool) :
    ones n ++ (true :: true :: true :: rest) =
      true :: (ones (n+2) ++ rest) := by
  have hp : ones n ++ [true,true,true] = true :: ones (n+2) := by
    calc
      ones n ++ [true,true,true] = ones (n+3) := by
        rw [ones_add]
        rfl
      _ = ones (1+(n+2)) := by congr 1 <;> omega
      _ = true :: ones (n+2) := by rw [ones_add]; rfl
  calc
    ones n ++ (true::true::true::rest) =
        (ones n ++ [true,true,true]) ++ rest := by
      rw [List.append_assoc]
      rfl
    _ = (true::ones (n+2)) ++ rest := by rw [hp]
    _ = true :: (ones (n+2) ++ rest) := rfl

/-- A/0, B/1 shift consuming a final 01 pair contains no C/0 instruction.
    It leaves an A/0 current with a single right one, for arbitrary length. -/
theorem a01_tail_shift_safe (v : Nat) (left : List Bool) :
    runSafe (2*(v+1)) (z 0 left false (true :: pairs01 (v+1))) =
      some (z 0 (ones (2*(v+1)) ++ left) false [true]) := by
  induction v generalizing left with
  | zero =>
      simpa [pairs01,ones] using (a01_pair_safe left [false,true])
  | succ v ih =>
      have hpair : runSafe 2
          (z 0 left false (true :: pairs01 (v+2))) =
          some (z 0 (true :: true :: left) false (true :: pairs01 (v+1))) := by rfl
      rw [show 2*(v+2)=2+2*(v+1) by omega,runSafe_add,hpair]
      simp only [Option.bind_some]
      rw [ih (true :: true :: left)]
      have hout : ones (2*(v+2)) ++ left =
          ones (2*(v+1)) ++ (true :: true :: left) := by
        rw [show 2*(v+2)=2*(v+1)+2 by omega,ones_add]
        simp [ones,List.append_assoc]
      rw [← hout, show 2+2*(v+1)=2*(v+2) by omega]

/-- Four further instructions reach C/0 with blank right half-tape,
    uniformly in the untouched left stack. -/
theorem a0_one_to_czero4 (left : List Bool) :
    runSafe 4 (z 0 left false [true]) =
      some (z 2 (ones 4 ++ left) false []) := by rfl

/-- Exact all-parameter first harmless C/0 gate in every positive-u,
    zero-right-budget Junc: at instruction start 2v+10 the source
    state is C/0 with the entire right half-tape blank, and every
    earlier instruction has avoided state C on current zero. -/
theorem junc_positive_w0_first_czero (u v : Nat) :
    runSafe (2*v+10) (junc (u+1) v 0) =
      some (z 2 (ones (2*v+9) ++ (pairs01 u ++ ones 5)) false []) := by
  have hprep : runSafe 4 (junc (u+1) v 0) =
      some (z 0 (true :: true :: true :: (pairs01 u ++ ones 5)) false
        (true :: pairs01 (v+1))) := by
    have hp : pairs01 v ++ ones 0 ++ [false,true] = pairs01 (v+1) := by
      simpa [ones] using (pairs01_succ_append v)
    have hpre0 : runSafe 4 (junc (u+1) v 0) =
      some (z 0 (true :: true :: true :: (pairs01 u ++ ones 5)) false
        (true :: (pairs01 v ++ ones 0 ++ [false,true]))) := by rfl
    rw [hp] at hpre0
    exact hpre0
  have hshift := a01_tail_shift_safe v
    (true :: true :: true :: (pairs01 u ++ ones 5))
  have htail := a0_one_to_czero4
    (ones (2*(v+1)) ++ (true :: true :: true :: (pairs01 u ++ ones 5)))
  rw [show 2*v+10=4+(2*(v+1)+4) by omega,runSafe_add,hprep]
  simp only [Option.bind_some]
  rw [runSafe_add,hshift]
  simp only [Option.bind_some]
  rw [htail]
  have hones : ones 4 ++
      (ones (2*(v+1)) ++ (true :: true :: true :: (pairs01 u ++ ones 5))) =
      ones (2*v+9) ++ (pairs01 u ++ ones 5) := by
    rw [ones_three_left]
    have hsum : ones 4 ++ (true :: ones (2*(v+1)+2)) =
        ones (2*v+9) := by
      calc
        ones 4 ++ (true :: ones (2*(v+1)+2)) =
          ones 4 ++ ones (1+(2*(v+1)+2)) := by
            have hh : true :: ones (2*(v+1)+2) =
                ones (1+(2*(v+1)+2)) := by
              simpa [ones] using (ones_add 1 (2*(v+1)+2)).symm
            exact congrArg (fun ys : List Bool => ones 4 ++ ys) hh
        _ = ones (4+(1+(2*(v+1)+2))) := by
          exact (ones_add 4 (1+(2*(v+1)+2))).symm
        _ = ones (2*v+9) := by congr 1 <;> omega
    calc
      ones 4 ++ (true :: (ones (2*(v+1)+2) ++ (pairs01 u ++ ones 5))) =
          (ones 4 ++ (true :: ones (2*(v+1)+2))) ++ (pairs01 u ++ ones 5) := by
            simp [List.append_assoc]
      _ = ones (2*v+9) ++ (pairs01 u ++ ones 5) := by rw [hsum]
  rw [hones]

/-- Every original-zipper prefix strictly before the zero-budget first
    C/0 gate is defined and has not yet visited the C/0 gateway. -/
theorem junc_positive_w0_no_earlier_czero (u v t : Nat)
    (ht : t < 2*v+10) :
    ∃ p, run t (junc (u+1) v 0) = some p ∧
      (p.state == 2 && !p.current) = false := by
  exact runSafe_no_czero_prefix (2*v+10) t
    (junc (u+1) v 0)
    (z 2 (ones (2*v+9) ++ (pairs01 u ++ ones 5)) false [])
    (junc_positive_w0_first_czero u v) ht

#print axioms junc_positive_w0_first_czero
#print axioms junc_positive_w0_no_earlier_czero

end BB429PositiveZeroGate
