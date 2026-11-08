import W4CZeroCount
import BB429JuncHeadExcursion
import Lean.Elab.Tactic.Omega

set_option maxRecDepth 8192
set_option maxHeartbeats 30000000

namespace BB429W4CZeroOrdinary

open BB429OddExcursion BB429SourceE1Return
open BB429FinishScanEDelta BB429JuncHeadExcursion
open BB429W4CZeroSafe BB429W4CZeroCount

private theorem ones_add' (m n : Nat) :
    ones (m+n) = ones m ++ ones n := by simp [ones]

private theorem pairs01_rightstep (n : Nat) :
    pairs01 (n+1) = pairs01 n ++ [false,true] := by
  induction n with
  | zero => rfl
  | succ n ih =>
      change false::true::pairs01 (n+1) =
        (false::true::pairs01 n) ++ [false,true]
      rw [ih]
      rfl

/-- A two-step rightward A/0,B/1 pair cannot scan C/0. -/
theorem shift_A01_pair_safe (left suffix : List Bool) :
    runSafe 2 (z 0 left false (true::true::suffix)) =
      some (z 0 (true::true::left) true suffix) := by rfl

/-- The complete parameter-uniform rightward A/01 sweep is C/0-free. -/
theorem shift_A01_safe (v : Nat) (left suffix : List Bool) :
    runSafe (2*(v+1))
      (z 0 left false (true :: (pairs01 v ++ (true :: suffix)))) =
      some (z 0 (ones (2*(v+1)) ++ left) true suffix) := by
  induction v generalizing left suffix with
  | zero => simpa [pairs01,ones] using shift_A01_pair_safe left suffix
  | succ v ih =>
      have hpair : runSafe 2
        (z 0 left false (true :: (pairs01 (v+1) ++ (true :: suffix)))) =
        some (z 0 (true::true::left) false
          (true :: (pairs01 v ++ (true :: suffix)))) := by rfl
      rw [show 2*(v+2)=2+2*(v+1) by omega,runSafe_add,hpair]
      simp only [Option.bind_some]
      rw [ih (true::true::left) suffix]
      have hleft : ones (2*(v+1)) ++ (true::true::left) =
          ones (2*(v+2)) ++ left := by
        calc
          ones (2*(v+1)) ++ (true::true::left) =
            (ones (2*(v+1)) ++ [true,true]) ++ left := by simp [List.append_assoc]
          _ = ones (2*(v+2)) ++ left := by
            change (ones (2*(v+1)) ++ ones 2) ++ left = _
            rw [← ones_add']
            rw [show 2*(v+1)+2=2*(v+2) by omega]
      rw [hleft]
      rw [show 2+2*(v+1)=2*(v+2) by omega]

/-- Four-instruction preparation at the positive-left Junc boundary. -/
theorem juncPos_prep4_safe (u v w : Nat) :
    runSafe 4 (junc (u+1) v w) =
      some (z 0 (true :: true :: true :: (pairs01 u ++ ones 5)) false
        (true :: (pairs01 v ++ ones w ++ [false,true]))) := by rfl

/-- No C/0 visit occurs in the positive-left Junc's rightward prefix. -/
theorem juncPos_to_midA_safe (u v w : Nat) (hw : 1 ≤ w) :
    runSafe (2*v+6) (junc (u+1) v w) =
      some (midApos u v w) := by
  have hones : ones w = true :: ones (w-1) := by
    cases w with
    | zero => omega
    | succ w => rfl
  rw [show 2*v+6 = 4+2*(v+1) by omega,runSafe_add,juncPos_prep4_safe]
  simp only [Option.bind_some]
  have hshift : runSafe (2*(v+1))
      (z 0 (true :: true :: true :: (pairs01 u ++ ones 5)) false
        (true :: (pairs01 v ++ ones w ++ [false,true]))) =
      some (z 0 (ones (2*(v+1)) ++ true :: true :: true ::
        (pairs01 u ++ ones 5)) true (ones (w-1) ++ [false,true])) := by
    simpa [hones,List.append_assoc,List.cons_append] using
      (shift_A01_safe v (true :: true :: true :: (pairs01 u ++ ones 5))
        (ones (w-1) ++ [false,true]))
  rw [hshift]
  simp only [midApos,Option.some.injEq]
  rw [ones_three_left (2*(v+1)) (pairs01 u ++ ones 5)]
  rw [show 2*(v+1)+2=2*(v+2) by omega]
  simp [List.append_assoc]

/-- Two-step leftward A/1,F/1 sweep pair never scans C/0. -/
theorem shift_A11_pair_safe (tail suffix : List Bool) :
    runSafe 2 (z 0 (true :: true :: true :: tail) true (true :: suffix)) =
      some (z 0 (true :: tail) true (true :: false :: true :: suffix)) := by rfl

/-- The entire leftward A/11 sweep contains no C/0 for arbitrary context. -/
theorem shift_A11_safe (p : Nat) (left suffix : List Bool) :
    runSafe (2*p)
      (z 0 (true :: (ones (2*p) ++ left)) true (true :: suffix)) =
      some (z 0 (true :: left) true (true :: (pairs01 p ++ suffix))) := by
  induction p generalizing left suffix with
  | zero => rfl
  | succ p ih =>
      have hrep : ones (2+2*p) = [true,true] ++ ones (2*p) := by
        calc
          ones (2+2*p) = ones (2*(p+1)) := by congr 1; omega
          _ = ones 2 ++ ones (2*p) := by
            rw [show 2*(p+1)=2+2*p by omega,ones_add' 2 (2*p)]
      have hfirst : runSafe 2
          (z 0 (true :: true :: true :: (ones (2*p) ++ left)) true
            (true :: suffix)) =
          some (z 0 (true :: (ones (2*p) ++ left)) true
            (true :: false :: true :: suffix)) := by
        exact shift_A11_pair_safe (ones (2*p) ++ left) suffix
      rw [show 2*(p+1)=2+2*p by omega,hrep]
      simp only [List.cons_append,List.nil_append]
      rw [runSafe_add,hfirst]
      simp only [Option.bind_some]
      rw [ih left (false :: true :: suffix)]
      have hright : pairs01 p ++ (false :: true :: suffix) =
          pairs01 (p+1) ++ suffix := by
        calc
          pairs01 p ++ (false :: true :: suffix) =
            pairs01 p ++ ([false,true] ++ suffix) := rfl
          _ = (pairs01 p ++ [false,true]) ++ suffix := by
            rw [← List.append_assoc]
          _ = pairs01 (p+1) ++ suffix := by
            exact congrArg (fun xs : List Bool => xs ++ suffix)
              (pairs01_rightstep p).symm
      rw [hright]

/-- An entire ordinary positive-left Junc macro never processes C/0. -/
theorem juncPos_next_safe (u v w : Nat) (hw : 2 ≤ w) :
    runSafe (4*v+10) (junc (u+1) v w) =
      some (junc u (v+2) (w-2)) := by
  have hmid := juncPos_to_midA_safe u v w (by omega)
  have hones : ones (w-1) = true :: ones (w-2) := by
    cases w with
    | zero => omega
    | succ w => cases w with
      | zero => omega
      | succ w => rfl
  rw [show 4*v+10 = (2*v+6)+2*(v+2) by omega,
    runSafe_add,hmid]
  simp only [Option.bind_some]
  have hinput : midApos u v w =
      z 0 (true :: (ones (2*(v+2)) ++ (pairs01 u ++ ones 5))) true
        (true :: (ones (w-2) ++ [false,true])) := by
    simp [midApos,hones,List.append_assoc,List.cons_append]
  rw [hinput]
  have hshift := shift_A11_safe (v+2) (pairs01 u ++ ones 5)
    (ones (w-2) ++ [false,true])
  rw [hshift]
  simp only [Option.some.injEq]
  simp [junc,pairs01,List.append_assoc,List.cons_append]

/-- The B/0,C/1 pair within the zero-left Junc sweep cannot process C/0. -/
theorem shift_B01_pair_safe (left suffix : List Bool) :
    runSafe 2 (z 1 left false (true::true::suffix)) =
      some (z 1 (false::true::left) true suffix) := by rfl

theorem shift_B01_safe (v : Nat) (left suffix : List Bool) :
    runSafe (2*(v+1))
      (z 1 left false (true :: (pairs01 v ++ (true :: suffix)))) =
      some (z 1 (pairs01 (v+1) ++ left) true suffix) := by
  induction v generalizing left suffix with
  | zero => simpa [pairs01] using shift_B01_pair_safe left suffix
  | succ v ih =>
      have hpair : runSafe 2
        (z 1 left false (true :: (pairs01 (v+1) ++ (true :: suffix)))) =
        some (z 1 (false::true::left) false
          (true :: (pairs01 v ++ (true :: suffix)))) := by rfl
      rw [show 2*(v+2)=2+2*(v+1) by omega,runSafe_add,hpair]
      simp only [Option.bind_some]
      rw [ih (false::true::left) suffix]
      have hleft : pairs01 (v+1) ++ (false::true::left) =
          pairs01 (v+2) ++ left := by
        calc
          pairs01 (v+1) ++ (false::true::left) =
            pairs01 (v+1) ++ ([false,true] ++ left) := rfl
          _ = (pairs01 (v+1) ++ [false,true]) ++ left := by
            rw [← List.append_assoc]
          _ = pairs01 (v+2) ++ left := by
            exact congrArg (fun xs : List Bool => xs ++ left)
              (pairs01_rightstep (v+1)).symm
      rw [hleft]

/-- The fixed preparation and unbounded rightward B/01 sweep, guarded
    against C/0, terminate at the B/1 gate for any positive w. -/
theorem junc0_prep20_safe (v w : Nat) :
    runSafe 20 (junc 0 v w) =
      some (z 1 (ones 5) false
        (true :: (pairs01 (v+2) ++ ones w ++ [false,true]))) := by rfl

theorem junc0_to_B_safe (v w : Nat) (hw : 1 ≤ w) :
    runSafe (2*v+26) (junc 0 v w) =
      some (z 1 (pairs01 (v+3) ++ ones 5) true
        (ones (w-1) ++ [false,true])) := by
  have hones : ones w = true :: ones (w-1) := by
    cases w with
    | zero => omega
    | succ w => rfl
  rw [show 2*v+26=20+2*(v+3) by omega,
    runSafe_add,junc0_prep20_safe]
  simp only [Option.bind_some]
  have hshift := shift_B01_safe (v+2) (ones 5)
    (ones (w-1) ++ [false,true])
  have hinput : z 1 (ones 5) false
      (true :: (pairs01 (v+2) ++ ones w ++ [false,true])) =
    z 1 (ones 5) false
      (true :: (pairs01 (v+2) ++ (true :: (ones (w-1) ++ [false,true])))) := by
    rw [hones]
    simp [List.append_assoc,List.cons_append]
  rw [hinput,hshift]

/-- For every v and w>=3, the complete ordinary zero-left Junc macro
    visits no C/0 configuration at any primitive step, including endpoint. -/
theorem junc0_next_safe (v w : Nat) (hw : 3 ≤ w) :
    runSafe (2*v+27) (junc 0 v w) =
      some (junc (v+3) 0 (w-3)) := by
  have hB := junc0_to_B_safe v w (by omega)
  rw [show 2*v+27=(2*v+26)+1 by omega,runSafe_add,hB]
  simp only [Option.bind_some]
  have hlast : runSafe 1
      (z 1 (pairs01 (v+3) ++ ones 5) true
        (ones (w-1) ++ [false,true])) =
    some (z 0 (true::(pairs01 (v+3) ++ ones 5)) true
      (ones (w-2) ++ [false,true])) := by
    cases w with
    | zero => omega
    | succ w => cases w with
      | zero => omega
      | succ w => rfl
  rw [hlast]
  simp only [Option.some.injEq]
  have honesTail : ones (w-2) = true :: ones (w-3) := by
    cases w with
    | zero => omega
    | succ w => cases w with
      | zero => omega
      | succ w => cases w with
        | zero => omega
        | succ w => rfl
  simp [junc,pairs01,honesTail,List.append_assoc,List.cons_append]

/-- Arbitrarily many successive positive-left Junc macros remain C/0-free. -/
theorem juncPos_iter_safe (N U v w : Nat) (hU : N ≤ U)
    (hw : 2*N ≤ w) :
    runSafe (juncPosFullTime N v) (junc U v w) =
      some (junc (U-N) (v+2*N) (w-2*N)) := by
  induction N generalizing U v w with
  | zero => rfl
  | succ N ih =>
      have hstep0 := juncPos_next_safe (U-1) v w (by omega)
      have hstep : runSafe (4*v+10) (junc U v w) =
          some (junc (U-1) (v+2) (w-2)) := by
        simpa [Nat.sub_add_cancel (by omega : 1 ≤ U)] using hstep0
      rw [show juncPosFullTime (N+1) v =
        (4*v+10) + juncPosFullTime N (v+2) by rfl,
        runSafe_add,hstep]
      simp only [Option.bind_some]
      have htail := ih (U-1) (v+2) (w-2) (by omega) (by omega)
      rw [htail]
      have hUsub : U-1-N=U-(N+1) := by omega
      have hv : v+2+2*N=v+2*(N+1) := by omega
      have hwsub : w-2-2*N=w-2*(N+1) := by omega
      rw [hUsub,hv,hwsub]

/-- Original-source exact event count for the ordinary Junc transitions. -/
theorem juncPos_next_zero_czero_count (u v w : Nat) (hw : 2 ≤ w) :
    runCount (4*v+10) (junc (u+1) v w) =
      some (junc u (v+2) (w-2),0) :=
  runSafe_to_count_zero _ _ _ (juncPos_next_safe u v w hw)

theorem junc0_next_zero_czero_count (v w : Nat) (hw : 3 ≤ w) :
    runCount (2*v+27) (junc 0 v w) =
      some (junc (v+3) 0 (w-3),0) :=
  runSafe_to_count_zero _ _ _ (junc0_next_safe v w hw)

theorem juncPos_iter_zero_czero_count (N U v w : Nat)
    (hU : N ≤ U) (hw : 2*N ≤ w) :
    runCount (juncPosFullTime N v) (junc U v w) =
      some (junc (U-N) (v+2*N) (w-2*N),0) :=
  runSafe_to_count_zero _ _ _ (juncPos_iter_safe N U v w hU hw)

#print axioms juncPos_next_safe
#print axioms junc0_next_safe
#print axioms juncPos_iter_safe
#print axioms juncPos_next_zero_czero_count
#print axioms junc0_next_zero_czero_count
#print axioms juncPos_iter_zero_czero_count

end BB429W4CZeroOrdinary
