import W4JuncOne
import Lean.Elab.Tactic.Omega

namespace BB429W4JuncGeneral

open BB429OddExcursion BB429SourceE1Return BB429SourceE1Delta
open BB429FinishScanEDelta BB429JuncHeadExcursion
open BB429W4JuncOne

/-- Fixed twenty-step C/1-to-E/1 preparation, retaining the untouched
    two alternating pairs and five-one left tail. -/
theorem c1_even_to_e1_20_general (k : Nat) :
  runWithDelta 20
    (z 2 (ones (4*k+5) ++ pairs01 2 ++ ones 5) true sigma) =
    some (z 4 (ones (4*k+13) ++ pairs01 2 ++ ones 5) true [true,false,true], 8) := by
  rfl

/-- Exactly 72 original machine moves close the fixed E/1 partial sweep
    with an arbitrary remaining right-one block. -/
theorem even_e1_tail72 (k : Nat) :
  runWithDelta 72
    (z 4 (pairs01 2 ++ ones 5) true (ones (4*k+13) ++ [true,false,true])) =
    some (junc 2 4 (4*k+9), -4) := by
  have hr :
      ones (4*k+13) ++ [true,false,true] =
      ones (4*k+14) ++ [false,true] := by
    calc
      ones (4*k+13) ++ [true,false,true] =
          (ones (4*k+13) ++ [true]) ++ [false,true] := by
            simp [List.append_assoc]
      _ = ones (4*k+14) ++ [false,true] := by
        have hone : ones (4*k+13) ++ [true] = ones (4*k+14) := by
          change List.replicate (4*k+13) true ++ [true] =
            List.replicate (4*k+14) true
          rw [show 4*k+14 = (4*k+13)+1 by omega]
          exact List.replicate_succ'.symm
        rw [hone]
  rw [hr]
  rfl

/-- Generic all-left-prefix E/1 sweep, retaining an arbitrary untouched
    left tail. -/
theorem E1_sweep_prefix_delta (n : Nat) (left suffix : List Bool) :
    runWithDelta n (z 4 (ones n ++ left) true suffix) =
      some (z 4 left true (ones n ++ suffix), -((n : Nat) : Int)) := by
  induction n generalizing left suffix with
  | zero =>
      rfl
  | succ n ih =>
      rw [show n+1 = 1+n by omega, runWithDelta_add]
      have hleft : ones (1+n) ++ left = true :: (ones n ++ left) := by
        rw [BB429SourceE1Return.ones_add 1 n]
        simp [ones]
      have hstep :
          runWithDelta 1 (z 4 (ones (1+n) ++ left) true suffix) =
            some (z 4 (ones n ++ left) true (true :: suffix), -1) := by
        rw [hleft]
        rfl
      rw [hstep]
      simp only [Option.bind_some]
      rw [ih]
      simp only [Option.map_some]
      have hones : ones n ++ [true] = ones (n+1) := by
        simpa [ones] using (BB429SourceE1Return.ones_add n 1).symm
      have hright : ones n ++ (true :: suffix) = ones (n+1) ++ suffix := by
        calc
          ones n ++ (true :: suffix) = ones n ++ ([true] ++ suffix) := rfl
          _ = (ones n ++ [true]) ++ suffix := by rw [← List.append_assoc]
          _ = ones (n+1) ++ suffix := by rw [hones]
      rw [hright, show n+1 = 1+n by omega]
      simp only [Option.some.injEq, Prod.mk.injEq]
      constructor
      · trivial
      · omega

/-- The full even-index S_E sigma return retains a short nonzero-left
    Junc parameter and produces a right-one block of unbounded length. -/
theorem scanE_even_sigma_to_junc2 (k : Nat) :
  runWithDelta (18*k+161) (sourceScanE (2*k+2) sigma) =
    some (junc 2 4 (4*k+9), -((4*k+9 : Nat) : Int)) := by
  have hret := sourceScanE_e1_revisit_delta (2*(k+1)) sigma
  rw [crossTime_even, finalLeft_even] at hret
  have hprep := c1_even_to_e1_20_general k
  have hsweep := E1_sweep_prefix_delta (4*k+13) (pairs01 2 ++ ones 5)
    [true,false,true]
  have htail := even_e1_tail72 k
  have hrewrite : 2*(k+1) = 2*k+2 := by omega
  rw [hrewrite] at hret
  have htime :
      18*k+161 = ((14*(k+1)+41)+1) + (20 + ((4*k+13)+72)) := by omega
  rw [htime, runWithDelta_add, hret]
  simp only [Option.bind_some]
  rw [runWithDelta_add]
  have hleft :
      ones (4*(k+1)+1) ++ [false,true,false,true] ++ ones 5 =
      ones (4*k+5) ++ pairs01 2 ++ ones 5 := by
    rw [show 4*(k+1)+1 = 4*k+5 by omega]
    rfl
  rw [hleft, hprep]
  simp only [Option.bind_some]
  have hsweep' :
      runWithDelta (4*k+13)
        (z 4 (ones (4*k+13) ++ pairs01 2 ++ ones 5) true [true,false,true]) =
      some (z 4 (pairs01 2 ++ ones 5) true
        (ones (4*k+13) ++ [true,false,true]), -((4*k+13 : Nat) : Int)) := by
    simpa only [List.append_assoc] using hsweep
  rw [runWithDelta_add, hsweep']
  simp only [Option.bind_some]
  rw [htail]
  simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq]
  constructor
  · trivial
  · omega

/-- For every even v, the canonical u=0 Junc with one right budget
    reaches a uniform u=2 Junc family; no restriction on k is needed. -/
theorem junc0_all_even_w1 (k : Nat) :
  runWithDelta (22*k+203) (junc 0 (2*k) 1) =
    some (junc 2 4 (4*k+9), -9) := by
  have hfirst := junc0_w1_to_scanE (2*k)
  have htail := scanE_even_sigma_to_junc2 k
  have htime : 22*k+203 = (2*(2*k)+42) + (18*k+161) := by omega
  rw [htime, runWithDelta_add, hfirst]
  simp only [Option.bind_some]
  rw [htail]
  simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq]
  constructor
  · trivial
  · omega

/-- Two source-verified positive-u steps and one zero-u step reach a
    normalized Junc with zero middle parameter for all even v. -/
theorem junc0_even_w1_to_positive (k : Nat) :
  runWithDelta (22*k+306) (junc 0 (2*k) 1) =
    some (junc 11 0 (4*k+2), 6) := by
  have hfirst := junc0_all_even_w1 k
  have hmid := juncPos_iter_full_delta 2 2 4 (4*k+9) (by omega) (by omega)
  have hlast := junc0_next_delta 8 (4*k+5) (by omega)
  have hmTime : juncPosFullTime 2 4 = 60 := by rfl
  rw [hmTime] at hmid
  have hm : 4*k+9-2*2 = 4*k+5 := by omega
  rw [hm] at hmid
  have hl : 4*k+5-3 = 4*k+2 := by omega
  rw [hl] at hlast
  have htime : 22*k+306 = (22*k+203) + (60+43) := by omega
  rw [htime, runWithDelta_add, hfirst]
  simp only [Option.bind_some]
  rw [runWithDelta_add, hmid]
  simp only [Option.bind_some]
  rw [hlast]
  simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq]
  constructor
  · trivial
  · omega

#print axioms c1_even_to_e1_20_general
#print axioms even_e1_tail72
#print axioms E1_sweep_prefix_delta
#print axioms scanE_even_sigma_to_junc2
#print axioms junc0_all_even_w1
#print axioms junc0_even_w1_to_positive

end BB429W4JuncGeneral
