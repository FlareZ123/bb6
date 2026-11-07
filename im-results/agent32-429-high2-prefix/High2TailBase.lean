import High2Tail
import Lean.Elab.Tactic.Omega

namespace BB429High2TailBase

open BB429High2Tail
open BB429OddExcursion BB429SourceE1Return BB429SourceE1Delta
open BB429JuncHeadExcursion BB429FinishScanEDelta

/-- The first four source steps normalize the A/F fringe and restore the
    original right suffix. -/
theorem midAaux_prefix4_delta (k : Nat) :
    runWithDelta 4 (midAaux 0 k) =
      some (z 0 (ones 8) false (tens k ++ [false,true]), 0) := by
  rfl

/-- One A/01 pair transfers two ones to the left and advances by two cells. -/
theorem a_right_two_delta (left suffix : List Bool) :
    runWithDelta 2 (z 0 left false (true::false::suffix)) =
      some (z 0 (true::true::left) false suffix, 2) := by
  rfl

/-- Repeated A/01 pairs consume an alternating right block exactly. -/
theorem a_right_pairs_delta (j : Nat) (left suffix : List Bool) :
    runWithDelta (2*j) (z 0 left false (tens j ++ suffix)) =
      some (z 0 (ones (2*j) ++ left) false suffix, ((2*j : Nat) : Int)) := by
  induction j generalizing left suffix with
  | zero => rfl
  | succ j ih =>
      have hfirst :
          runWithDelta 2 (z 0 left false (tens (j+1) ++ suffix)) =
            some (z 0 (true::true::left) false (tens j ++ suffix), 2) := by
        rfl
      rw [show 2*(j+1) = 2 + 2*j by omega, runWithDelta_add, hfirst]
      simp only [Option.bind_some]
      rw [ih (true::true::left) suffix]
      simp only [Option.map_some]
      have hleft : ones (2*j) ++ (true::true::left) =
          ones (2*(j+1)) ++ left := by
        rw [show 2*(j+1) = 2*j+2 by omega, BB429FinishScanEDelta.ones_add]
        simp [ones, List.append_assoc]
      rw [hleft]
      simp [show 2*(j+1) = 2+2*j by omega]

/-- The A/F prefix followed by all alternating pairs reaches A/0 with
    a solid one block on the left. -/
theorem midAaux_to_A0_delta (k : Nat) :
    runWithDelta (2*k+4) (midAaux 0 k) =
      some (z 0 (ones (2*k+8)) false [false,true], ((2*k : Nat) : Int)) := by
  rw [show 2*k+4 = 4 + 2*k by omega, runWithDelta_add,
    midAaux_prefix4_delta]
  simp only [Option.bind_some]
  have hpairs := a_right_pairs_delta k (ones 8) [false,true]
  have hleft : ones (2*k) ++ ones 8 = ones (2*k+8) := by
    symm
    rw [BB429FinishScanEDelta.ones_add]
  rw [hpairs]
  simp only [Option.map_some]
  rw [hleft]
  simp

/-- The terminal A/0 pair enters C/1 and adds two left ones. -/
theorem midAaux_A0_to_C1_delta (left : List Bool) :
    runWithDelta 2 (z 0 left false [false,true]) =
      some (z 2 (true::true::left) true [], 2) := by
  rfl

/-- The fixed C/1 segment reaches E/1 with a three-cell right suffix. -/
theorem midAaux_C1_to_E1_delta (left : List Bool) :
    runWithDelta 8 (z 2 left true []) =
      some (z 4 left true [true,false,true], 0) := by
  rfl

/-- E/1 moves left across an arbitrary all-one block, preserving its length
    as a right-side block and recording the exact displacement. -/
theorem E1_sweep_delta (n : Nat) (suffix : List Bool) :
    runWithDelta n (z 4 (ones n) true suffix) =
      some (z 4 [] true (ones n ++ suffix), -((n : Nat) : Int)) := by
  induction n generalizing suffix with
  | zero => rfl
  | succ n ih =>
      have hfirst :
          runWithDelta 1 (z 4 (ones (1+n)) true suffix) =
            some (z 4 (ones n) true (true::suffix), -1) := by
        have hrep : ones (1+n) = true :: ones n := by
          rw [show 1+n = n+1 by omega]
          change List.replicate (n+1) true = true :: List.replicate n true
          exact List.replicate_succ
        rw [hrep]
        rfl
      rw [show n+1 = 1+n by omega, runWithDelta_add, hfirst]
      simp only [Option.bind_some]
      rw [ih (true::suffix)]
      simp only [Option.map_some]
      have hone1 : ones n ++ [true] = ones (n+1) := by
        symm
        change List.replicate (n+1) true = List.replicate n true ++ [true]
        exact List.replicate_succ'
      have hones : ones n ++ (true::suffix) = ones (1+n) ++ suffix := by
        change ones n ++ ([true] ++ suffix) = ones (1+n) ++ suffix
        rw [show 1+n = n+1 by omega, ← List.append_assoc, hone1]
      rw [hones]
      have hdelta : (-1 : Int) + -(n : Int) = -((1+n : Nat) : Int) := by
        rw [show 1+n = n+1 by omega]
        simp only [Int.natCast_add]
        omega
      apply congrArg some
      apply congrArg (fun d : Int => (z 4 [] true (ones (1+n) ++ suffix), d))
      exact hdelta

/-- The final twelve source steps consume four right-side ones and create
    the six-one Junc left fringe. -/
theorem E1_tail12_delta (suffix : List Bool) :
    runWithDelta 12 (z 4 [] true (ones 4 ++ suffix)) =
      some (z 0 (ones 6) true suffix, 4) := by
  rfl

/-- Exact v=0 boundary family for the high-2 suffix, with its full
    primitive-step cost and signed head displacement. -/
theorem midAaux_zero_base (k : Nat) :
    runWithDelta (4*k+36) (midAaux 0 k) =
      some (junc 0 0 (2*k+6), -4) := by
  have hprefix := midAaux_to_A0_delta k
  have hA : runWithDelta 2 (z 0 (ones (2*k+8)) false [false,true]) =
      some (z 2 (ones (2*k+10)) true [], 2) := by
    have hones : ones (2*k+10) = true :: true :: ones (2*k+8) := by
      calc
        ones (2*k+10) = ones (2 + (2*k+8)) := by congr 1; omega
        _ = ones 2 ++ ones (2*k+8) :=
          BB429FinishScanEDelta.ones_add 2 _
        _ = true :: true :: ones (2*k+8) := rfl
    have hA0 := midAaux_A0_to_C1_delta (ones (2*k+8))
    rw [← hones] at hA0
    exact hA0
  have hC := midAaux_C1_to_E1_delta (ones (2*k+10))
  have hE := E1_sweep_delta (2*k+10) [true,false,true]
  have htail := E1_tail12_delta (ones (2*k+7) ++ [false,true])
  have htime : 4*k+36 =
      (2*k+4) + (2 + (8 + ((2*k+10) + 12))) := by omega
  have hright : ones (2*k+10) ++ [true,false,true] =
      ones (2*k+11) ++ [false,true] := by
    rw [BB429FinishScanEDelta.ones_add (2*k+10) 1]
    simp [ones]
  have htailInput : ones (2*k+11) ++ [false,true] =
      ones 4 ++ (ones (2*k+7) ++ [false,true]) := by
    have hn : 2*k+11 = 4 + (2*k+7) := by omega
    rw [hn, BB429FinishScanEDelta.ones_add]
    simp [List.append_assoc]
  rw [htime, runWithDelta_add, hprefix]
  simp only [Option.bind_some]
  rw [runWithDelta_add, hA]
  simp only [Option.bind_some]
  rw [runWithDelta_add, hC]
  simp only [Option.bind_some]
  rw [runWithDelta_add, hE]
  simp only [Option.bind_some]
  rw [hright, htailInput, htail]
  simp only [Option.map_some]
  have hfinalRight : ones (2*k+7) = true :: ones (2*k+6) := by
    rw [show 2*k+7 = (2*k+6)+1 by omega]
    change List.replicate ((2*k+6)+1) true =
      true :: List.replicate (2*k+6) true
    exact List.replicate_succ
  rw [hfinalRight]
  simp [junc, ones, pairs01] <;> omega

/-- The auxiliary v-reduction followed by the zero-base theorem closes
    every member of the two-parameter midAaux family. -/
theorem midAaux_to_junc0_of_base (v k : Nat)
    (hbase : ∀ j : Nat,
      runWithDelta (4*j+36) (midAaux 0 j) =
        some (junc 0 0 (2*j+6), -4)) :
    runWithDelta (6*v+4*k+36) (midAaux v k) =
      some (junc 0 0 (2*(v+k)+6), -((2*v+4 : Nat) : Int)) := by
  have hreduce := midAaux_reduce_v v k
  have hlast := hbase (k+v)
  have htime : 6*v+4*k+36 = 2*v + (4*(k+v)+36) := by omega
  have hparam : 2*(k+v)+6 = 2*(v+k)+6 := by omega
  have hdisp : -((2*v : Nat) : Int) + (-4) =
      -((2*v+4 : Nat) : Int) := by omega
  rw [htime, runWithDelta_add, hreduce]
  simp only [Option.bind_some]
  rw [hlast]
  simp only [Option.map_some]
  rw [hparam, hdisp]

#print axioms midAaux_zero_base
#print axioms midAaux_to_junc0_of_base

end BB429High2TailBase
