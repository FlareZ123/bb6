import MidAposBoundary
import Lean.Elab.Tactic.Omega
namespace BB429High0Source
open BB429OddExcursion BB429SourceE1Return BB429SourceE1Delta
open BB429High2Prefix BB429FinishScanEDelta BB429High2TailBase
open BB429MidAposBoundary

/-- The high-zero C/B sweep has the same processed left stack as high-two,
    with unprocessed right suffix 01. -/
def high0SweepStart (u : Nat) : Zipper :=
  z 2 (tens (2*u+2) ++ ones 6) true [false,true]

theorem high0_enter_e (u : Nat) :
  runWithDelta 11 (high0SweepStart u) =
    some (sourceScanE (2*u+3) rightBlock, 1) := by
  unfold high0SweepStart
  rw [tens_append_ones6]
  rfl

theorem e_drop_two (b : Nat) (suffix : List Bool) :
  runWithDelta 6 (sourceScanE (b+2) suffix) =
    some (sourceScanE b (rightBlock ++ suffix), -4) := by
  rfl

def blocks : Nat → List Bool
 | 0 => []
 | n+1 => rightBlock ++ blocks n

theorem e_drop_all (j k : Nat) :
  runWithDelta (6*j) (sourceScanE (2*j+1) (blocks k)) =
    some (sourceScanE 1 (blocks (j+k)), -((4*j : Nat) : Int)) := by
  induction j generalizing k with
  | zero => simp [runWithDelta]
  | succ j ih =>
    have hf : 2*(j+1)+1 = (2*j+1)+2 := by omega
    have ht : 6*(j+1) = 6+6*j := by omega
    rw [ht, hf, runWithDelta_add, e_drop_two]
    simp only [Option.bind_some]
    have hb : rightBlock ++ blocks k = blocks (k+1) := by rfl
    rw [hb, ih (k+1)]
    simp only [Option.map_some]
    have heq : j+(k+1)=(j+1)+k := by omega
    rw [heq]
    simp only [Option.some.injEq, Prod.mk.injEq]
    constructor
    · trivial
    · omega

theorem c_eight_blocks (k m : Nat) :
  runWithDelta (8*k) (z 2 (ones m) true (blocks k)) =
    some (z 2 (ones (4*k+m)) true [], ((4*k : Nat) : Int)) := by
  induction k generalizing m with
  | zero => simp [runWithDelta,blocks]
  | succ k ih =>
    have ht : 8*(k+1) = 8+8*k := by omega
    rw [ht, runWithDelta_add]
    change (runWithDelta 8 (z 2 (ones m) true (rightBlock ++ blocks k))).bind _ = _
    rw [eight_step_macro_delta]
    simp only [Option.bind_some]
    have hones : ones 4 ++ ones m = ones (m+4) := by
      rw [← BB429SourceE1Return.ones_add 4 m]
      rw [Nat.add_comm]
    rw [hones]
    rw [ih (m+4)]
    simp only [Option.map_some]
    have ha : 4*k+(m+4)=4*(k+1)+m := by omega
    rw [ha]
    simp only [Option.some.injEq, Prod.mk.injEq]
    constructor
    · trivial
    · omega

theorem c_solid_to_e (u : Nat) :
  runWithDelta (4*u+19) (z 2 (ones (4*u+16)) true []) =
    some (sourceScanE 0 (ones (4*u+12) ++ [false,true]),
      -((4*u+11 : Nat) : Int)) := by
  have ht : 4*u+19 = 8+(4*u+11) := by omega
  rw [ht, runWithDelta_add, midAaux_C1_to_E1_delta]
  simp only [Option.bind_some]
  have hleft : ones (4*u+16)=ones (4*u+11)++ones 5 := by
    rw [← BB429SourceE1Return.ones_add]
  rw [hleft, E1_sweep_prefix_delta]
  simp only [Option.map_some]
  have hright : ones (4*u+11) ++ [true,false,true] =
      ones (4*u+12) ++ [false,true] := by
    rw [show 4*u+12 = (4*u+11)+1 by omega]
    rw [BB429SourceE1Return.ones_add (4*u+11) 1]
    simp [ones, List.append_assoc]
  rw [hright]
  rfl

theorem e_zero_to_junc (u : Nat) :
  runWithDelta 17 (sourceScanE 0 (ones (4*u+12) ++ [false,true])) =
    some (junc 0 0 (4*u+12), -1) := by
  rfl

/-- Exact high-zero C/B sweep-to-Junc transition for every natural u. -/
theorem high0_to_junc (u : Nat) :
  runWithDelta (18*u+85) (high0SweepStart u) =
    some (junc 0 0 (4*u+12), -((4*u+7 : Nat) : Int)) := by
  have a := high0_enter_e u
  have b := e_drop_all (u+1) 1
  have c := sourceScanE_e1_revisit_delta 1 (blocks (u+2))
  have d := c_eight_blocks (u+2) 8
  have e := c_solid_to_e u
  have f := e_zero_to_junc u
  have hlen : 18*u+85 =
      11 + 6*(u+1) + (crossTime 1+1) + 8*(u+2) + (4*u+19) + 17 := by
    simp [crossTime]; omega
  rw [hlen, show 11 + 6*(u+1) + (crossTime 1+1) + 8*(u+2) + (4*u+19) + 17 =
        11 + (6*(u+1) + ((crossTime 1+1) + (8*(u+2) + ((4*u+19)+17)))) by omega]
  rw [runWithDelta_add, a]
  simp only [Option.bind_some]
  have h2u : 2*(u+1)+1 = 2*u+3 := by omega
  have hbl : blocks 1 = rightBlock := rfl
  rw [runWithDelta_add, ←h2u, ←hbl, b]
  simp only [Option.bind_some]
  rw [runWithDelta_add, c]
  simp only [Option.bind_some]
  simp only [finalLeft]
  rw [runWithDelta_add, d]
  simp only [Option.bind_some]
  have hnorm : 4*(u+2)+8=4*u+16 := by omega
  rw [hnorm]
  rw [runWithDelta_add, e]
  simp only [Option.bind_some]
  rw [f]
  simp only [Option.map_some]
  simp only [Option.some.injEq, Prod.mk.injEq, true_and]
  simp only [Int.natCast_add, Int.natCast_mul]
  omega

#print axioms high0_to_junc
end BB429High0Source
