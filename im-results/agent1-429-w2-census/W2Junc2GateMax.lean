import W2CZeroTailMax
import PositiveRegularHeadMax
import High2Tail
import Lean.Elab.Tactic.Omega

set_option maxHeartbeats 30000000
set_option maxRecDepth 8192

namespace BB429W2Junc2GateMax

open BB429OddExcursion BB429SourceE1Return BB429SourceE1Delta
open BB429FinishScanEDelta BB429JuncHeadExcursion BB429High2Tail
open BB429W4HeadMax BB429W2CZeroTailMax BB429PositiveRegularHeadMax

/-- An A/0,B/1 rightward pair attains its final coordinate as its all-prefix
    head maximum. Arbitrary unvisited tape context is preserved. -/
theorem a_right_two_max (left suffix : List Bool) :
    runWithMax 2 (z 0 left false (true::false::suffix)) =
      some (z 0 (true::true::left) false suffix, 2, 2) := by rfl

/-- Every all-prefix head maximum over an arbitrary A/01 transfer equals
    the number of cells transferred. -/
theorem a_right_pairs_max (j : Nat) (left suffix : List Bool) :
    runWithMax (2*j) (z 0 left false (tens j ++ suffix)) =
      some (z 0 (ones (2*j) ++ left) false suffix,
        ((2*j : Nat) : Int), ((2*j : Nat) : Int)) := by
  induction j generalizing left with
  | zero => rfl
  | succ j ih =>
      have hfirst : runWithMax 2 (z 0 left false (tens (j+1) ++ suffix)) =
          some (z 0 (true::true::left) false (tens j ++ suffix),2,2) := by rfl
      rw [show 2*(j+1)=2+2*j by omega,runWithMax_add,hfirst]
      simp only [Option.bind_some]
      rw [ih (true::true::left)]
      simp only [Option.map_some]
      have hwords : ones (2*j) ++ (true::true::left) =
          ones (2*(j+1)) ++ left := by
        change (List.replicate (2*j) true) ++ (true::true::left) = _
        rw [show 2*(j+1) = (2*j)+2 by omega]
        change List.replicate (2*j) true ++ (true::true::left) =
          List.replicate (2*j+2) true ++ left
        rw [show 2*j+2=(2*j)+2 by omega,← List.replicate_append_replicate]
        simp [List.append_assoc]
      rw [hwords, show 2+2*j = 2*(j+1) by omega]
      simp only [Option.some.injEq,Prod.mk.injEq]
      constructor
      · trivial
      · constructor <;> simp [Int.max_def] <;> omega

/-- The four-step A/F correction never advances to the right. -/
theorem midAaux_prefix4_max (k : Nat) :
    runWithMax 4 (midAaux 0 k) =
      some (z 0 (ones 8) false (tens k ++ [false,true]),0,0) := by rfl

theorem midAaux_A0_C1_max (n : Nat) :
    runWithMax 2 (z 0 (ones (2*n+8)) false [false,true]) =
      some (z 2 (ones (2*n+10)) true [],2,2) := by rfl

theorem midAaux_C1_C0_max (n : Nat) :
    runWithMax 2 (z 2 (ones (2*n+10)) true []) =
      some (z 2 (true::false::ones (2*n+10)) false [],2,2) := by rfl

/-- Exact full-prefix maximum up to the C/0 gate in a normalized A/F
    residual for every k, with a blank right half-tape at the gate. -/
theorem midAaux_zero_gate_max (k : Nat) :
    runWithMax (2*k+8) (midAaux 0 k) =
      some (z 2 (true::false::ones (2*k+10)) false [],
        ((2*k+4 : Nat) : Int), ((2*k+4 : Nat) : Int)) := by
  have h0 := midAaux_prefix4_max k
  have h1 := a_right_pairs_max k (ones 8) [false,true]
  have h2 := midAaux_A0_C1_max k
  have h3 := midAaux_C1_C0_max k
  have hsum : ones (2*k) ++ ones 8 = ones (2*k+8) := by
    simp [ones, ←List.replicate_append_replicate]
  rw [show 2*k+8=4+(2*k+(2+2)) by omega,runWithMax_add,h0]
  simp only [Option.bind_some]
  rw [runWithMax_add,h1]
  simp only [Option.bind_some]
  rw [hsum,runWithMax_add,h2]
  simp only [Option.bind_some]
  rw [h3]
  simp only [Option.map_some, Option.some.injEq,Prod.mk.injEq]
  constructor
  · trivial
  · constructor <;> simp [Int.max_def] <;> omega

theorem midAaux_step2_max (v k : Nat) :
    runWithMax 2 (midAaux (v+1) k) =
      some (midAaux v (k+1), -2, 0) := by rfl

/-- Reduction of an unbounded A/F left prefix makes no rightward excursion. -/
theorem midAaux_reduce_max (v k : Nat) :
    runWithMax (2*v) (midAaux v k) =
      some (midAaux 0 (k+v), -((2*v : Nat) : Int), 0) := by
  induction v generalizing k with
  | zero => rfl
  | succ v ih =>
      rw [show 2*(v+1) = 2+2*v by omega,runWithMax_add,
        midAaux_step2_max]
      simp only [Option.bind_some]
      rw [ih (k+1)]
      simp only [Option.map_some,Option.some.injEq,Prod.mk.injEq]
      constructor
      · congr 1
        omega
      · constructor <;> simp [Int.max_def] <;> omega

/-- Parameter-uniform C/0 record after the complete A/F fringe reduction. -/
theorem midAaux_all_gate_max (v k : Nat) :
    runWithMax (2*v + (2*(k+v)+8)) (midAaux v k) =
      some (z 2 (true::false::ones (2*(k+v)+10)) false [],
        ((2*k+4 : Nat) : Int), ((2*k+4 : Nat) : Int)) := by
  rw [runWithMax_add,midAaux_reduce_max]
  simp only [Option.bind_some]
  rw [midAaux_zero_gate_max]
  simp only [Option.map_some,Option.some.injEq,Prod.mk.injEq]
  constructor
  · trivial
  · constructor <;> simp [Int.max_def] <;> omega

/-- The fixed left-going six-step MidA fringe has maximum zero. -/
theorem midApos_to_midAaux_max (v : Nat) :
    runWithMax 6 (midApos 1 (v+1) 1) =
      some (midAaux v 3, -6, 0) := by
  have hones : ones (2*(v+3)) = ones 5 ++ ones (2*v+1) := by
    rw [show 2*(v+3) = 5+(2*v+1) by omega]
    simp [ones,← List.replicate_append_replicate]
  unfold midApos
  rw [show v+1+2 = v+3 by omega]
  rw [hones]
  simp [runWithMax, oneWithDelta, one, action, midAaux,
    pairs01,ones,tens,z,List.append_assoc]
  simp [Int.max_def]

/-- The C/0 gate lies exactly four cells to the right of the MidA entry,
    and no primitive-step prefix overshoots that coordinate. -/
theorem midApos_w1_gate_max (v : Nat) (hv : 1 ≤ v) :
    runWithMax (4*v+16) (midApos 1 v 1) =
      some (z 2 (true::false::ones (2*v+14)) false [],4,4) := by
  have h6 : runWithMax 6 (midApos 1 v 1) =
      some (midAaux (v-1) 3,-6,0) := by
    simpa [show v-1+1=v by omega] using midApos_to_midAaux_max (v-1)
  have hlast := midAaux_all_gate_max (v-1) 3
  have htime : 4*v+16 = 6 + (2*(v-1) + (2*(3+(v-1))+8)) := by omega
  rw [htime,runWithMax_add,h6]
  simp only [Option.bind_some]
  rw [hlast]
  have hparam : 2*(3+(v-1))+10=2*v+14 := by omega
  rw [hparam]
  simp only [Option.map_some,Option.some.injEq,Prod.mk.injEq]
  constructor
  · trivial
  · constructor <;> simp [Int.max_def] <;> omega

/-- The positive-left Junc(2,v,1) reaches its MidA boundary at its
    previous rightmost head record 2v+2. -/
theorem junc2_w1_to_midA_max (v : Nat) :
  runWithMax (2*v+6) (junc 2 v 1) =
    some (midApos 1 v 1, ((2*v+2 : Nat) : Int), ((2*v+2 : Nat) : Int)) := by
  have hprep := juncPos_prep4_max 1 v 1
  have hshift := shift_A01_max v
    (true::true::true::(pairs01 1 ++ ones 5)) [false,true]
  have hinput : z 0 (true::true::true::(pairs01 1 ++ ones 5)) false
      (true :: (pairs01 v ++ ones 1 ++ [false,true])) =
      z 0 (true::true::true::(pairs01 1 ++ ones 5)) false
      (true :: (pairs01 v ++ (true :: [false,true]))) := by
    simp [ones,List.append_assoc]
  have hcfg : z 0 (ones (2*(v+1)) ++
          (true::true::true::(pairs01 1 ++ ones 5))) true [false,true] =
        midApos 1 v 1 := by
    rw [ones_three_left]
    simp [midApos, ones, List.append_assoc,
      show 2*(v+1)+2=2*(v+2) by omega]
  rw [show 2*v+6 = 4+2*(v+1) by omega,runWithMax_add,hprep]
  simp only [Option.bind_some]
  rw [hinput,hshift,hcfg]
  simp only [Option.map_some,Option.some.injEq,Prod.mk.injEq]
  constructor
  · trivial
  · constructor <;> simp [Int.max_def] <;> omega

/-- The only C/0 gateway of Junc(2,v,1) is reached at a strict head
    record with a blank entire right tape, after 6v+22 steps. -/
theorem junc2_w1_gate_max (v : Nat) (hv : 1 ≤ v) :
  runWithMax (6*v+22) (junc 2 v 1) =
    some (z 2 (true::false::ones (2*v+14)) false [],
      ((2*v+6 : Nat) : Int), ((2*v+6 : Nat) : Int)) := by
  have hfirst := junc2_w1_to_midA_max v
  have hlast := midApos_w1_gate_max v hv
  rw [show 6*v+22 = (2*v+6)+(4*v+16) by omega,
      runWithMax_add,hfirst]
  simp only [Option.bind_some]
  rw [hlast]
  simp only [Option.map_some,Option.some.injEq,Prod.mk.injEq]
  constructor
  · trivial
  · constructor <;> simp [Int.max_def] <;> omega

/-- Sharp all-primitive-prefix head maximum of an ENTIRE Junc(2,v,1)
    exceptional return: 8v+54 steps, net displacement minus six, and
    maximum 2v+7 reached one move after its sole C/0 gateway. -/
theorem junc2_w1_full_max (v : Nat) (hv : 1 ≤ v) :
  runWithMax (8*v+54) (junc 2 v 1) =
    some (junc 0 0 (2*v+10), -6, ((2*v+7 : Nat) : Int)) := by
  have hfirst := junc2_w1_gate_max v hv
  have htail := c0_tail_max v
  rw [show 8*v+54=(6*v+22)+(2*v+32) by omega,
      runWithMax_add,hfirst]
  simp only [Option.bind_some]
  rw [htail]
  simp only [Option.map_some,Option.some.injEq,Prod.mk.injEq]
  constructor
  · trivial
  · constructor <;> simp [Int.max_def] <;> omega

#print axioms a_right_pairs_max
#print axioms midAaux_all_gate_max
#print axioms junc2_w1_gate_max
#print axioms junc2_w1_full_max

end BB429W2Junc2GateMax
