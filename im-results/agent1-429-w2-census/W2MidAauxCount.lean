import W4CZeroCount
import High2TailBase
import Lean.Elab.Tactic.Omega

set_option maxRecDepth 8192
set_option maxHeartbeats 30000000

namespace BB429W2MidAauxCount

open BB429OddExcursion BB429SourceE1Return BB429FinishScanEDelta
open BB429W4CZeroSafe BB429W4CZeroCount BB429High2Tail
open BB429JuncHeadExcursion

/-- An entire A/01 rightward sweep, including arbitrary left and right
    context, processes no C/0 instruction. -/
theorem a_right_pairs_safe (j : Nat) (left suffix : List Bool) :
    runSafe (2*j) (z 0 left false (tens j ++ suffix)) =
      some (z 0 (ones (2*j) ++ left) false suffix) := by
  induction j generalizing left with
  | zero => rfl
  | succ j ih =>
      have hfirst : runSafe 2 (z 0 left false (tens (j+1) ++ suffix)) =
          some (z 0 (true::true::left) false (tens j ++ suffix)) := by rfl
      rw [show 2*(j+1) = 2+2*j by omega,runSafe_add,hfirst]
      simp only [Option.bind_some]
      rw [ih (true::true::left)]
      have hwords : ones (2*j) ++ (true::true::left) =
          ones (2*(j+1)) ++ left := by
        change (List.replicate (2*j) true) ++ (true::true::left) = _
        rw [show 2*(j+1) = (2*j)+2 by omega]
        change List.replicate (2*j) true ++ (true::true::left) =
          List.replicate (2*j+2) true ++ left
        rw [show 2*j+2 = (2*j)+2 by omega,←List.replicate_append_replicate]
        simp [List.append_assoc]
      rw [hwords]
      rw [show 2+2*j=2*(j+1) by omega]

/-- An E/1 leftward sweep over any marked block is C/0-free. -/
theorem E1_ones_safe (j : Nat) (left suffix : List Bool) :
    runSafe j (z 4 (ones j ++ left) true suffix) =
      some (z 4 left true (ones j ++ suffix)) := by
  induction j generalizing suffix with
  | zero => rfl
  | succ j ih =>
      have hfirst : runSafe 1 (z 4 (ones (j+1) ++ left) true suffix) =
          some (z 4 (ones j ++ left) true (true::suffix)) := by rfl
      rw [show j+1 = 1+j by omega,runSafe_add,show 1+j=j+1 by omega,hfirst]
      simp only [Option.bind_some]
      rw [ih (true::suffix)]
      have hright : ones j ++ (true::suffix) = ones (j+1) ++ suffix := by
        simp [ones,List.replicate_succ',List.append_assoc]
      rw [hright]

private theorem ones_add (m n : Nat) : ones (m+n) = ones m ++ ones n := by
  simp [ones]

private theorem tail_ones (j : Nat) :
    ones j ++ [true,false,true] = true :: (ones j ++ [false,true]) := by
  have h : ones j ++ [true] = true :: ones j := by
    have h1 : ones (j+1) = ones j ++ [true] := List.replicate_succ'
    have h2 : ones (j+1) = true :: ones j := List.replicate_succ
    exact h1.symm.trans h2
  calc
    ones j ++ [true,false,true] = (ones j ++ [true]) ++ [false,true] := by
      simp [List.append_assoc]
    _ = true :: (ones j ++ [false,true]) := by rw [h]; rfl

/-- For every natural k, this exact original-table A/F boundary
    executes precisely one C/0 instruction before the canonical Junc.
    Its C/0 has a completely blank right half-tape. -/
theorem midAaux_zero_count (k : Nat) :
    runCount (4*k+36) (midAaux 0 k) =
      some (junc 0 0 (2*k+6),1) := by
  have h0 := runSafe_to_count_zero 4 (midAaux 0 k)
    (z 0 (ones 8) false (tens k ++ [false,true])) (by rfl)
  have h1 := runSafe_to_count_zero (2*k)
    (z 0 (ones 8) false (tens k ++ [false,true]))
    (z 0 (ones (2*k) ++ ones 8) false [false,true])
    (a_right_pairs_safe k (ones 8) [false,true])
  have hsum : ones (2*k) ++ ones 8 = ones (2*k+8) := by
    rw [show 2*k+8 = 2*k+8 by omega,ones_add]
  have h2 := runSafe_to_count_zero 2
    (z 0 (ones (2*k+8)) false [false,true])
    (z 2 (ones (2*k+10)) true []) (by
      have hleft : ones (2*k+10) = true::true::ones (2*k+8) := by
        rw [show 2*k+10 = 2+(2*k+8) by omega,ones_add]
        rfl
      rw [hleft]; rfl)
  have h3 : runCount 8 (z 2 (ones (2*k+10)) true []) =
    some (z 4 (ones (2*k+10)) true [true,false,true],1) := by rfl
  have h4 := runSafe_to_count_zero (2*k+10)
    (z 4 (ones (2*k+10)) true [true,false,true])
    (z 4 [] true (ones (2*k+10) ++ [true,false,true]))
    (by simpa only [List.append_nil] using
        (E1_ones_safe (2*k+10) [] [true,false,true]))
  have h5 := runSafe_to_count_zero 12
    (z 4 [] true (ones 4 ++ (ones (2*k+6) ++ [true,false,true])))
    (z 0 (ones 6) true (ones (2*k+6) ++ [true,false,true]))
    (by rfl)
  have htime : 4*k+36 = 4 + ((2*k)+(2+(8+((2*k+10)+12)))) := by omega
  rw [htime,runCount_add,h0]
  simp only [Option.bind_some]
  rw [runCount_add,h1]
  simp only [Option.bind_some]
  rw [hsum,runCount_add,h2]
  simp only [Option.bind_some]
  rw [runCount_add,h3]
  simp only [Option.bind_some]
  rw [runCount_add,h4]
  simp only [Option.bind_some]
  have hright : ones (2*k+10) ++ [true,false,true] =
      ones 4 ++ (ones (2*k+6) ++ [true,false,true]) := by
    rw [show 2*k+10 = 4+(2*k+6) by omega,ones_add,List.append_assoc]
  rw [hright,h5]
  simp only [Option.map_some,Option.some.injEq,Prod.mk.injEq]
  constructor
  · change z 0 (ones 6) true (ones (2*k+6) ++ [true,false,true]) =
      z 0 (true :: ones 5) true (true :: (ones (2*k+6) ++ [false,true]))
    rw [tail_ones]
    rfl
  · trivial

/-- Positive-left A/F reduction does not execute C/0. -/
theorem midAaux_step2_safe (v k : Nat) :
    runSafe 2 (midAaux (v+1) k) = some (midAaux v (k+1)) := by rfl

theorem midAaux_reduce_safe (v k : Nat) :
    runSafe (2*v) (midAaux v k) = some (midAaux 0 (k+v)) := by
  induction v generalizing k with
  | zero => rfl
  | succ v ih =>
      rw [show 2*(v+1) = 2+2*v by omega,runSafe_add,midAaux_step2_safe]
      simp only [Option.bind_some]
      rw [ih (k+1)]
      have hparam : (k+1)+v = k+(v+1) := by omega
      rw [hparam]

/-- The general A/F residual boundary has exactly one C/0. -/
theorem midAaux_all_count (v k : Nat) :
    runCount (2*v+(4*(k+v)+36)) (midAaux v k) =
      some (junc 0 0 (2*(k+v)+6),1) := by
  have hpre := runSafe_to_count_zero (2*v) (midAaux v k)
    (midAaux 0 (k+v)) (midAaux_reduce_safe v k)
  rw [runCount_add,hpre]
  simp only [Option.bind_some]
  rw [midAaux_zero_count]
  rfl

/-- The fixed MidA entry into A/F is also C/0-free. -/
theorem midApos_to_midAaux_safe (v : Nat) :
    runSafe 6 (midApos 1 (v+1) 1) = some (midAaux v 3) := by
  have hones : ones (2*(v+3)) = ones 5 ++ ones (2*v+1) := by
    rw [show 2*(v+3) = 5+(2*v+1) by omega,ones_add]
  unfold midApos
  rw [show v+1+2=v+3 by omega]
  rw [hones]
  simp [runSafe,oneSafe,one,action,midAaux,
    pairs01,ones,tens,z,List.append_assoc]

/-- Every positive-middle MidA right-one passage processes one C/0. -/
theorem midApos_w1_count (v : Nat) (hv : 1 ≤ v) :
    runCount (6*v+48) (midApos 1 v 1) =
      some (junc 0 0 (2*v+10),1) := by
  have hsub : v-1+1 = v := Nat.sub_add_cancel hv
  have h6 : runCount 6 (midApos 1 v 1) =
      some (midAaux (v-1) 3,0) :=
    runSafe_to_count_zero 6 (midApos 1 v 1)
      (midAaux (v-1) 3) (by
        simpa [hsub] using midApos_to_midAaux_safe (v-1))
  have hremain := midAaux_all_count (v-1) 3
  have htime : 6*v+48 = 6+(2*(v-1)+(4*(3+(v-1))+36)) := by omega
  rw [htime,runCount_add,h6]
  simp only [Option.bind_some]
  rw [hremain]
  have hparam : 2*(3+(v-1))+6 = 2*v+10 := by omega
  rw [hparam]
  rfl

#print axioms midAaux_zero_count
#print axioms midAaux_all_count
#print axioms midApos_to_midAaux_safe
#print axioms midApos_w1_count

end BB429W2MidAauxCount
