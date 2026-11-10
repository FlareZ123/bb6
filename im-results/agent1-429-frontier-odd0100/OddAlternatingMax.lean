import OddCZeroToE1Max
import Lean.Elab.Tactic.Omega

set_option maxRecDepth 8192
set_option maxHeartbeats 30000000

namespace BB429OddAlternatingMax
open BB429OddExcursion BB429CZeroEvenReturn BB429OddCZeroToE1Max
open BB429W4HeadMax BB429CZeroHeadFrontier

private def quads : Nat → List Bool
  | 0 => []
  | q+1 => [true,false,true,true] ++ quads q

private def extras : Nat → List Bool
  | 0 => []
  | q+1 => [false,true,true,true] ++ extras q

private theorem tens_add (a b : Nat) :
    tens (a+b) = tens a ++ tens b := by
  induction a with
  | zero => simp [tens]
  | succ a ih => simp only [Nat.succ_add,tens,ih,List.cons_append]

private theorem e_transfer6_max (l r : List Bool) :
    runWithMax 6 (z 4 (tens 2 ++ l) true r) =
      some (z 4 l true ([true,false,true,true] ++ r),-4,0) := by rfl

private theorem e_transfer_many_max (q : Nat) (l r : List Bool) :
    runWithMax (6*q) (z 4 (tens (2*q) ++ l) true r) =
      some (z 4 l true (quads q ++ r),-((4*q:Nat):Int),0) := by
  induction q generalizing l r with
  | zero => simp [runWithMax,tens,quads]
  | succ q ih =>
    have hword : tens (2*(q+1)) ++ l =
        tens (2*q) ++ (tens 2 ++ l) := by
      rw [show 2*(q+1)=2*q+2 by omega,tens_add]
      simp only [List.append_assoc]
    rw [show 6*(q+1)=6*q+6 by omega,runWithMax_add,hword,ih]
    simp only [Option.bind_some]
    rw [e_transfer6_max]
    simp only [Option.map_some,Option.some.injEq,Prod.mk.injEq]
    constructor
    · rfl
    constructor <;> simp [Int.max_def] <;> omega

private theorem quad_shift (q : Nat) (r : List Bool) :
    quads q ++ (true :: r) = true :: (extras q ++ r) := by
  induction q with
  | zero => rfl
  | succ q ih =>
    simp only [quads,extras,List.append_assoc]
    rw [ih]
    rfl

private theorem e_base7_max (l r : List Bool) :
    runWithMax 7 (z 4 ([true,false,false] ++ l) true (true :: r)) =
      some (z 0 ([true,false,true,true] ++ l) true r,1,1) := by rfl

private theorem a_extra8_max (l r : List Bool) :
    runWithMax 8 (z 0 ([true,false,true,true] ++ l) true
      ([false,true,true,true] ++ r)) =
      some (z 0 ([true,false,true,true] ++ ones 4 ++ l) true r,4,4) := by rfl

private theorem a_extra_many_max (q : Nat) (l r : List Bool) :
    runWithMax (8*q) (z 0 ([true,false,true,true] ++ l) true (extras q ++ r)) =
      some (z 0 ([true,false,true,true] ++ ones (4*q) ++ l) true r,
        ((4*q:Nat):Int),((4*q:Nat):Int)) := by
  induction q generalizing l r with
  | zero => simp [runWithMax,ones,extras]
  | succ q ih =>
    rw [show 8*(q+1)=8+8*q by omega,runWithMax_add]
    change ((runWithMax 8 (z 0 ([true,false,true,true] ++ l) true
      ([false,true,true,true] ++ (extras q ++ r)))).bind _) = _
    rw [a_extra8_max]
    simp only [Option.bind_some]
    have h := ih (ones 4 ++ l) r
    simp only [List.append_assoc] at h ⊢
    rw [h]
    simp only [Option.map_some,Option.some.injEq,Prod.mk.injEq]
    constructor
    · have hw : ones (4*q) ++ ones 4 ++ l = ones (4*(q+1)) ++ l := by
        change (List.replicate (4*q) true ++ List.replicate 4 true) ++ l =
          List.replicate (4*(q+1)) true ++ l
        rw [List.replicate_append_replicate]
        congr 1
      simpa only [List.append_assoc] using congrArg (fun xs =>
        z 0 ([true,false,true,true] ++ xs) true r) hw
    constructor <;> simp [Int.max_def] <;> omega

private theorem a_finish2_max (m : Nat) (l : List Bool) :
    runWithMax 2 (z 0 ([true,false,true,true] ++ l) true
      (tens m ++ [false,true])) =
      some (z 0 ([true,true] ++ l) false
        (tens (m+1) ++ [false,true]),-2,0) := by rfl

private theorem a_finish4_max (l : List Bool) :
    runWithMax 4 (z 0 l false [false,true]) =
      some (z 2 ([true,false,true,true] ++ l) false [],4,4) := by rfl

private theorem a_finish_max (m : Nat) (l : List Bool) :
    runWithMax (2*m+8) (z 0 ([true,false,true,true] ++ l) true
      (tens m ++ [false,true])) =
      some (z 2 ([true,false] ++ ones (2*m+6) ++ l) false [],
        ((2*m+4:Nat):Int),((2*m+4:Nat):Int)) := by
  have h0 := a_finish2_max m l
  have h1 := ar_pairs_max_uniform (m+1) ([true,true] ++ l) [false,true]
  have h2 := a_finish4_max (ones (2*(m+1)) ++ ([true,true] ++ l))
  rw [show 2*m+8=2+(2*(m+1)+4) by omega,
      runWithMax_add,h0]
  simp only [Option.bind_some]
  rw [runWithMax_add,h1]
  simp only [Option.bind_some]
  rw [h2]
  simp only [Option.map_some,Option.some.injEq,Prod.mk.injEq]
  constructor
  · have h : ones 2 ++ ones (2*(m+1)) ++ ones 2 = ones (2*m+6) := by
      change (List.replicate 2 true ++ List.replicate (2*(m+1)) true) ++
        List.replicate 2 true = List.replicate (2*m+6) true
      rw [List.replicate_append_replicate,List.replicate_append_replicate]
      congr 1
      omega
    exact congrArg (fun xs => z 2 xs false []) (by
      simpa [ones,List.append_assoc] using congrArg (fun xs =>
        [true,false] ++ (xs ++ l)) h)
  constructor <;> simp [Int.max_def] <;> omega

/-- The new all-parameter safe C/0 return is a right-record event.
    All primitive prefixes stay no farther than three cells right of entry. -/
theorem odd_alternating_head_max (m q : Nat) (tail : List Bool) :
    runWithMax (4*m+14*q+21)
      (z 2 (ones (2*m+1) ++ [false] ++ tens (2*q+1) ++ [false] ++ tail)
        false []) =
    some (z 2 ([true,false] ++ ones (2*m+4*q+6) ++ tail)
      false [],3,3) := by
  have h0 := odd_C0_to_E1_head_max m (tens (2*q+1) ++ [false] ++ tail)
  have htime : 4*m+14*q+21=(2*m+6)+(6*q+(7+(8*q+(2*m+8)))) := by omega
  have hinit : ones (2*m+1) ++ [false] ++ tens (2*q+1) ++ [false] ++ tail =
      ones (2*m+1) ++ (false :: (tens (2*q+1) ++ [false] ++ tail)) := by
    simp [List.append_assoc]
  rw [htime,runWithMax_add,hinit,h0]
  simp only [Option.bind_some]
  have hleft : tens (2*q+1) ++ [false] ++ tail =
      tens (2*q) ++ (tens 1 ++ [false] ++ tail) := by
    rw [show 2*q+1=2*q+1 by omega,tens_add]
    simp only [List.append_assoc]
  rw [hleft,runWithMax_add,e_transfer_many_max]
  simp only [Option.bind_some]
  have hr : quads q ++ (true :: tens m ++ [false,true]) =
       true :: (extras q ++ (tens m ++ [false,true])) := by
    simpa [List.append_assoc] using quad_shift q (tens m ++ [false,true])
  have hb : tens 1 ++ [false] ++ tail = [true,false,false] ++ tail := by rfl
  rw [runWithMax_add,hr,hb,e_base7_max]
  simp only [Option.bind_some]
  rw [runWithMax_add,a_extra_many_max]
  simp only [Option.bind_some]
  have hfinish := a_finish_max m (ones (4*q) ++ tail)
  simp only [List.append_assoc] at hfinish ⊢
  rw [hfinish]
  simp only [Option.map_some,Option.some.injEq,Prod.mk.injEq]
  constructor
  · have hw : ones (2*m+6) ++ (ones (4*q) ++ tail) =
        ones (2*m+4*q+6) ++ tail := by
      change List.replicate (2*m+6) true ++ (List.replicate (4*q) true ++ tail) =
        List.replicate (2*m+4*q+6) true ++ tail
      rw [← List.append_assoc, List.replicate_append_replicate]
      have hn : 2*m+6+4*q=2*m+4*q+6 := by omega
      rw [hn]
    simpa [List.append_assoc] using congrArg (fun xs => z 2 ([true,false] ++ xs) false []) hw
  constructor <;> simp [Int.max_def] <;> omega

#print axioms odd_alternating_head_max
end BB429OddAlternatingMax
