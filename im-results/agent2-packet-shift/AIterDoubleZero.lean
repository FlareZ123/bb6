import Lean.Elab.Tactic.Omega
import EDoubleTripleGeneral

set_option maxHeartbeats 15000000
set_option maxRecDepth 8192
set_option linter.unusedSimpArgs false

namespace BB6.Agent2AIterDoubleZero
open CryptidBoundary

def front (v r : Nat) : List Bool :=
  pairs (v+2) ++ ([true,true,false] ++ (pairs r ++ [false]))

def out (v r : Nat) : List Bool :=
  List.replicate (2*v+1) true ++
    (false :: List.replicate (2*r+6) true)

private theorem aZeroTwo (L zs : List Bool) :
    run 2 (⟨L,false,false::zs,0⟩ : Cfg) =
      ⟨L,true,true::zs,2⟩ := by
  simp [run,step,goL,goR]

/-- Crossing the literal 0110101 pattern from C/1 has a fixed seven-step
    action regardless of the untouched left and right contexts. -/
private theorem cSeven (L zs : List Bool) :
    run 7
      (⟨[false,true,true,false,true,false,true]++L,true,zs,2⟩ : Cfg) =
    ⟨L,true,[true,false,true,true,true,true,true]++zs,2⟩ := by
  simp [run,step,goL,goR]

private theorem opSplit (v : Nat) (L : List Bool) :
    [false,true,true] ++ (oppairs (v+2) ++ L) =
    [false,true,true,false,true,false,true] ++ (oppairs v ++ L) := by
  simp [oppairs,List.append_assoc]

private theorem onesShift (v r : Nat) (ys : List Bool) :
    List.replicate (2*v) true ++
      ([true,false,true,true,true,true,true] ++
        (List.replicate (2*r) true ++ true::ys)) =
    out v r ++ ys := by
  have h : List.replicate (2*v+1) true =
      List.replicate (2*v) true ++ [true] := by
    rw [show 2*v+1=(2*v)+1 by omega,←List.replicate_append_replicate]
    rfl
  have hr : List.replicate (2*r+6) true =
      List.replicate 5 true ++ (List.replicate (2*r) true ++ [true]) := by
    rw [show 2*r+6=5+(2*r+1) by omega,
       ←List.replicate_append_replicate,
       show 2*r+1=(2*r)+1 by omega,
       ←List.replicate_append_replicate]
    rfl
  rw [h,hr]
  simp [out,List.append_assoc,List.replicate_succ]

/-- Exact, unbounded, literal original six-state A/0 to C/1 turnaround:
    (10)^(v+2) 110 (10)^r 0 Y is consumed for every v,r,Y and any
    unknown physical left tape, leaving 1^(2v+1) 0 1^(2r+6) Y. -/
theorem a_double_zero_turn (v r : Nat) (L ys : List Bool) :
    run (4*v+4*r+20)
      (⟨L,false,front v r ++ ys,0⟩ : Cfg) =
    ⟨L,true,out v r ++ ys,2⟩ := by
  let U : List Bool := oppairs (v+2) ++ L
  let V : List Bool := [false,true,true] ++ U
  let R : List Bool := oppairs r ++ V
  let zs : List Bool := pairs r ++ (false :: ys)
  let afterSeven : Cfg := ⟨V,false,zs,0⟩
  let beforeZero : Cfg := ⟨R,false,false::ys,0⟩
  let afterZero : Cfg := ⟨R,true,true::ys,2⟩
  let afterR : Cfg := ⟨V,true,
    List.replicate (2*r) true ++ true::ys,2⟩
  let afterC7 : Cfg := ⟨oppairs v ++ L,true,
    [true,false,true,true,true,true,true] ++
      (List.replicate (2*r) true ++ true::ys),2⟩
  have hstart : run (2*(v+2))
      (⟨L,false,front v r ++ ys,0⟩ : Cfg) =
      (⟨U,false,[true,true,false]++zs,0⟩ : Cfg) := by
    dsimp [U,zs,front]
    rw [List.append_assoc]
    exact aTenOppIter (v+2) L ([true,true,false]++(pairs r++(false::ys)))
  have hseven : run 7
      (⟨U,false,[true,true,false]++zs,0⟩ : Cfg) =
      afterSeven := by
    dsimp [U,V,zs,afterSeven]
    exact aDoubleSeven (v+1) L (pairs r ++ (false::ys))
  have hten : run (2*r) afterSeven = beforeZero := by
    dsimp [afterSeven,beforeZero,R,V,zs]
    exact aTenOppIter r
      ([false,true,true] ++ (oppairs (v+2) ++ L)) (false::ys)
  have hzero : run 2 beforeZero = afterZero := by
    dsimp [beforeZero,afterZero]
    exact aZeroTwo R ys
  have hback : run (2*r) afterZero = afterR := by
    dsimp [afterZero,afterR,R]
    exact cWalk_run r V (true::ys)
  have hc7 : run 7 afterR = afterC7 := by
    dsimp [afterR,afterC7,V]
    rw [opSplit]
    exact cSeven (oppairs v++L)
      (List.replicate (2*r) true ++ true::ys)
  have hlast : run (2*v) afterC7 =
      (⟨L,true,out v r ++ ys,2⟩ : Cfg) := by
    dsimp [afterC7]
    rw [cWalk_run]
    exact congrArg (fun xs : List Bool => (⟨L,true,xs,2⟩ : Cfg))
      (onesShift v r ys)
  have ht : 4*v+4*r+20 =
      2*(v+2)+(7+(2*r+(2+(2*r+(7+2*v))))) := by omega
  rw [ht,run_add,hstart]
  rw [run_add,hseven]
  rw [run_add,hten]
  rw [run_add,hzero]
  rw [run_add,hback]
  rw [run_add,hc7]
  exact hlast

#print axioms a_double_zero_turn
end BB6.Agent2AIterDoubleZero
