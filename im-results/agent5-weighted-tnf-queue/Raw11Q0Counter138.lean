import Agent5MultiPump
import Root56Coverage
set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace BB6Coverage.Agent31Pump.Multi.Raw11Q0Counter138
open BB6Coverage Agent31Pump BB6.Agent13BlankDelay

def table : PartialMachine := fun s => match s.1.val,s.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 0,true => some (some ⟨true,false,2⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 1,true => some (some ⟨true,true,3⟩)
  | 2,false => some (some ⟨false,false,0⟩)
  | 2,true => some (some ⟨true,false,0⟩)
  | 3,false => none
  | 3,true => some (some ⟨false,true,4⟩)
  | 4,false => some (some ⟨false,true,5⟩)
  | 4,true => some (some ⟨true,true,4⟩)
  | 5,false => some (some ⟨true,true,0⟩)
  | 5,true => some (some ⟨false,false,2⟩)
  | _,_ => none

def pair : List Bool := [true,true]
def H (n : Nat) : Z0 :=
  ⟨5,[false,false,false] ++ rep pair n ++ rep pair 17 ++ [false] ++ rep pair 6,[]⟩
def J (x y : Nat) : Z0 :=
  ⟨5,[false,false,true,true,true,false] ++ rep pair x ++ rep pair 1 ++ [false] ++ rep pair y ++ rep pair 16 ++ [false] ++ rep pair 2,[]⟩

private theorem rep_num_0 : rep [true,true] 0 = [] := by decide +kernel
private theorem rep_num_1 : rep [true,true] 1 = [true,true] := by decide +kernel
private theorem rep_num_2 : rep [true,true] 2 = [true,true,true,true] := by decide +kernel
private theorem rep_num_3 : rep [true,true] 3 = [true,true,true,true,true,true] := by decide +kernel
private theorem rep_num_4 : rep [true,true] 4 = [true,true,true,true,true,true,true,true] := by decide +kernel
private theorem rep_num_5 : rep [true,true] 5 = [true,true,true,true,true,true,true,true,true,true] := by decide +kernel
private theorem rep_num_6 : rep [true,true] 6 = [true,true,true,true,true,true,true,true,true,true,true,true] := by decide +kernel
private theorem rep_num_7 : rep [true,true] 7 = [true,true,true,true,true,true,true,true,true,true,true,true,true,true] := by decide +kernel
private theorem rep_num_11 : rep [true,true] 11 = [true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true] := by decide +kernel
private theorem rep_num_14 : rep [true,true] 14 = [true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true] := by decide +kernel
private theorem rep_num_16 : rep [true,true] 16 = [true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true] := by decide +kernel
private theorem rep_num_17 : rep [true,true] 17 = [true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true] := by decide +kernel

def certH : Cert := ⟨⟨5,(.periodic [false,false,false,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true] [true,true] false (.lit [true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,false,true,true,true,true,true,true,true,true,true,true,true,true])),(.lit [])⟩,⟨5,(.periodic [false,false,true,true,true,false,true,true,true,true,true,true,true,true] [true,true] false (.lit [true,true,true,true,true,true,true,true,false,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,false,true,true,true,true])),(.lit [])⟩,[
    .steps 10,
    .left [true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true] [] [true,true] [true,true] false (.lit [true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,false,true,true,true,true,true,true,true,true,true,true,true,true]) (.lit [true,true,false]) 2,
    .steps 40,
    .right [true] [true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true] [true,true] [true,true] false (.lit [false,true,true,true,true,true,true,true,true,true,true,true,true,true,true]) (.lit [true,true,false]) 2,
    .steps 46,
    .left [true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true] [] [true,true] [true,true] false (.lit [false,true,true,true,true,true,true,true,true,true,true,true,true,true,true]) (.lit [false,true,true,true,false]) 2,
    .steps 102,
    .right [true] [true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true] [true,true] [true,true] false (.lit [false,true,true,true,true,true,true,true,true,true,true,true,true,false,true,true,true,true]) (.lit [false,true,true,true,false]) 2,
    .steps 38,
    .left [true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true] [] [true,true] [true,true] false (.lit [false,true,true,true,true,true,true,true,true,true,true,true,true,false,true,true,true,true]) (.lit [false,false,true,true,false]) 2,
    .steps 92,
    .right [true] [true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true] [true,true] [true,true] false (.lit [false,true,true,true,true,true,true,true,true,true,true,false,true,true,true,true,true,true,true,true]) (.lit [false,false,true,true,false]) 2,
    .steps 52,
    .left [true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true] [] [true,true] [true,true] false (.lit [false,true,true,true,true,true,true,true,true,true,true,false,true,true,true,true,true,true,true,true]) (.lit [false,true,false,true,true,true,false]) 2,
    .steps 84,
    .right [true] [true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true] [true,true] [true,true] false (.lit [false,true,true,true,true,true,true,true,true,false,true,true,true,true,true,true,true,true,true,true,true,true]) (.lit [false,true,false,true,true,true,false]) 2,
    .steps 36,
    .left [true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true] [] [true,true] [true,true] false (.lit [false,true,true,true,true,true,true,true,true,false,true,true,true,true,true,true,true,true,true,true,true,true]) (.lit [false,false,false,true,true,true,false]) 2,
    .steps 74,
    .right [true] [true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true] [true,true] [true,true] false (.lit [false,true,true,true,true,true,true,false,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true]) (.lit [false,false,false,true,true,true,false]) 2,
    .steps 52,
    .left [true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true] [] [true,true] [true,true] false (.lit [false,true,true,true,true,true,true,false,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true]) (.lit [false,true,true,true,false,true,false,true,true,true,false]) 2,
    .steps 64,
    .right [true] [true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true] [true,true] [true,true] false (.lit [false,true,true,true,true,false,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true]) (.lit [false,true,true,true,false,true,false,true,true,true,false]) 2,
    .steps 32,
    .left [true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true] [] [true,true] [true,true] false (.lit [false,true,true,true,true,false,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true]) (.lit [false,false,true,true,false,true,false,true,true,true,false]) 2,
    .steps 54,
    .right [true] [true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true] [true,true] [true,true] false (.lit [false,true,true,false,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true]) (.lit [false,false,true,true,false,true,false,true,true,true,false]) 2,
    .steps 40,
    .left [true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true] [] [true,true] [true,true] false (.lit [false,true,true,false,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true]) (.lit [false,true,false,false,false,true,true,true,false]) 2,
    .steps 161,
    .right [true] [true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true] [true,true] [true,true] false (.lit [false,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,false,true,true,true,true]) (.lit [false,true,false,false,false,true,true,true,false]) 2,
    .steps 29,
    .left [true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true] [] [true,true] [true,true] false (.lit [false,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,false,true,true,true,true]) (.lit [false,false,false,false,false,true,true,true,false]) 2,
    .steps 29,
    .right [true] [true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true] [true,true] [true,true] false (.lit [false,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,false,true,true,true,true]) (.lit [false,false,false,false,false,true,true,true,false]) 2,
    .steps 33,
    .left [true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true] [] [true,true] [true,true] false (.lit [false,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,false,true,true,true,true]) (.lit [false,true,true,true,false,true,true,true,false]) 2,
    .steps 27,
    .right [true] [true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true] [true,true] [true,true] false (.lit [false,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,false,true,true,true,true]) (.lit [false,true,true,true,false,true,true,true,false]) 2,
    .steps 25,
    .left [true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true] [] [true,true] [true,true] false (.lit [false,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,false,true,true,true,true]) (.lit [false,false,true,true,false,true,true,true,false]) 2,
    .steps 25,
    .right [true] [true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true] [true,true] [true,true] false (.lit [false,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,false,true,true,true,true]) (.lit [false,false,true,true,false,true,true,true,false]) 2,
    .steps 33,
    .left [true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true] [] [true,true] [true,true] false (.lit [false,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,false,true,true,true,true]) (.lit [false,true,false,false,true,true,false]) 2,
    .steps 25,
    .right [true] [true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true] [true,true] [true,true] false (.lit [false,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,false,true,true,true,true]) (.lit [false,true,false,false,true,true,false]) 2,
    .steps 23,
    .left [true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true] [] [true,true] [true,true] false (.lit [false,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,false,true,true,true,true]) (.lit [false,false,false,false,true,true,false]) 2,
    .steps 23,
    .right [true] [true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true] [true,true] [true,true] false (.lit [false,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,false,true,true,true,true]) (.lit [false,false,false,false,true,true,false]) 2,
    .steps 27,
    .left [true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true] [] [true,true] [true,true] false (.lit [false,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,false,true,true,true,true]) (.lit [false,true,true,true,true,true,false]) 2,
    .steps 21,
    .right [true] [true,true,true,true,true,true,true,true,true,true,true,true,true,true,true] [true,true] [true,true] false (.lit [false,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,false,true,true,true,true]) (.lit [false,true,true,true,true,true,false]) 2,
    .steps 19,
    .left [true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true] [] [true,true] [true,true] false (.lit [false,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,false,true,true,true,true]) (.lit [false,false,true,true,true,true,false]) 2,
    .steps 19,
    .right [true] [true,true,true,true,true,true,true,true,true,true,true,true,true] [true,true] [true,true] false (.lit [false,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,false,true,true,true,true]) (.lit [false,false,true,true,true,true,false]) 2,
    .steps 25
  ],60,0,1360⟩
theorem checkedH : check table certH = true := by decide +kernel

theorem stepH (n m : Nat) :
    run0 table (60*n+0*0+1360) (H n) = some (J (n+7) 4) := by
  have hh := check_sound table certH checkedH n 0
  rw [← PZ.norm_sound certH.source n 0, ← PZ.norm_sound certH.target n 0] at hh
  change run0 table (60*n+0*0+1360) (PZ.eval ⟨5,(.periodic [false,false,false] [true,true] false (.lit [true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,false,true,true,true,true,true,true,true,true,true,true,true,true])),(.lit [])⟩ n 0) = some (PZ.eval ⟨5,(.periodic [false,false,true,true,true,false] [true,true] false (.lit [true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,false,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,false,true,true,true,true])),(.lit [])⟩ n 0) at hh
  simpa only [H,J,pair,PZ.eval,Word.eval,Bool.false_eq_true,ite_false,ite_true,← Auto.rep_add,rep_num_0,rep_num_1,rep_num_2,rep_num_3,rep_num_4,rep_num_5,rep_num_6,rep_num_7,rep_num_11,rep_num_14,rep_num_16,rep_num_17,List.append_assoc,List.cons_append,List.nil_append,Nat.zero_mul,Nat.zero_add,Nat.add_zero] using hh

def certJ : Cert := ⟨⟨5,(.periodic [false,false,true,true,true,false,true,true,true,true,true,true] [true,true] false (.periodic [true,true,true,true,true,true,false,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true] [true,true] true (.lit [true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,false,true,true,true,true]))),(.lit [])⟩,⟨5,(.periodic [false,false,true,true,true,false,true,true] [true,true] false (.periodic [true,true,false,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true] [true,true] true (.lit [true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,false,true,true,true,true]))),(.lit [])⟩,[
    .steps 12,
    .left [true,true,true,true,true,true] [] [true,true] [true,true] false (.periodic [true,true,true,true,true,true,false,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true] [true,true] true (.lit [true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,false,true,true,true,true])) (.lit [false,true,true,true,false,true,true,true,false]) 2,
    .steps 15,
    .right [true] [true,true,true,true,true,true,true,true,true] [true,true] [true,true] false (.periodic [false,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true] [true,true] true (.lit [true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,false,true,true,true,true])) (.lit [false,true,true,true,false,true,true,true,false]) 2,
    .steps 13,
    .left [true,true,true,true,true,true,true,true,true,true] [] [true,true] [true,true] false (.periodic [false,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true] [true,true] true (.lit [true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,false,true,true,true,true])) (.lit [false,false,true,true,false,true,true,true,false]) 2,
    .steps 13,
    .right [true] [true,true,true,true,true,true,true] [true,true] [true,true] false (.periodic [false,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true] [true,true] true (.lit [true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,false,true,true,true,true])) (.lit [false,false,true,true,false,true,true,true,false]) 2,
    .steps 21,
    .left [true,true,true,true,true,true,true,true,true,true] [] [true,true] [true,true] false (.periodic [false,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true] [true,true] true (.lit [true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,false,true,true,true,true])) (.lit [false,true,false,false,true,true,false]) 2,
    .steps 13,
    .right [true] [true,true,true,true,true,true,true] [true,true] [true,true] false (.periodic [false,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true] [true,true] true (.lit [true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,false,true,true,true,true])) (.lit [false,true,false,false,true,true,false]) 2,
    .steps 11,
    .left [true,true,true,true,true,true,true,true] [] [true,true] [true,true] false (.periodic [false,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true] [true,true] true (.lit [true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,false,true,true,true,true])) (.lit [false,false,false,false,true,true,false]) 2,
    .steps 11,
    .right [true] [true,true,true,true,true] [true,true] [true,true] false (.periodic [false,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true] [true,true] true (.lit [true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,false,true,true,true,true])) (.lit [false,false,false,false,true,true,false]) 2,
    .steps 15,
    .left [true,true,true,true,true,true] [] [true,true] [true,true] false (.periodic [false,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true] [true,true] true (.lit [true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,false,true,true,true,true])) (.lit [false,true,true,true,true,true,false]) 2,
    .steps 9,
    .right [true] [true,true,true] [true,true] [true,true] false (.periodic [false,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true] [true,true] true (.lit [true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,false,true,true,true,true])) (.lit [false,true,true,true,true,true,false]) 2,
    .steps 7,
    .left [true,true,true,true] [] [true,true] [true,true] false (.periodic [false,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true] [true,true] true (.lit [true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,false,true,true,true,true])) (.lit [false,false,true,true,true,true,false]) 2,
    .steps 7,
    .right [true] [true] [true,true] [true,true] false (.periodic [false,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true] [true,true] true (.lit [true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,false,true,true,true,true])) (.lit [false,false,true,true,true,true,false]) 2,
    .steps 13
  ],24,0,160⟩
theorem checkedJ : check table certJ = true := by decide +kernel

theorem stepJ (n m : Nat) :
    run0 table (24*n+0*m+160) (J (n+5) m) = some (J (n+1) (m+6)) := by
  have hh := check_sound table certJ checkedJ n m
  rw [← PZ.norm_sound certJ.source n m, ← PZ.norm_sound certJ.target n m] at hh
  change run0 table (24*n+0*m+160) (PZ.eval ⟨5,(.periodic [false,false,true,true,true,false] [true,true] false (.periodic [true,true,true,true,true,true,true,true,true,true,true,true,false] [true,true] true (.lit [true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,false,true,true,true,true]))),(.lit [])⟩ n m) = some (PZ.eval ⟨5,(.periodic [false,false,true,true,true,false] [true,true] false (.periodic [true,true,true,true,false] [true,true] true (.lit [true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,false,true,true,true,true]))),(.lit [])⟩ n m) at hh
  simpa only [H,J,pair,PZ.eval,Word.eval,Bool.false_eq_true,ite_false,ite_true,← Auto.rep_add,rep_num_0,rep_num_1,rep_num_2,rep_num_3,rep_num_4,rep_num_5,rep_num_6,rep_num_7,rep_num_11,rep_num_14,rep_num_16,rep_num_17,List.append_assoc,List.cons_append,List.nil_append,Nat.zero_mul,Nat.zero_add,Nat.add_zero] using hh

def certJ2 : Cert := ⟨⟨5,(.periodic [false,false,true,true,true,false,true,true,false,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true] [true,true] false (.lit [true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,false,true,true,true,true])),(.lit [])⟩,⟨5,(.periodic [false,false,false,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true] [true,true] false (.lit [true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,false,true,true,true,true,true,true,true,true,true,true,true,true])),(.lit [])⟩,[
    .steps 23,
    .left [true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true] [] [true,true] [true,true] false (.lit [true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,false,true,true,true,true]) (.lit [false,true,true,false,true,true,true,false]) 2,
    .steps 39,
    .right [true] [true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true] [true,true] [true,true] false (.lit [false,true,true,true,true,true,true]) (.lit [false,true,true,false,true,true,true,false]) 2,
    .steps 37,
    .left [true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true] [] [true,true] [true,true] false (.lit [false,true,true,true,true,true,true]) (.lit [false,false,true,false,true,true,true,false]) 2,
    .steps 37,
    .right [true] [true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true] [true,true] [true,true] false (.lit [false,true,true,true,true,true,true,true,true]) (.lit [false,false,true,false,true,true,true,false]) 2,
    .steps 45,
    .left [true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true] [] [true,true] [true,true] false (.lit [false,true,true,true,true,true,true,true,true]) (.lit [false,true,true,false]) 2,
    .steps 39,
    .right [true] [true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true] [true,true] [true,true] false (.lit [false,true,true,true,true,true,true,true,true,true,true]) (.lit [false,true,true,false]) 2,
    .steps 37,
    .left [true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true] [] [true,true] [true,true] false (.lit [false,true,true,true,true,true,true,true,true,true,true]) (.lit [false,false,true,false]) 2,
    .steps 37,
    .right [true] [true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true] [true,true] [true,true] false (.lit [false,true,true,true,true,true,true,true,true,true,true,true,true]) (.lit [false,false,true,false]) 2,
    .steps 40
  ],16,0,334⟩
theorem checkedJ2 : check table certJ2 = true := by decide +kernel

theorem stepJ2 (n m : Nat) :
    run0 table (16*n+0*0+334) (J 0 n) = some (H n) := by
  have hh := check_sound table certJ2 checkedJ2 n 0
  rw [← PZ.norm_sound certJ2.source n 0, ← PZ.norm_sound certJ2.target n 0] at hh
  change run0 table (16*n+0*0+334) (PZ.eval ⟨5,(.periodic [false,false,true,true,true,false,true,true,false] [true,true] false (.lit [true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,false,true,true,true,true])),(.lit [])⟩ n 0) = some (PZ.eval ⟨5,(.periodic [false,false,false] [true,true] false (.lit [true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,false,true,true,true,true,true,true,true,true,true,true,true,true])),(.lit [])⟩ n 0) at hh
  simpa only [H,J,pair,PZ.eval,Word.eval,Bool.false_eq_true,ite_false,ite_true,← Auto.rep_add,rep_num_0,rep_num_1,rep_num_2,rep_num_3,rep_num_4,rep_num_5,rep_num_6,rep_num_7,rep_num_11,rep_num_14,rep_num_16,rep_num_17,List.append_assoc,List.cons_append,List.nil_append,Nat.zero_mul,Nat.zero_add,Nat.add_zero] using hh

def certJ4 : Cert := ⟨⟨5,(.periodic [false,false,true,true,true,false,true,true,true,true,false,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true] [true,true] false (.lit [true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,false,true,true,true,true])),(.lit [])⟩,⟨5,(.periodic [false,false,true,true,true,false,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true] [true,true] false (.lit [true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,false,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,false,true,true,true,true])),(.lit [])⟩,[
    .steps 53,
    .left [true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true] [] [true,true] [true,true] false (.lit [true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,false,true,true,true,true]) (.lit [false,false,false,true,true,false]) 2,
    .steps 43,
    .right [true] [true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true] [true,true] [true,true] false (.lit [false,true,true,true,true,true,true]) (.lit [false,false,false,true,true,false]) 2,
    .steps 61,
    .left [true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true] [] [true,true] [true,true] false (.lit [false,true,true,true,true,true,true]) (.lit [false,true,true,true,true,true,true,true,true,false]) 2,
    .steps 41,
    .right [true] [true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true] [true,true] [true,true] false (.lit [false,true,true,true,true,true,true,true,true]) (.lit [false,true,true,true,true,true,true,true,true,false]) 2,
    .steps 39,
    .left [true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true] [] [true,true] [true,true] false (.lit [false,true,true,true,true,true,true,true,true]) (.lit [false,false,true,true,true,true,true,true,true,false]) 2,
    .steps 39,
    .right [true] [true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true] [true,true] [true,true] false (.lit [false,true,true,true,true,true,true,true,true,true,true]) (.lit [false,false,true,true,true,true,true,true,true,false]) 2,
    .steps 140,
    .left [true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true] [] [true,true] [true,true] false (.lit [false,true,true,true,true,true,true,true,true,true,true]) (.lit [true,true,false,true,false,true,true,true,false]) 2,
    .steps 50,
    .right [true] [true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true] [true,true] [true,true] false (.lit [false,true,true,true,true,true,true,true,true,true,true,true,true]) (.lit [true,true,false,true,false,true,true,true,false]) 2,
    .steps 50,
    .left [true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true] [] [true,true] [true,true] false (.lit [false,true,true,true,true,true,true,true,true,true,true,true,true]) (.lit [false,false,false,true,true,true,false]) 2,
    .steps 104,
    .right [true] [true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true] [true,true] [true,true] false (.lit [false,true,true,true,true,true,true,true,true,true,true,false,true,true,true,true]) (.lit [false,false,false,true,true,true,false]) 2,
    .steps 66,
    .left [true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true] [] [true,true] [true,true] false (.lit [false,true,true,true,true,true,true,true,true,true,true,false,true,true,true,true]) (.lit [false,true,true,true,false,true,false,true,true,true,false]) 2,
    .steps 94,
    .right [true] [true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true] [true,true] [true,true] false (.lit [false,true,true,true,true,true,true,true,true,false,true,true,true,true,true,true,true,true]) (.lit [false,true,true,true,false,true,false,true,true,true,false]) 2,
    .steps 46,
    .left [true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true] [] [true,true] [true,true] false (.lit [false,true,true,true,true,true,true,true,true,false,true,true,true,true,true,true,true,true]) (.lit [false,false,true,true,false,true,false,true,true,true,false]) 2,
    .steps 84,
    .right [true] [true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true] [true,true] [true,true] false (.lit [false,true,true,true,true,true,true,false,true,true,true,true,true,true,true,true,true,true,true,true]) (.lit [false,false,true,true,false,true,false,true,true,true,false]) 2,
    .steps 54,
    .left [true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true] [] [true,true] [true,true] false (.lit [false,true,true,true,true,true,true,false,true,true,true,true,true,true,true,true,true,true,true,true]) (.lit [false,true,false,false,false,true,true,true,false]) 2,
    .steps 76,
    .right [true] [true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true] [true,true] [true,true] false (.lit [false,true,true,true,true,false,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true]) (.lit [false,true,false,false,false,true,true,true,false]) 2,
    .steps 44,
    .left [true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true] [] [true,true] [true,true] false (.lit [false,true,true,true,true,false,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true]) (.lit [false,false,false,false,false,true,true,true,false]) 2,
    .steps 66,
    .right [true] [true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true] [true,true] [true,true] false (.lit [false,true,true,false,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true]) (.lit [false,false,false,false,false,true,true,true,false]) 2,
    .steps 48,
    .left [true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true] [] [true,true] [true,true] false (.lit [false,true,true,false,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true]) (.lit [false,true,true,true,false,true,true,true,false]) 2,
    .steps 155,
    .right [true] [true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true] [true,true] [true,true] false (.lit [false,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,false,true,true,true,true]) (.lit [false,true,true,true,false,true,true,true,false]) 2,
    .steps 39,
    .left [true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true] [] [true,true] [true,true] false (.lit [false,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,false,true,true,true,true]) (.lit [false,false,true,true,false,true,true,true,false]) 2,
    .steps 39,
    .right [true] [true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true] [true,true] [true,true] false (.lit [false,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,false,true,true,true,true]) (.lit [false,false,true,true,false,true,true,true,false]) 2,
    .steps 47,
    .left [true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true] [] [true,true] [true,true] false (.lit [false,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,false,true,true,true,true]) (.lit [false,true,false,false,true,true,false]) 2,
    .steps 39,
    .right [true] [true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true] [true,true] [true,true] false (.lit [false,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,false,true,true,true,true]) (.lit [false,true,false,false,true,true,false]) 2,
    .steps 37,
    .left [true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true] [] [true,true] [true,true] false (.lit [false,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,false,true,true,true,true]) (.lit [false,false,false,false,true,true,false]) 2,
    .steps 37,
    .right [true] [true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true] [true,true] [true,true] false (.lit [false,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,false,true,true,true,true]) (.lit [false,false,false,false,true,true,false]) 2,
    .steps 41,
    .left [true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true] [] [true,true] [true,true] false (.lit [false,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,false,true,true,true,true]) (.lit [false,true,true,true,true,true,false]) 2,
    .steps 35,
    .right [true] [true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true] [true,true] [true,true] false (.lit [false,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,false,true,true,true,true]) (.lit [false,true,true,true,true,true,false]) 2,
    .steps 33,
    .left [true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true] [] [true,true] [true,true] false (.lit [false,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,false,true,true,true,true]) (.lit [false,false,true,true,true,true,false]) 2,
    .steps 33,
    .right [true] [true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true] [true,true] [true,true] false (.lit [false,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,false,true,true,true,true]) (.lit [false,false,true,true,true,true,false]) 2,
    .steps 39
  ],60,0,1772⟩
theorem checkedJ4 : check table certJ4 = true := by decide +kernel

theorem stepJ4 (n m : Nat) :
    run0 table (60*n+0*0+1772) (J 1 n) = some (J (n+14) 0) := by
  have hh := check_sound table certJ4 checkedJ4 n 0
  rw [← PZ.norm_sound certJ4.source n 0, ← PZ.norm_sound certJ4.target n 0] at hh
  change run0 table (60*n+0*0+1772) (PZ.eval ⟨5,(.periodic [false,false,true,true,true,false,true,true,true,true,false] [true,true] false (.lit [true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,false,true,true,true,true])),(.lit [])⟩ n 0) = some (PZ.eval ⟨5,(.periodic [false,false,true,true,true,false] [true,true] false (.lit [true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,false,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,false,true,true,true,true])),(.lit [])⟩ n 0) at hh
  simpa only [H,J,pair,PZ.eval,Word.eval,Bool.false_eq_true,ite_false,ite_true,← Auto.rep_add,rep_num_0,rep_num_1,rep_num_2,rep_num_3,rep_num_4,rep_num_5,rep_num_6,rep_num_7,rep_num_11,rep_num_14,rep_num_16,rep_num_17,List.append_assoc,List.cons_append,List.nil_append,Nat.zero_mul,Nat.zero_add,Nat.add_zero] using hh

def certJ6 : Cert := ⟨⟨5,(.periodic [false,false,true,true,true,false,true,true,true,true,true,true,false,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true] [true,true] false (.lit [true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,false,true,true,true,true])),(.lit [])⟩,⟨5,(.periodic [false,false,true,true,true,false,true,true,true,true,true,true,true,true,true,true,true,true] [true,true] false (.lit [true,true,true,true,true,true,true,true,true,true,true,true,false,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,false,true,true,true,true])),(.lit [])⟩,[
    .steps 78,
    .left [true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true] [] [true,true] [true,true] false (.lit [true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,false,true,true,true,true]) (.lit [true,true,true,true,false]) 2,
    .steps 46,
    .right [true] [true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true] [true,true] [true,true] false (.lit [false,true,true,true,true,true,true]) (.lit [true,true,true,true,false]) 2,
    .steps 54,
    .left [true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true] [] [true,true] [true,true] false (.lit [false,true,true,true,true,true,true]) (.lit [false,true,true,true,false]) 2,
    .steps 78,
    .right [true] [true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true] [true,true] [true,true] false (.lit [false,true,true,true,true,false,true,true,true,true]) (.lit [false,true,true,true,false]) 2,
    .steps 46,
    .left [true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true] [] [true,true] [true,true] false (.lit [false,true,true,true,true,false,true,true,true,true]) (.lit [false,false,true,true,false]) 2,
    .steps 68,
    .right [true] [true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true] [true,true] [true,true] false (.lit [false,true,true,false,true,true,true,true,true,true,true,true]) (.lit [false,false,true,true,false]) 2,
    .steps 60,
    .left [true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true] [] [true,true] [true,true] false (.lit [false,true,true,false,true,true,true,true,true,true,true,true]) (.lit [false,true,false,true,true,true,false]) 2,
    .steps 111,
    .right [true] [true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true] [true,true] [true,true] false (.lit [false,true,true,true,true,true,true,true,true,true,true,false,true,true,true,true]) (.lit [false,true,false,true,true,true,false]) 2,
    .steps 43,
    .left [true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true] [] [true,true] [true,true] false (.lit [false,true,true,true,true,true,true,true,true,true,true,false,true,true,true,true]) (.lit [false,false,false,true,true,true,false]) 2,
    .steps 43,
    .right [true] [true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true] [true,true] [true,true] false (.lit [false,true,true,true,true,true,true,true,true,true,true,true,true,false,true,true,true,true]) (.lit [false,false,false,true,true,true,false]) 2,
    .steps 59,
    .left [true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true] [] [true,true] [true,true] false (.lit [false,true,true,true,true,true,true,true,true,true,true,true,true,false,true,true,true,true]) (.lit [false,true,true,true,false,true,false,true,true,true,false]) 2,
    .steps 41,
    .right [true] [true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true] [true,true] [true,true] false (.lit [false,true,true,true,true,true,true,true,true,true,true,true,true,true,true,false,true,true,true,true]) (.lit [false,true,true,true,false,true,false,true,true,true,false]) 2,
    .steps 39,
    .left [true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true] [] [true,true] [true,true] false (.lit [false,true,true,true,true,true,true,true,true,true,true,true,true,true,true,false,true,true,true,true]) (.lit [false,false,true,true,false,true,false,true,true,true,false]) 2,
    .steps 39,
    .right [true] [true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true] [true,true] [true,true] false (.lit [false,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,false,true,true,true,true]) (.lit [false,false,true,true,false,true,false,true,true,true,false]) 2,
    .steps 47,
    .left [true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true] [] [true,true] [true,true] false (.lit [false,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,false,true,true,true,true]) (.lit [false,true,false,false,false,true,true,true,false]) 2,
    .steps 39,
    .right [true] [true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true] [true,true] [true,true] false (.lit [false,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,false,true,true,true,true]) (.lit [false,true,false,false,false,true,true,true,false]) 2,
    .steps 37,
    .left [true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true] [] [true,true] [true,true] false (.lit [false,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,false,true,true,true,true]) (.lit [false,false,false,false,false,true,true,true,false]) 2,
    .steps 37,
    .right [true] [true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true] [true,true] [true,true] false (.lit [false,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,false,true,true,true,true]) (.lit [false,false,false,false,false,true,true,true,false]) 2,
    .steps 41,
    .left [true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true] [] [true,true] [true,true] false (.lit [false,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,false,true,true,true,true]) (.lit [false,true,true,true,false,true,true,true,false]) 2,
    .steps 35,
    .right [true] [true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true] [true,true] [true,true] false (.lit [false,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,false,true,true,true,true]) (.lit [false,true,true,true,false,true,true,true,false]) 2,
    .steps 33,
    .left [true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true] [] [true,true] [true,true] false (.lit [false,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,false,true,true,true,true]) (.lit [false,false,true,true,false,true,true,true,false]) 2,
    .steps 33,
    .right [true] [true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true] [true,true] [true,true] false (.lit [false,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,false,true,true,true,true]) (.lit [false,false,true,true,false,true,true,true,false]) 2,
    .steps 41,
    .left [true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true] [] [true,true] [true,true] false (.lit [false,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,false,true,true,true,true]) (.lit [false,true,false,false,true,true,false]) 2,
    .steps 33,
    .right [true] [true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true] [true,true] [true,true] false (.lit [false,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,false,true,true,true,true]) (.lit [false,true,false,false,true,true,false]) 2,
    .steps 31,
    .left [true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true] [] [true,true] [true,true] false (.lit [false,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,false,true,true,true,true]) (.lit [false,false,false,false,true,true,false]) 2,
    .steps 31,
    .right [true] [true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true] [true,true] [true,true] false (.lit [false,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,false,true,true,true,true]) (.lit [false,false,false,false,true,true,false]) 2,
    .steps 35,
    .left [true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true] [] [true,true] [true,true] false (.lit [false,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,false,true,true,true,true]) (.lit [false,true,true,true,true,true,false]) 2,
    .steps 29,
    .right [true] [true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true] [true,true] [true,true] false (.lit [false,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,false,true,true,true,true]) (.lit [false,true,true,true,true,true,false]) 2,
    .steps 27,
    .left [true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true] [] [true,true] [true,true] false (.lit [false,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,false,true,true,true,true]) (.lit [false,false,true,true,true,true,false]) 2,
    .steps 27,
    .right [true] [true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true] [true,true] [true,true] false (.lit [false,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,false,true,true,true,true]) (.lit [false,false,true,true,true,true,false]) 2,
    .steps 33
  ],60,0,1394⟩
theorem checkedJ6 : check table certJ6 = true := by decide +kernel

theorem stepJ6 (n m : Nat) :
    run0 table (60*n+0*0+1394) (J 2 n) = some (J (n+11) 0) := by
  have hh := check_sound table certJ6 checkedJ6 n 0
  rw [← PZ.norm_sound certJ6.source n 0, ← PZ.norm_sound certJ6.target n 0] at hh
  change run0 table (60*n+0*0+1394) (PZ.eval ⟨5,(.periodic [false,false,true,true,true,false,true,true,true,true,true,true,false] [true,true] false (.lit [true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,false,true,true,true,true])),(.lit [])⟩ n 0) = some (PZ.eval ⟨5,(.periodic [false,false,true,true,true,false] [true,true] false (.lit [true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,false,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,false,true,true,true,true])),(.lit [])⟩ n 0) at hh
  simpa only [H,J,pair,PZ.eval,Word.eval,Bool.false_eq_true,ite_false,ite_true,← Auto.rep_add,rep_num_0,rep_num_1,rep_num_2,rep_num_3,rep_num_4,rep_num_5,rep_num_6,rep_num_7,rep_num_11,rep_num_14,rep_num_16,rep_num_17,List.append_assoc,List.cons_append,List.nil_append,Nat.zero_mul,Nat.zero_add,Nat.add_zero] using hh

def certJ8 : Cert := ⟨⟨5,(.periodic [false,false,true,true,true,false,true,true,true,true,true,true,true,true,false,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true] [true,true] false (.lit [true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,false,true,true,true,true])),(.lit [])⟩,⟨5,(.periodic [false,false,false,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true] [true,true] false (.lit [true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,false,true,true,true,true,true,true,true,true,true,true,true,true])),(.lit [])⟩,[
    .steps 103,
    .left [true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true] [] [true,true] [true,true] false (.lit [true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,false,true,true,true,true]) (.lit [false,true,true,true,true,false]) 2,
    .steps 47,
    .right [true] [true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true] [true,true] [true,true] false (.lit [false,true,true,true,true,true,true]) (.lit [false,true,true,true,true,false]) 2,
    .steps 45,
    .left [true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true] [] [true,true] [true,true] false (.lit [false,true,true,true,true,true,true]) (.lit [false,false,true,true,true,false]) 2,
    .steps 45,
    .right [true] [true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true] [true,true] [true,true] false (.lit [false,true,true,true,true,true,true,true,true]) (.lit [false,false,true,true,true,false]) 2,
    .steps 69,
    .left [true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true] [] [true,true] [true,true] false (.lit [false,true,true,true,true,true,true,true,true]) (.lit [false,true,true,false]) 2,
    .steps 49,
    .right [true] [true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true] [true,true] [true,true] false (.lit [false,true,true,true,true,true,true,true,true,true,true]) (.lit [false,true,true,false]) 2,
    .steps 47,
    .left [true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true] [] [true,true] [true,true] false (.lit [false,true,true,true,true,true,true,true,true,true,true]) (.lit [false,false,true,false]) 2,
    .steps 47,
    .right [true] [true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true] [true,true] [true,true] false (.lit [false,true,true,true,true,true,true,true,true,true,true,true,true]) (.lit [false,false,true,false]) 2,
    .steps 50
  ],16,0,502⟩
theorem checkedJ8 : check table certJ8 = true := by decide +kernel

theorem stepJ8 (n m : Nat) :
    run0 table (16*n+0*0+502) (J 3 n) = some (H (n+5)) := by
  have hh := check_sound table certJ8 checkedJ8 n 0
  rw [← PZ.norm_sound certJ8.source n 0, ← PZ.norm_sound certJ8.target n 0] at hh
  change run0 table (16*n+0*0+502) (PZ.eval ⟨5,(.periodic [false,false,true,true,true,false,true,true,true,true,true,true,true,true,false] [true,true] false (.lit [true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,false,true,true,true,true])),(.lit [])⟩ n 0) = some (PZ.eval ⟨5,(.periodic [false,false,false] [true,true] false (.lit [true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,false,true,true,true,true,true,true,true,true,true,true,true,true])),(.lit [])⟩ n 0) at hh
  simpa only [H,J,pair,PZ.eval,Word.eval,Bool.false_eq_true,ite_false,ite_true,← Auto.rep_add,rep_num_0,rep_num_1,rep_num_2,rep_num_3,rep_num_4,rep_num_5,rep_num_6,rep_num_7,rep_num_11,rep_num_14,rep_num_16,rep_num_17,List.append_assoc,List.cons_append,List.nil_append,Nat.zero_mul,Nat.zero_add,Nat.add_zero] using hh

def certJ10 : Cert := ⟨⟨5,(.periodic [false,false,true,true,true,false,true,true,true,true,true,true,true,true,true,true,false,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true] [true,true] false (.lit [true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,false,true,true,true,true])),(.lit [])⟩,⟨5,(.periodic [false,false,true,true,true,false,true,true,false,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true] [true,true] false (.lit [true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,false,true,true,true,true])),(.lit [])⟩,[
    .steps 136
  ],0,0,136⟩
theorem checkedJ10 : check table certJ10 = true := by decide +kernel

theorem stepJ10 (n m : Nat) :
    run0 table (0*n+0*0+136) (J 4 n) = some (J 0 (n+6)) := by
  have hh := check_sound table certJ10 checkedJ10 n 0
  rw [← PZ.norm_sound certJ10.source n 0, ← PZ.norm_sound certJ10.target n 0] at hh
  change run0 table (0*n+0*0+136) (PZ.eval ⟨5,(.periodic [false,false,true,true,true,false,true,true,true,true,true,true,true,true,true,true,false] [true,true] false (.lit [true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,false,true,true,true,true])),(.lit [])⟩ n 0) = some (PZ.eval ⟨5,(.periodic [false,false,true,true,true,false,true,true,false] [true,true] false (.lit [true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,false,true,true,true,true])),(.lit [])⟩ n 0) at hh
  simpa only [H,J,pair,PZ.eval,Word.eval,Bool.false_eq_true,ite_false,ite_true,← Auto.rep_add,rep_num_0,rep_num_1,rep_num_2,rep_num_3,rep_num_4,rep_num_5,rep_num_6,rep_num_7,rep_num_11,rep_num_14,rep_num_16,rep_num_17,List.append_assoc,List.cons_append,List.nil_append,Nat.zero_mul,Nat.zero_add,Nat.add_zero] using hh

def region (z : Z0) : Prop := (∃ n, z = H n) ∨ (∃ x y, z = J x y)

theorem closed (z : Z0) (hz : region z) :
    ∃ k t, 0 < k ∧ region t ∧ run0 table k z = some t := by
  rcases hz with ⟨n,rfl⟩ | ⟨x,y,rfl⟩
  · exact ⟨_,_,by omega,Or.inr ⟨n+7,4,rfl⟩,stepH n 0⟩
  · rcases x with _|x
    · exact ⟨_,_,by omega,Or.inl ⟨y,rfl⟩,stepJ2 y 0⟩
    rcases x with _|x
    · exact ⟨_,_,by omega,Or.inr ⟨y+14,0,rfl⟩,stepJ4 y 0⟩
    rcases x with _|x
    · exact ⟨_,_,by omega,Or.inr ⟨y+11,0,rfl⟩,stepJ6 y 0⟩
    rcases x with _|x
    · exact ⟨_,_,by omega,Or.inl ⟨y+5,rfl⟩,stepJ8 y 0⟩
    rcases x with _|x
    · exact ⟨_,_,by omega,Or.inr ⟨0,y+6,rfl⟩,stepJ10 y 0⟩
    exact ⟨_,_,by omega,Or.inr ⟨x+1,y+6,rfl⟩,stepJ x y⟩

theorem seed : run0 table 2157 ⟨0,[],[]⟩ = some (H 5) := by decide +kernel

theorem never (m : Machine) (hm : compatible table m) : NeverHalts m :=
  never_of_region table region 2157 (H 5) seed (Or.inl ⟨5,rfl⟩) closed m hm

theorem cover (B : Nat) : Cover (WeightedBound B) table :=
  .leaf _ fun m hm => weighted_never B m (never m hm)

#print axioms closed
#print axioms never
#print axioms cover
end BB6Coverage.Agent31Pump.Multi.Raw11Q0Counter138
