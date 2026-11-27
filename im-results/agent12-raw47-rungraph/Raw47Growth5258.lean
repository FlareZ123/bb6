import SweepPumping
import FAR
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace BB6.Agent12Raw47Growth5258
open BB6Coverage BB6Coverage.Agent31Pump

def ctr : PartialMachine := fun s => match s.1.val,s.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 1,true => some (some ⟨false,false,5⟩)
  | 2,false => some (some ⟨false,true,3⟩)
  | 2,true => some (some ⟨false,false,4⟩)
  | 3,false => some (some ⟨true,false,3⟩)
  | 3,true => some (some ⟨false,true,2⟩)
  | 4,false => some (some ⟨true,true,0⟩)
  | 4,true => some (some ⟨false,true,4⟩)
  | 5,false => some (some ⟨false,false,4⟩)
  | 5,true => some (some ⟨true,false,1⟩)
  | _,_ => none

-- Start at the second observed return (time 1038), leaving fixed framing blocks.
def cfg (n : Nat) : Z0 := ⟨0,[false,true,false],[true,false,false,false,false] ++ rep [true,false,false,false,false,false,true,false,false,false,false,false] n ++ [true,false,false,false,false,false,true,false,false,false,false,false,true,false,false,false,true,false]⟩

theorem entry : run0 ctr 1038 ⟨0,[],[]⟩ = some (cfg 0) := rfl

theorem phase0 (n : Nat) : run0 ctr 93 ⟨0,[false,true,false],[true,false,false,false,false] ++ rep [true,false,false,false,false,false,true,false,false,false,false,false] n ++ [true,false,false,false,false,false,true,false,false,false,false,false,true,false,false,false,true,false]⟩ = some ⟨0,[false,true,false,false,false,true,true,true,false,true,true],[] ++ rep [true,false,false,false,false,false,true,false,false,false,false,false] n ++ [true,false,false,false,false,false,true,false,false,false,false,false,true,false,false,false,true,false]⟩ := rfl

theorem phase1 (n : Nat) : run0 ctr 0 ⟨0,[false,true,false,false,false,true,true,true,false,true,true],[] ++ rep [true,false,false,false,false,false,true,false,false,false,false,false] n ++ [true,false,false,false,false,false,true,false,false,false,false,false,true,false,false,false,true,false]⟩ = some ⟨0,[false,true,false,false,false,true,true,true,false,true,true],[true] ++ rep [false,false,false,false,false,true,false,false,false,false,false,true] n ++ [false,false,false,false,false,true,false,false,false,false,false,true,false,false,false,true,false]⟩ := by
  have h := moveCut [] [false,false,false,false,false,true,false,false,false,false,false,true,false,false,false,true,false] [false,false,false,false,false,true,false,false,false,false,false] true n
  have h' := congrArg (fun w => (⟨0,[false,true,false,false,false,true,true,true,false,true,true],w⟩ : Z0)) h.symm
  simpa only [run0,List.append_assoc,List.cons_append,List.nil_append] using congrArg some h'

theorem phase2 (n : Nat) : run0 ctr 11 ⟨0,[false,true,false,false,false,true,true,true,false,true,true],[true] ++ rep [false,false,false,false,false,true,false,false,false,false,false,true] n ++ [false,false,false,false,false,true,false,false,false,false,false,true,false,false,false,true,false]⟩ = some ⟨0,[false,true,false,true,true,false,true,true,true,false,true,true],[] ++ rep [false,false,false,false,false,true,false,false,false,false,false,true] n ++ [false,false,false,false,false,true,false,false,false,false,false,true,false,false,false,true,false]⟩ := rfl

theorem phase3 (n : Nat) : run0 ctr 0 ⟨0,[false,true,false,true,true,false,true,true,true,false,true,true],[] ++ rep [false,false,false,false,false,true,false,false,false,false,false,true] n ++ [false,false,false,false,false,true,false,false,false,false,false,true,false,false,false,true,false]⟩ = some ⟨0,[false,true,false,true,true,false,true,true,true,false,true,true],[false] ++ rep [false,false,false,false,true,false,false,false,false,false,true,false] n ++ [false,false,false,false,true,false,false,false,false,false,true,false,false,false,true,false]⟩ := by
  have h := moveCut [] [false,false,false,false,true,false,false,false,false,false,true,false,false,false,true,false] [false,false,false,false,true,false,false,false,false,false,true] false n
  have h' := congrArg (fun w => (⟨0,[false,true,false,true,true,false,true,true,true,false,true,true],w⟩ : Z0)) h.symm
  simpa only [run0,List.append_assoc,List.cons_append,List.nil_append] using congrArg some h'

theorem phase4 (n : Nat) : run0 ctr 1 ⟨0,[false,true,false,true,true,false,true,true,true,false,true,true],[false] ++ rep [false,false,false,false,true,false,false,false,false,false,true,false] n ++ [false,false,false,false,true,false,false,false,false,false,true,false,false,false,true,false]⟩ = some ⟨1,[false,true,true,false,true,true,false,true,true,true,false,true,true],[] ++ rep [false,false,false,false,true,false,false,false,false,false,true,false] n ++ [false,false,false,false,true,false,false,false,false,false,true,false,false,false,true,false]⟩ := rfl

theorem phase5 (n : Nat) : run0 ctr 0 ⟨1,[false,true,true,false,true,true,false,true,true,true,false,true,true],[] ++ rep [false,false,false,false,true,false,false,false,false,false,true,false] n ++ [false,false,false,false,true,false,false,false,false,false,true,false,false,false,true,false]⟩ = some ⟨1,[false,true,true,false,true,true,false,true,true,true,false,true,true],[false] ++ rep [false,false,false,true,false,false,false,false,false,true,false,false] n ++ [false,false,false,true,false,false,false,false,false,true,false,false,false,true,false]⟩ := by
  have h := moveCut [] [false,false,false,true,false,false,false,false,false,true,false,false,false,true,false] [false,false,false,true,false,false,false,false,false,true,false] false n
  have h' := congrArg (fun w => (⟨1,[false,true,true,false,true,true,false,true,true,true,false,true,true],w⟩ : Z0)) h.symm
  simpa only [run0,List.append_assoc,List.cons_append,List.nil_append] using congrArg some h'

theorem phase6 (n : Nat) : run0 ctr 1 ⟨1,[false,true,true,false,true,true,false,true,true,true,false,true,true],[false] ++ rep [false,false,false,true,false,false,false,false,false,true,false,false] n ++ [false,false,false,true,false,false,false,false,false,true,false,false,false,true,false]⟩ = some ⟨2,[false,true,true,true,false,true,true,false,true,true,true,false,true,true],[] ++ rep [false,false,false,true,false,false,false,false,false,true,false,false] n ++ [false,false,false,true,false,false,false,false,false,true,false,false,false,true,false]⟩ := rfl

theorem phase7 (n : Nat) : run0 ctr 0 ⟨2,[false,true,true,true,false,true,true,false,true,true,true,false,true,true],[] ++ rep [false,false,false,true,false,false,false,false,false,true,false,false] n ++ [false,false,false,true,false,false,false,false,false,true,false,false,false,true,false]⟩ = some ⟨2,[false,true,true,true,false,true,true,false,true,true,true,false,true,true],[false] ++ rep [false,false,true,false,false,false,false,false,true,false,false,false] n ++ [false,false,true,false,false,false,false,false,true,false,false,false,true,false]⟩ := by
  have h := moveCut [] [false,false,true,false,false,false,false,false,true,false,false,false,true,false] [false,false,true,false,false,false,false,false,true,false,false] false n
  have h' := congrArg (fun w => (⟨2,[false,true,true,true,false,true,true,false,true,true,true,false,true,true],w⟩ : Z0)) h.symm
  simpa only [run0,List.append_assoc,List.cons_append,List.nil_append] using congrArg some h'

theorem phase8 (n : Nat) : run0 ctr 37 ⟨2,[false,true,true,true,false,true,true,false,true,true,true,false,true,true],[false] ++ rep [false,false,true,false,false,false,false,false,true,false,false,false] n ++ [false,false,true,false,false,false,false,false,true,false,false,false,true,false]⟩ = some ⟨2,[false,false,false,true,true,true,false,true,true,true,true,true,false,true,true],[] ++ rep [false,false,true,false,false,false,false,false,true,false,false,false] n ++ [false,false,true,false,false,false,false,false,true,false,false,false,true,false]⟩ := rfl

theorem phase9 (n : Nat) : run0 ctr 0 ⟨2,[false,false,false,true,true,true,false,true,true,true,true,true,false,true,true],[] ++ rep [false,false,true,false,false,false,false,false,true,false,false,false] n ++ [false,false,true,false,false,false,false,false,true,false,false,false,true,false]⟩ = some ⟨2,[false,false,false,true,true,true,false,true,true,true,true,true,false,true,true],[false] ++ rep [false,true,false,false,false,false,false,true,false,false,false,false] n ++ [false,true,false,false,false,false,false,true,false,false,false,true,false]⟩ := by
  have h := moveCut [] [false,true,false,false,false,false,false,true,false,false,false,true,false] [false,true,false,false,false,false,false,true,false,false,false] false n
  have h' := congrArg (fun w => (⟨2,[false,false,false,true,true,true,false,true,true,true,true,true,false,true,true],w⟩ : Z0)) h.symm
  simpa only [run0,List.append_assoc,List.cons_append,List.nil_append] using congrArg some h'

theorem phase10 (n : Nat) : run0 ctr 200 ⟨2,[false,false,false,true,true,true,false,true,true,true,true,true,false,true,true],[false] ++ rep [false,true,false,false,false,false,false,true,false,false,false,false] n ++ [false,true,false,false,false,false,false,true,false,false,false,true,false]⟩ = some ⟨2,[false,true,true,true,false,true,true,false,true,true,true,false,true,true],[false,true,false,true,true] ++ rep [false,true,false,false,false,false,false,true,false,false,false,false] n ++ [false,true,false,false,false,false,false,true,false,false,false,true,false]⟩ := rfl

theorem phase11 (n : Nat) : run0 ctr 43 ⟨2,[false,true,true,true,false,true,true,false,true,true,true,false,true,true],[false,true,false,true,true] ++ rep [false,true,false,false,false,false,false,true,false,false,false,false] n ++ [false,true,false,false,false,false,false,true,false,false,false,true,false]⟩ = some ⟨0,[false,true,false,false,false,false,false,true,true,true,false,true,true,true,true,true,false,true,true],[] ++ rep [false,true,false,false,false,false,false,true,false,false,false,false] n ++ [false,true,false,false,false,false,false,true,false,false,false,true,false]⟩ := rfl

-- One framed transfer has cost 380; induction repeats it n times.
theorem phase12 (n : Nat) : run0 ctr (380*n) ⟨0,[false,true,false,false,false,false,false,true,true,true,false,true,true,true,true,true,false,true,true],[] ++ rep [false,true,false,false,false,false,false,true,false,false,false,false] n ++ [false,true,false,false,false,false,false,true,false,false,false,true,false]⟩ = some ⟨0,[false,true,false,false,false,false,false] ++ rep [true,true,true,false,true,true,true,true,true,false,true,true] n ++ [true,true,true,false,true,true,true,true,true,false,true,true],[false,true,false,false,false,false,false,true,false,false,false,true,false]⟩ := by
  simpa only [List.append_assoc,List.cons_append,List.nil_append] using
    sweepR ctr 0 [false,true,false,false,false,false,false] [] [false,true,false,false,false,false,false,true,false,false,false,false] [true,true,true,false,true,true,true,true,true,false,true,true] 380 (by intro L R; rfl) n [true,true,true,false,true,true,true,true,true,false,true,true] [false,true,false,false,false,false,false,true,false,false,false,true,false]

theorem phase13 (n : Nat) : run0 ctr 200 ⟨0,[false,true,false,false,false,false,false] ++ rep [true,true,true,false,true,true,true,true,true,false,true,true] n ++ [true,true,true,false,true,true,true,true,true,false,true,true],[false,true,false,false,false,false,false,true,false,false,false,true,false]⟩ = some ⟨3,[false,false,true,true,true,false,true,true,true,true,false,false,false] ++ rep [true,true,true,false,true,true,true,true,true,false,true,true] n ++ [true,true,true,false,true,true,true,true,true,false,true,true],[false,false,true,false,true,true,true,true]⟩ := rfl

theorem phase14 (n : Nat) : run0 ctr 200 ⟨3,[false,false,true,true,true,false,true,true,true,true,false,false,false] ++ rep [true,true,true,false,true,true,true,true,true,false,true,true] n ++ [true,true,true,false,true,true,true,true,true,false,true,true],[false,false,true,false,true,true,true,true]⟩ = some ⟨4,[true,true,false,false,false,true,true,true,false,true,true,true,true,true,false,true,true] ++ rep [true,true,true,false,true,true,true,true,true,false,true,true] n ++ [true,true,true,false,true,true,true,true,true,false,true,true],[false,false,true,false]⟩ := rfl

theorem phase15 (n : Nat) : run0 ctr 200 ⟨4,[true,true,false,false,false,true,true,true,false,true,true,true,true,true,false,true,true] ++ rep [true,true,true,false,true,true,true,true,true,false,true,true] n ++ [true,true,true,false,true,true,true,true,true,false,true,true],[false,false,true,false]⟩ = some ⟨1,[false,true,true,true,true,true,true,true,false,true,true,true,true,true,false,true,true] ++ rep [true,true,true,false,true,true,true,true,true,false,true,true] n ++ [true,true,true,false,true,true,true,true,true,false,true,true],[true,false,false,false,false,false,false,true,false]⟩ := rfl

theorem phase16 (n : Nat) : run0 ctr 187 ⟨1,[false,true,true,true,true,true,true,true,false,true,true,true,true,true,false,true,true] ++ rep [true,true,true,false,true,true,true,true,true,false,true,true] n ++ [true,true,true,false,true,true,true,true,true,false,true,true],[true,false,false,false,false,false,false,true,false]⟩ = some ⟨4,[] ++ rep [true,true,true,false,true,true,true,true,true,false,true,true] n ++ [true,true,true,false,true,true,true,true,true,false,true,true],[false,false,true,false,false,false,false,false,true,false,false,false,false,false,true,false,false,false,false,false,true,false,false,false,true,false]⟩ := rfl

-- One framed transfer has cost 140; induction repeats it n times.
theorem phase17 (n : Nat) : run0 ctr (140*n) ⟨4,[] ++ rep [true,true,true,false,true,true,true,true,true,false,true,true] n ++ [true,true,true,false,true,true,true,true,true,false,true,true],[false,false,true,false,false,false,false,false,true,false,false,false,false,false,true,false,false,false,false,false,true,false,false,false,true,false]⟩ = some ⟨4,[true,true,true,false,true,true,true,true,true,false,true,true],[false,false,true,false] ++ rep [false,false,false,false,true,false,false,false,false,false,true,false] n ++ [false,false,false,false,true,false,false,false,false,false,true,false,false,false,false,false,true,false,false,false,true,false]⟩ := by
  simpa only [List.append_assoc,List.cons_append,List.nil_append] using
    sweepL ctr 4 [] [false,false,true,false] [true,true,true,false,true,true,true,true,true,false,true,true] [false,false,false,false,true,false,false,false,false,false,true,false] 140 (by intro L R; rfl) n [true,true,true,false,true,true,true,true,true,false,true,true] [false,false,false,false,true,false,false,false,false,false,true,false,false,false,false,false,true,false,false,false,true,false]

theorem phase18 (n : Nat) : run0 ctr 135 ⟨4,[true,true,true,false,true,true,true,true,true,false,true,true],[false,false,true,false] ++ rep [false,false,false,false,true,false,false,false,false,false,true,false] n ++ [false,false,false,false,true,false,false,false,false,false,true,false,false,false,false,false,true,false,false,false,true,false]⟩ = some ⟨0,[false,true,false],[true,false,false,false,false,true,false,false,false,false,false,true,false] ++ rep [false,false,false,false,true,false,false,false,false,false,true,false] n ++ [false,false,false,false,true,false,false,false,false,false,true,false,false,false,false,false,true,false,false,false,true,false]⟩ := rfl

theorem phase19 (n : Nat) : run0 ctr 0 ⟨0,[false,true,false],[true,false,false,false,false,true,false,false,false,false,false,true,false] ++ rep [false,false,false,false,true,false,false,false,false,false,true,false] n ++ [false,false,false,false,true,false,false,false,false,false,true,false,false,false,false,false,true,false,false,false,true,false]⟩ = some ⟨0,[false,true,false],[true,false,false,false,false,true,false,false,false,false,false,true] ++ rep [false,false,false,false,false,true,false,false,false,false,false,true] n ++ [false,false,false,false,false,true,false,false,false,false,false,true,false,false,false,false,false,true,false,false,false,true,false]⟩ := by
  have h := moveCut [true,false,false,false,false,true,false,false,false,false,false,true] [false,false,false,false,true,false,false,false,false,false,true,false,false,false,false,false,true,false,false,false,true,false] [false,false,false,false,true,false,false,false,false,false,true] false n
  have h' := congrArg (fun w => (⟨0,[false,true,false],w⟩ : Z0)) h
  simpa only [run0,List.append_assoc,List.cons_append,List.nil_append] using congrArg some h'

theorem phase20 (n : Nat) : run0 ctr 0 ⟨0,[false,true,false],[true,false,false,false,false,true,false,false,false,false,false,true] ++ rep [false,false,false,false,false,true,false,false,false,false,false,true] n ++ [false,false,false,false,false,true,false,false,false,false,false,true,false,false,false,false,false,true,false,false,false,true,false]⟩ = some ⟨0,[false,true,false],[true,false,false,false,false,true,false,false,false,false,false] ++ rep [true,false,false,false,false,false,true,false,false,false,false,false] n ++ [true,false,false,false,false,false,true,false,false,false,false,false,true,false,false,false,false,false,true,false,false,false,true,false]⟩ := by
  have h := moveCut [true,false,false,false,false,true,false,false,false,false,false] [false,false,false,false,false,true,false,false,false,false,false,true,false,false,false,false,false,true,false,false,false,true,false] [false,false,false,false,false,true,false,false,false,false,false] true n
  have h' := congrArg (fun w => (⟨0,[false,true,false],w⟩ : Z0)) h
  simpa only [run0,List.append_assoc,List.cons_append,List.nil_append] using congrArg some h'

theorem phase21 (n : Nat) : run0 ctr 0 ⟨0,[false,true,false],[true,false,false,false,false,true,false,false,false,false,false] ++ rep [true,false,false,false,false,false,true,false,false,false,false,false] n ++ [true,false,false,false,false,false,true,false,false,false,false,false,true,false,false,false,false,false,true,false,false,false,true,false]⟩ = some ⟨0,[false,true,false],[true,false,false,false,false,true,false,false,false,false] ++ rep [false,true,false,false,false,false,false,true,false,false,false,false] n ++ [false,true,false,false,false,false,false,true,false,false,false,false,false,true,false,false,false,false,false,true,false,false,false,true,false]⟩ := by
  have h := moveCut [true,false,false,false,false,true,false,false,false,false] [true,false,false,false,false,false,true,false,false,false,false,false,true,false,false,false,false,false,true,false,false,false,true,false] [true,false,false,false,false,false,true,false,false,false,false] false n
  have h' := congrArg (fun w => (⟨0,[false,true,false],w⟩ : Z0)) h
  simpa only [run0,List.append_assoc,List.cons_append,List.nil_append] using congrArg some h'

theorem phase22 (n : Nat) : run0 ctr 0 ⟨0,[false,true,false],[true,false,false,false,false,true,false,false,false,false] ++ rep [false,true,false,false,false,false,false,true,false,false,false,false] n ++ [false,true,false,false,false,false,false,true,false,false,false,false,false,true,false,false,false,false,false,true,false,false,false,true,false]⟩ = some ⟨0,[false,true,false],[true,false,false,false,false,true,false,false,false] ++ rep [false,false,true,false,false,false,false,false,true,false,false,false] n ++ [false,false,true,false,false,false,false,false,true,false,false,false,false,false,true,false,false,false,false,false,true,false,false,false,true,false]⟩ := by
  have h := moveCut [true,false,false,false,false,true,false,false,false] [false,true,false,false,false,false,false,true,false,false,false,false,false,true,false,false,false,false,false,true,false,false,false,true,false] [false,true,false,false,false,false,false,true,false,false,false] false n
  have h' := congrArg (fun w => (⟨0,[false,true,false],w⟩ : Z0)) h
  simpa only [run0,List.append_assoc,List.cons_append,List.nil_append] using congrArg some h'

theorem phase23 (n : Nat) : run0 ctr 0 ⟨0,[false,true,false],[true,false,false,false,false,true,false,false,false] ++ rep [false,false,true,false,false,false,false,false,true,false,false,false] n ++ [false,false,true,false,false,false,false,false,true,false,false,false,false,false,true,false,false,false,false,false,true,false,false,false,true,false]⟩ = some ⟨0,[false,true,false],[true,false,false,false,false,true,false,false] ++ rep [false,false,false,true,false,false,false,false,false,true,false,false] n ++ [false,false,false,true,false,false,false,false,false,true,false,false,false,false,false,true,false,false,false,false,false,true,false,false,false,true,false]⟩ := by
  have h := moveCut [true,false,false,false,false,true,false,false] [false,false,true,false,false,false,false,false,true,false,false,false,false,false,true,false,false,false,false,false,true,false,false,false,true,false] [false,false,true,false,false,false,false,false,true,false,false] false n
  have h' := congrArg (fun w => (⟨0,[false,true,false],w⟩ : Z0)) h
  simpa only [run0,List.append_assoc,List.cons_append,List.nil_append] using congrArg some h'

theorem phase24 (n : Nat) : run0 ctr 0 ⟨0,[false,true,false],[true,false,false,false,false,true,false,false] ++ rep [false,false,false,true,false,false,false,false,false,true,false,false] n ++ [false,false,false,true,false,false,false,false,false,true,false,false,false,false,false,true,false,false,false,false,false,true,false,false,false,true,false]⟩ = some ⟨0,[false,true,false],[true,false,false,false,false,true,false] ++ rep [false,false,false,false,true,false,false,false,false,false,true,false] n ++ [false,false,false,false,true,false,false,false,false,false,true,false,false,false,false,false,true,false,false,false,false,false,true,false,false,false,true,false]⟩ := by
  have h := moveCut [true,false,false,false,false,true,false] [false,false,false,true,false,false,false,false,false,true,false,false,false,false,false,true,false,false,false,false,false,true,false,false,false,true,false] [false,false,false,true,false,false,false,false,false,true,false] false n
  have h' := congrArg (fun w => (⟨0,[false,true,false],w⟩ : Z0)) h
  simpa only [run0,List.append_assoc,List.cons_append,List.nil_append] using congrArg some h'

theorem phase25 (n : Nat) : run0 ctr 0 ⟨0,[false,true,false],[true,false,false,false,false,true,false] ++ rep [false,false,false,false,true,false,false,false,false,false,true,false] n ++ [false,false,false,false,true,false,false,false,false,false,true,false,false,false,false,false,true,false,false,false,false,false,true,false,false,false,true,false]⟩ = some ⟨0,[false,true,false],[true,false,false,false,false,true] ++ rep [false,false,false,false,false,true,false,false,false,false,false,true] n ++ [false,false,false,false,false,true,false,false,false,false,false,true,false,false,false,false,false,true,false,false,false,false,false,true,false,false,false,true,false]⟩ := by
  have h := moveCut [true,false,false,false,false,true] [false,false,false,false,true,false,false,false,false,false,true,false,false,false,false,false,true,false,false,false,false,false,true,false,false,false,true,false] [false,false,false,false,true,false,false,false,false,false,true] false n
  have h' := congrArg (fun w => (⟨0,[false,true,false],w⟩ : Z0)) h
  simpa only [run0,List.append_assoc,List.cons_append,List.nil_append] using congrArg some h'

theorem phase26 (n : Nat) : run0 ctr 0 ⟨0,[false,true,false],[true,false,false,false,false,true] ++ rep [false,false,false,false,false,true,false,false,false,false,false,true] n ++ [false,false,false,false,false,true,false,false,false,false,false,true,false,false,false,false,false,true,false,false,false,false,false,true,false,false,false,true,false]⟩ = some ⟨0,[false,true,false],[true,false,false,false,false] ++ rep [true,false,false,false,false,false,true,false,false,false,false,false] n ++ [true,false,false,false,false,false,true,false,false,false,false,false,true,false,false,false,false,false,true,false,false,false,false,false,true,false,false,false,true,false]⟩ := by
  have h := moveCut [true,false,false,false,false] [false,false,false,false,false,true,false,false,false,false,false,true,false,false,false,false,false,true,false,false,false,false,false,true,false,false,false,true,false] [false,false,false,false,false,true,false,false,false,false,false] true n
  have h' := congrArg (fun w => (⟨0,[false,true,false],w⟩ : Z0)) h
  simpa only [run0,List.append_assoc,List.cons_append,List.nil_append] using congrArg some h'

theorem growth (n : Nat) : run0 ctr (1308+520*n) (cfg n) = some (cfg (n+1)) := by
  have H0 := phase0 n
  have H1 := join0 H0 (phase1 n)
  have H2 := join0 H1 (phase2 n)
  have H3 := join0 H2 (phase3 n)
  have H4 := join0 H3 (phase4 n)
  have H5 := join0 H4 (phase5 n)
  have H6 := join0 H5 (phase6 n)
  have H7 := join0 H6 (phase7 n)
  have H8 := join0 H7 (phase8 n)
  have H9 := join0 H8 (phase9 n)
  have H10 := join0 H9 (phase10 n)
  have H11 := join0 H10 (phase11 n)
  have H12 := join0 H11 (phase12 n)
  have H13 := join0 H12 (phase13 n)
  have H14 := join0 H13 (phase14 n)
  have H15 := join0 H14 (phase15 n)
  have H16 := join0 H15 (phase16 n)
  have H17 := join0 H16 (phase17 n)
  have H18 := join0 H17 (phase18 n)
  have H19 := join0 H18 (phase19 n)
  have H20 := join0 H19 (phase20 n)
  have H21 := join0 H20 (phase21 n)
  have H22 := join0 H21 (phase22 n)
  have H23 := join0 H22 (phase23 n)
  have H24 := join0 H23 (phase24 n)
  have H25 := join0 H24 (phase25 n)
  have H26 := join0 H25 (phase26 n)
  rw [show 93+0+11+0+1+0+1+0+37+0+200+43+(380*n)+200+200+200+187+(140*n)+135+0+0+0+0+0+0+0+0=1308+520*n by omega] at H26
  simpa only [cfg,rep,List.append_assoc,List.cons_append,List.nil_append,← rep_snoc] using H26

theorem never (m : Machine) (hm : compatible ctr m) : NeverHalts m :=
  never_of_growth ctr cfg 1038 (fun n => 1308+520*n) entry (by intro n; omega) growth m hm

#print axioms growth
#print axioms never
end BB6.Agent12Raw47Growth5258
