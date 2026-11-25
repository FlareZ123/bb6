import SweepPumping
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedVariables false
namespace BB6.Agent11Raw39B0REPumps
open BB6Coverage BB6Coverage.Agent31Pump


namespace M325

-- 1RB0RE_1RC0RB_0RD0LA_1LD0RA_1RF0RC_---0LB

def table : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 0,true => some (some ⟨false,true,4⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 1,true => some (some ⟨false,true,1⟩)
  | 2,false => some (some ⟨false,true,3⟩)
  | 2,true => some (some ⟨false,false,0⟩)
  | 3,false => some (some ⟨true,false,3⟩)
  | 3,true => some (some ⟨false,true,0⟩)
  | 4,false => some (some ⟨true,true,5⟩)
  | 4,true => some (some ⟨false,true,2⟩)
  | 5,true => some (some ⟨false,false,1⟩)
  | _,_ => none

def family (n : Nat) : Z0 := ⟨2,([false,true]) ++ (rep [false,false] (n)) ++ ([true]) ++ (rep [false,false] (n)),[]⟩

theorem entry : run0 table 2 ⟨0,[],[]⟩ = some (family 0) := by rfl

theorem phase0 (n : Nat) : run0 table 7 ⟨2,([false,true]) ++ (rep [false,false] (n)) ++ ([true]) ++ (rep [false,false] (n)),[]⟩ = some ⟨3,([false,false,false,false,false]) ++ (rep [false,false] (n)) ++ ([true]) ++ (rep [false,false] (n)),[]⟩ := by rfl

theorem local1 (L R : List Bool) : run0 table 2 ⟨3,([false,false,false,false,false]) ++ ([false,false]) ++ (L),(R)⟩ = some ⟨3,([false,false,false,false,false]) ++ (L),([true,true]) ++ (R)⟩ := by rfl

theorem phase1 (n : Nat) : run0 table (2*n) ⟨3,([false,false,false,false,false]) ++ (rep [false,false] (n)) ++ ([true]) ++ (rep [false,false] (n)),[]⟩ = some ⟨3,([false,false,false,false,false,true]) ++ (rep [false,false] (n)),(rep [true,true] (n))⟩ := by
  simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using sweepL table 3 [false,false,false,false,false] [] [false,false] [true,true] 2 local1 n (([true]) ++ (rep [false,false] (n))) ([])

theorem phase2 (n : Nat) : run0 table 10 ⟨3,([false,false,false,false,false,true]) ++ (rep [false,false] (n)),(rep [true,true] (n))⟩ = some ⟨1,([false,true,false,false]) ++ (rep [false,false] (n)),([true,true]) ++ (rep [true,true] (n))⟩ := by rfl

theorem local3 (L R : List Bool) : run0 table 6 ⟨1,([false]) ++ (L),([true,true]) ++ ([true,true]) ++ (R)⟩ = some ⟨1,([false]) ++ ([false,false]) ++ (L),([true,true]) ++ (R)⟩ := by rfl

theorem phase3 (n : Nat) : run0 table (6*n) ⟨1,([false,true,false,false]) ++ (rep [false,false] (n)),([true,true]) ++ (rep [true,true] (n))⟩ = some ⟨1,([false]) ++ (rep [false,false] (n)) ++ ([true,false,false]) ++ (rep [false,false] (n)),([true,true])⟩ := by
  simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using sweepR table 1 [false] [true,true] [true,true] [false,false] 6 local3 n (([true,false,false]) ++ (rep [false,false] (n))) ([])

theorem phase4 (n : Nat) : run0 table 7 ⟨1,([false]) ++ (rep [false,false] (n)) ++ ([true,false,false]) ++ (rep [false,false] (n)),([true,true])⟩ = some ⟨2,([false,true,false,false]) ++ (rep [false,false] (n)) ++ ([true,false,false]) ++ (rep [false,false] (n)),[]⟩ := by rfl

theorem finalL (n : Nat) : ([false,true,false,false]) ++ (rep [false,false] (n)) ++ ([true,false,false]) ++ (rep [false,false] (n)) = ([false,true,false,false]) ++ (rep [false,false] (n)) ++ ([true,false,false]) ++ (rep [false,false] (n)) := by
  rfl

theorem finalR (n : Nat) : ([] : List Bool) = [] := by
  rfl

theorem growth (n : Nat) : run0 table (24+8*n) (family n) = some (family (n+1)) := by
  have H := (join0 (join0 (join0 (join0 (phase0 n) (phase1 n)) (phase2 n)) (phase3 n)) (phase4 n))
  rw [show 7+2*n+10+6*n+7=24+8*n by omega] at H
  simpa only [family,rep,List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using H

theorem never (m : Machine) (hm : compatible table m) : NeverHalts m :=
  never_of_growth table family 2 (fun n => 24+8*n) entry (by intro n; omega) growth m hm

#print axioms never

end M325

namespace M369

-- 1RB0RE_1RC1RB_0RD0LF_1LD0RA_---0RC_1LA1LF

def table : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 0,true => some (some ⟨false,true,4⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 1,true => some (some ⟨true,true,1⟩)
  | 2,false => some (some ⟨false,true,3⟩)
  | 2,true => some (some ⟨false,false,5⟩)
  | 3,false => some (some ⟨true,false,3⟩)
  | 3,true => some (some ⟨false,true,0⟩)
  | 4,true => some (some ⟨false,true,2⟩)
  | 5,false => some (some ⟨true,false,0⟩)
  | 5,true => some (some ⟨true,false,5⟩)
  | _,_ => none

def family (n : Nat) : Z0 := ⟨0,([false,false,false,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true]) ++ (rep [true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true] (n)),[]⟩

theorem entry : run0 table 136 ⟨0,[],[]⟩ = some (family 0) := by rfl

theorem phase0 (n : Nat) : run0 table 49 ⟨0,([false,false,false,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true]) ++ (rep [true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true] (n)),[]⟩ = some ⟨5,([true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true]) ++ (rep [true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true] (n)),([false,true,true,true,true,false])⟩ := by rfl

theorem local1 (L R : List Bool) : run0 table 23 ⟨5,([true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true]) ++ ([true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true]) ++ (L),(R)⟩ = some ⟨5,([true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true]) ++ (L),([true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true]) ++ (R)⟩ := by rfl

theorem phase1 (n : Nat) : run0 table (23*n) ⟨5,([true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true]) ++ (rep [true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true] (n)),([false,true,true,true,true,false])⟩ = some ⟨5,([true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true]),(rep [true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true] (n)) ++ ([false,true,true,true,true,false])⟩ := by
  simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using sweepL table 5 [true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true] [] [true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true] [true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true] 23 local1 n ([]) (([false,true,true,true,true,false]))

theorem phase2 (n : Nat) : run0 table 19 ⟨5,([true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true]),(rep [true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true] (n)) ++ ([false,true,true,true,true,false])⟩ = some ⟨1,([true,true]),([true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true]) ++ (rep [true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true] (n)) ++ ([false,true,true,true,true,false])⟩ := by rfl

theorem local3 (L R : List Bool) : run0 table 23 ⟨1,([true]) ++ (L),([true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true]) ++ ([true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true]) ++ (R)⟩ = some ⟨1,([true]) ++ ([true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true]) ++ (L),([true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true]) ++ (R)⟩ := by rfl

theorem phase3 (n : Nat) : run0 table (23*n) ⟨1,([true,true]),([true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true]) ++ (rep [true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true] (n)) ++ ([false,true,true,true,true,false])⟩ = some ⟨1,([true]) ++ (rep [true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true] (n)) ++ ([true]),([true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,false,true,true,true,true,false])⟩ := by
  simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using sweepR table 1 [true] [true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true] [true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true] [true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true] 23 local3 n (([true])) (([false,true,true,true,true,false]))

theorem phase4 (n : Nat) : run0 table 20 ⟨1,([true]) ++ (rep [true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true] (n)) ++ ([true]),([true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,false,true,true,true,true,false])⟩ = some ⟨5,([true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true]) ++ (rep [true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true] (n)) ++ ([true]),([false,true,true,true,false])⟩ := by rfl

theorem local5 (L R : List Bool) : run0 table 23 ⟨5,([true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true]) ++ ([true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true]) ++ (L),(R)⟩ = some ⟨5,([true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true]) ++ (L),([true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true]) ++ (R)⟩ := by rfl

theorem phase5 (n : Nat) : run0 table (23*n) ⟨5,([true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true]) ++ (rep [true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true] (n)) ++ ([true]),([false,true,true,true,false])⟩ = some ⟨5,([true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true]),(rep [true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true] (n)) ++ ([false,true,true,true,false])⟩ := by
  simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using sweepL table 5 [true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true] [] [true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true] [true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true] 23 local5 n (([true])) (([false,true,true,true,false]))

theorem phase6 (n : Nat) : run0 table 22 ⟨5,([true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true]),(rep [true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true] (n)) ++ ([false,true,true,true,false])⟩ = some ⟨1,([true,true]),([true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true]) ++ (rep [true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true] (n)) ++ ([false,true,true,true,false])⟩ := by rfl

theorem local7 (L R : List Bool) : run0 table 23 ⟨1,([true]) ++ (L),([true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true]) ++ ([true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true]) ++ (R)⟩ = some ⟨1,([true]) ++ ([true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true]) ++ (L),([true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true]) ++ (R)⟩ := by rfl

theorem phase7 (n : Nat) : run0 table (23*n) ⟨1,([true,true]),([true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true]) ++ (rep [true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true] (n)) ++ ([false,true,true,true,false])⟩ = some ⟨1,([true]) ++ (rep [true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true] (n)) ++ ([true]),([true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,false,true,true,true,false])⟩ := by
  simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using sweepR table 1 [true] [true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true] [true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true] [true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true] 23 local7 n (([true])) (([false,true,true,true,false]))

theorem phase8 (n : Nat) : run0 table 23 ⟨1,([true]) ++ (rep [true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true] (n)) ++ ([true]),([true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,false,true,true,true,false])⟩ = some ⟨5,([true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true]) ++ (rep [true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true] (n)) ++ ([true]),([false,true,true,false])⟩ := by rfl

theorem local9 (L R : List Bool) : run0 table 23 ⟨5,([true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true]) ++ ([true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true]) ++ (L),(R)⟩ = some ⟨5,([true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true]) ++ (L),([true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true]) ++ (R)⟩ := by rfl

theorem phase9 (n : Nat) : run0 table (23*n) ⟨5,([true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true]) ++ (rep [true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true] (n)) ++ ([true]),([false,true,true,false])⟩ = some ⟨5,([true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true]),(rep [true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true] (n)) ++ ([false,true,true,false])⟩ := by
  simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using sweepL table 5 [true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true] [] [true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true] [true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true] 23 local9 n (([true])) (([false,true,true,false]))

theorem phase10 (n : Nat) : run0 table 25 ⟨5,([true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true]),(rep [true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true] (n)) ++ ([false,true,true,false])⟩ = some ⟨1,([true,true]),([true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true]) ++ (rep [true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true] (n)) ++ ([false,true,true,false])⟩ := by rfl

theorem local11 (L R : List Bool) : run0 table 23 ⟨1,([true]) ++ (L),([true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true]) ++ ([true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true]) ++ (R)⟩ = some ⟨1,([true]) ++ ([true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true]) ++ (L),([true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true]) ++ (R)⟩ := by rfl

theorem phase11 (n : Nat) : run0 table (23*n) ⟨1,([true,true]),([true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true]) ++ (rep [true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true] (n)) ++ ([false,true,true,false])⟩ = some ⟨1,([true]) ++ (rep [true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true] (n)) ++ ([true]),([true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,false,true,true,false])⟩ := by
  simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using sweepR table 1 [true] [true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true] [true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true] [true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true] 23 local11 n (([true])) (([false,true,true,false]))

theorem phase12 (n : Nat) : run0 table 26 ⟨1,([true]) ++ (rep [true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true] (n)) ++ ([true]),([true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,false,true,true,false])⟩ = some ⟨5,([true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true]) ++ (rep [true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true] (n)) ++ ([true]),([false,true,false])⟩ := by rfl

theorem local13 (L R : List Bool) : run0 table 23 ⟨5,([true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true]) ++ ([true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true]) ++ (L),(R)⟩ = some ⟨5,([true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true]) ++ (L),([true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true]) ++ (R)⟩ := by rfl

theorem phase13 (n : Nat) : run0 table (23*n) ⟨5,([true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true]) ++ (rep [true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true] (n)) ++ ([true]),([false,true,false])⟩ = some ⟨5,([true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true]),(rep [true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true] (n)) ++ ([false,true,false])⟩ := by
  simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using sweepL table 5 [true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true] [] [true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true] [true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true] 23 local13 n (([true])) (([false,true,false]))

theorem phase14 (n : Nat) : run0 table 28 ⟨5,([true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true]),(rep [true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true] (n)) ++ ([false,true,false])⟩ = some ⟨1,([true,true]),([true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true]) ++ (rep [true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true] (n)) ++ ([false,true,false])⟩ := by rfl

theorem local15 (L R : List Bool) : run0 table 23 ⟨1,([true]) ++ (L),([true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true]) ++ ([true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true]) ++ (R)⟩ = some ⟨1,([true]) ++ ([true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true]) ++ (L),([true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true]) ++ (R)⟩ := by rfl

theorem phase15 (n : Nat) : run0 table (23*n) ⟨1,([true,true]),([true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true]) ++ (rep [true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true] (n)) ++ ([false,true,false])⟩ = some ⟨1,([true]) ++ (rep [true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true] (n)) ++ ([true]),([true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,false,true,false])⟩ := by
  simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using sweepR table 1 [true] [true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true] [true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true] [true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true] 23 local15 n (([true])) (([false,true,false]))

theorem phase16 (n : Nat) : run0 table 29 ⟨1,([true]) ++ (rep [true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true] (n)) ++ ([true]),([true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,false,true,false])⟩ = some ⟨5,([true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true]) ++ (rep [true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true] (n)) ++ ([true]),([false,false])⟩ := by rfl

theorem local17 (L R : List Bool) : run0 table 23 ⟨5,([true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true]) ++ ([true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true]) ++ (L),(R)⟩ = some ⟨5,([true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true]) ++ (L),([true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true]) ++ (R)⟩ := by rfl

theorem phase17 (n : Nat) : run0 table (23*n) ⟨5,([true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true]) ++ (rep [true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true] (n)) ++ ([true]),([false,false])⟩ = some ⟨5,([true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true]),(rep [true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true] (n)) ++ ([false,false])⟩ := by
  simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using sweepL table 5 [true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true] [] [true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true] [true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true] 23 local17 n (([true])) (([false,false]))

theorem phase18 (n : Nat) : run0 table 31 ⟨5,([true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true]),(rep [true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true] (n)) ++ ([false,false])⟩ = some ⟨1,([true,true]),([true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true]) ++ (rep [true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true] (n)) ++ ([false,false])⟩ := by rfl

theorem local19 (L R : List Bool) : run0 table 23 ⟨1,([true]) ++ (L),([true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true]) ++ ([true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true]) ++ (R)⟩ = some ⟨1,([true]) ++ ([true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true]) ++ (L),([true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true]) ++ (R)⟩ := by rfl

theorem phase19 (n : Nat) : run0 table (23*n) ⟨1,([true,true]),([true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true]) ++ (rep [true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true] (n)) ++ ([false,false])⟩ = some ⟨1,([true]) ++ (rep [true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true] (n)) ++ ([true]),([true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,false,false])⟩ := by
  simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using sweepR table 1 [true] [true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true] [true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true] [true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true] 23 local19 n (([true])) (([false,false]))

theorem phase20 (n : Nat) : run0 table 64 ⟨1,([true]) ++ (rep [true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true] (n)) ++ ([true]),([true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,false,false])⟩ = some ⟨5,([true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true]) ++ (rep [true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true] (n)) ++ ([true]),([false,true,false,true])⟩ := by rfl

theorem local21 (L R : List Bool) : run0 table 23 ⟨5,([true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true]) ++ ([true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true]) ++ (L),(R)⟩ = some ⟨5,([true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true]) ++ (L),([true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true]) ++ (R)⟩ := by rfl

theorem phase21 (n : Nat) : run0 table (23*n) ⟨5,([true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true]) ++ (rep [true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true] (n)) ++ ([true]),([false,true,false,true])⟩ = some ⟨5,([true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true]),(rep [true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true] (n)) ++ ([false,true,false,true])⟩ := by
  simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using sweepL table 5 [true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true] [] [true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true] [true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true] 23 local21 n (([true])) (([false,true,false,true]))

theorem phase22 (n : Nat) : run0 table 34 ⟨5,([true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true]),(rep [true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true] (n)) ++ ([false,true,false,true])⟩ = some ⟨1,([true,true]),([true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true]) ++ (rep [true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true] (n)) ++ ([false,true,false,true])⟩ := by rfl

theorem local23 (L R : List Bool) : run0 table 23 ⟨1,([true]) ++ (L),([true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true]) ++ ([true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true]) ++ (R)⟩ = some ⟨1,([true]) ++ ([true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true]) ++ (L),([true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true]) ++ (R)⟩ := by rfl

theorem phase23 (n : Nat) : run0 table (23*n) ⟨1,([true,true]),([true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true]) ++ (rep [true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true] (n)) ++ ([false,true,false,true])⟩ = some ⟨1,([true]) ++ (rep [true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true] (n)) ++ ([true]),([true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,false,true,false,true])⟩ := by
  simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using sweepR table 1 [true] [true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true] [true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true] [true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true] 23 local23 n (([true])) (([false,true,false,true]))

theorem phase24 (n : Nat) : run0 table 35 ⟨1,([true]) ++ (rep [true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true] (n)) ++ ([true]),([true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,false,true,false,true])⟩ = some ⟨5,([true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true]) ++ (rep [true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true] (n)) ++ ([true]),([false,false,true])⟩ := by rfl

theorem local25 (L R : List Bool) : run0 table 23 ⟨5,([true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true]) ++ ([true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true]) ++ (L),(R)⟩ = some ⟨5,([true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true]) ++ (L),([true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true]) ++ (R)⟩ := by rfl

theorem phase25 (n : Nat) : run0 table (23*n) ⟨5,([true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true]) ++ (rep [true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true] (n)) ++ ([true]),([false,false,true])⟩ = some ⟨5,([true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true]),(rep [true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true] (n)) ++ ([false,false,true])⟩ := by
  simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using sweepL table 5 [true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true] [] [true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true] [true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true] 23 local25 n (([true])) (([false,false,true]))

theorem phase26 (n : Nat) : run0 table 37 ⟨5,([true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true]),(rep [true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true] (n)) ++ ([false,false,true])⟩ = some ⟨1,([true,true]),([true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true]) ++ (rep [true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true] (n)) ++ ([false,false,true])⟩ := by rfl

theorem local27 (L R : List Bool) : run0 table 23 ⟨1,([true]) ++ (L),([true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true]) ++ ([true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true]) ++ (R)⟩ = some ⟨1,([true]) ++ ([true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true]) ++ (L),([true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true]) ++ (R)⟩ := by rfl

theorem phase27 (n : Nat) : run0 table (23*n) ⟨1,([true,true]),([true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true]) ++ (rep [true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true] (n)) ++ ([false,false,true])⟩ = some ⟨1,([true]) ++ (rep [true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true] (n)) ++ ([true]),([true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,false,false,true])⟩ := by
  simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using sweepR table 1 [true] [true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true] [true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true] [true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true] 23 local27 n (([true])) (([false,false,true]))

theorem phase28 (n : Nat) : run0 table 39 ⟨1,([true]) ++ (rep [true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true] (n)) ++ ([true]),([true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,false,false,true])⟩ = some ⟨0,([false,false,false,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true]) ++ (rep [true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true] (n)) ++ ([true]),[]⟩ := by rfl

theorem finalL (n : Nat) : ([false,false,false,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true]) ++ (rep [true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true] (n)) ++ ([true]) = ([false,false,false,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true]) ++ (rep [true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true] (n)) := by
  calc
    _ = ([false,false,false,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true]) ++ (rep [true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true] (n)) := by symm; simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using moveCut (([false,false,false,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true])) ([]) [true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true] true n

theorem finalR (n : Nat) : ([] : List Bool) = [] := by
  rfl

theorem growth (n : Nat) : run0 table (481+322*n) (family n) = some (family (n+1)) := by
  have H := (join0 (join0 (join0 (join0 (join0 (join0 (join0 (join0 (join0 (join0 (join0 (join0 (join0 (join0 (join0 (join0 (join0 (join0 (join0 (join0 (join0 (join0 (join0 (join0 (join0 (join0 (join0 (join0 (phase0 n) (phase1 n)) (phase2 n)) (phase3 n)) (phase4 n)) (phase5 n)) (phase6 n)) (phase7 n)) (phase8 n)) (phase9 n)) (phase10 n)) (phase11 n)) (phase12 n)) (phase13 n)) (phase14 n)) (phase15 n)) (phase16 n)) (phase17 n)) (phase18 n)) (phase19 n)) (phase20 n)) (phase21 n)) (phase22 n)) (phase23 n)) (phase24 n)) (phase25 n)) (phase26 n)) (phase27 n)) (phase28 n))
  rw [finalL n] at H
  rw [show 49+23*n+19+23*n+20+23*n+22+23*n+23+23*n+25+23*n+26+23*n+28+23*n+29+23*n+31+23*n+64+23*n+34+23*n+35+23*n+37+23*n+39=481+322*n by omega] at H
  simpa only [family,rep,List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using H

theorem never (m : Machine) (hm : compatible table m) : NeverHalts m :=
  never_of_growth table family 136 (fun n => 481+322*n) entry (by intro n; omega) growth m hm

#print axioms never

end M369

namespace M505

-- 1RB0RE_1RC0RF_0RD1RB_1LD0RA_---0RC_---0RB

def table : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 0,true => some (some ⟨false,true,4⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 1,true => some (some ⟨false,true,5⟩)
  | 2,false => some (some ⟨false,true,3⟩)
  | 2,true => some (some ⟨true,true,1⟩)
  | 3,false => some (some ⟨true,false,3⟩)
  | 3,true => some (some ⟨false,true,0⟩)
  | 4,true => some (some ⟨false,true,2⟩)
  | 5,true => some (some ⟨false,true,1⟩)
  | _,_ => none

def family (n : Nat) : Z0 := ⟨1,([false]) ++ (rep [false,false] (n)) ++ ([true]) ++ (rep [false,false,false] (n)),[]⟩

theorem entry : run0 table 1 ⟨0,[],[]⟩ = some (family 0) := by rfl

theorem phase0 (n : Nat) : run0 table 8 ⟨1,([false]) ++ (rep [false,false] (n)) ++ ([true]) ++ (rep [false,false,false] (n)),[]⟩ = some ⟨3,([false,false,false,false,false]) ++ (rep [false,false] (n)) ++ ([true]) ++ (rep [false,false,false] (n)),[]⟩ := by rfl

theorem local1 (L R : List Bool) : run0 table 2 ⟨3,([false,false,false,false,false]) ++ ([false,false]) ++ (L),(R)⟩ = some ⟨3,([false,false,false,false,false]) ++ (L),([true,true]) ++ (R)⟩ := by rfl

theorem phase1 (n : Nat) : run0 table (2*n) ⟨3,([false,false,false,false,false]) ++ (rep [false,false] (n)) ++ ([true]) ++ (rep [false,false,false] (n)),[]⟩ = some ⟨3,([false,false,false,false,false,true]) ++ (rep [false,false,false] (n)),(rep [true,true] (n))⟩ := by
  simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using sweepL table 3 [false,false,false,false,false] [] [false,false] [true,true] 2 local1 n (([true]) ++ (rep [false,false,false] (n))) ([])

theorem phase2 (n : Nat) : run0 table 9 ⟨3,([false,false,false,false,false,true]) ++ (rep [false,false,false] (n)),(rep [true,true] (n))⟩ = some ⟨1,([true,true,false,false,false]) ++ (rep [false,false,false] (n)),([true]) ++ (rep [true,true] (n))⟩ := by rfl

theorem local3 (L R : List Bool) : run0 table 2 ⟨1,([true]) ++ (L),([true]) ++ ([true,true]) ++ (R)⟩ = some ⟨1,([true]) ++ ([false,false]) ++ (L),([true]) ++ (R)⟩ := by rfl

theorem phase3 (n : Nat) : run0 table (2*n) ⟨1,([true,true,false,false,false]) ++ (rep [false,false,false] (n)),([true]) ++ (rep [true,true] (n))⟩ = some ⟨1,([true]) ++ (rep [false,false] (n)) ++ ([true,false,false,false]) ++ (rep [false,false,false] (n)),([true])⟩ := by
  simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using sweepR table 1 [true] [true] [true,true] [false,false] 2 local3 n (([true,false,false,false]) ++ (rep [false,false,false] (n))) ([])

theorem phase4 (n : Nat) : run0 table 2 ⟨1,([true]) ++ (rep [false,false] (n)) ++ ([true,false,false,false]) ++ (rep [false,false,false] (n)),([true])⟩ = some ⟨1,([false,false,false]) ++ (rep [false,false] (n)) ++ ([true,false,false,false]) ++ (rep [false,false,false] (n)),[]⟩ := by rfl

theorem finalL (n : Nat) : ([false,false,false]) ++ (rep [false,false] (n)) ++ ([true,false,false,false]) ++ (rep [false,false,false] (n)) = ([false,false,false]) ++ (rep [false,false] (n)) ++ ([true,false,false,false]) ++ (rep [false,false,false] (n)) := by
  rfl

theorem finalR (n : Nat) : ([] : List Bool) = [] := by
  rfl

theorem growth (n : Nat) : run0 table (19+4*n) (family n) = some (family (n+1)) := by
  have H := (join0 (join0 (join0 (join0 (phase0 n) (phase1 n)) (phase2 n)) (phase3 n)) (phase4 n))
  rw [show 8+2*n+9+2*n+2=19+4*n by omega] at H
  simpa only [family,rep,List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using H

theorem never (m : Machine) (hm : compatible table m) : NeverHalts m :=
  never_of_growth table family 1 (fun n => 19+4*n) entry (by intro n; omega) growth m hm

#print axioms never

end M505

namespace M521

-- 1RB0RE_1RC---_0RD1RF_1LD0RA_1LF0RC_0LA0LF

def table : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 0,true => some (some ⟨false,true,4⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 2,false => some (some ⟨false,true,3⟩)
  | 2,true => some (some ⟨true,true,5⟩)
  | 3,false => some (some ⟨true,false,3⟩)
  | 3,true => some (some ⟨false,true,0⟩)
  | 4,false => some (some ⟨true,false,5⟩)
  | 4,true => some (some ⟨false,true,2⟩)
  | 5,false => some (some ⟨false,false,0⟩)
  | 5,true => some (some ⟨false,false,5⟩)
  | _,_ => none

def family (n : Nat) : Z0 := ⟨5,[],([false,false,false,false,true,false,false,false,true]) ++ (rep [true,false,false,false,true] (n))⟩

theorem entry : run0 table 78 ⟨0,[],[]⟩ = some (family 0) := by rfl

theorem phase0 (n : Nat) : run0 table 2 ⟨5,[],([false,false,false,false,true,false,false,false,true]) ++ (rep [true,false,false,false,true] (n))⟩ = some ⟨1,([false,true]),([false,false,false,false,true,false,false,false,true]) ++ (rep [true,false,false,false,true] (n))⟩ := by rfl

theorem local1 (L R : List Bool) : run0 table 75 ⟨1,([false,true]) ++ (L),([false,false,false,false,true,false,false,false,true]) ++ ([true,false,false,false,true]) ++ (R)⟩ = some ⟨1,([false,true]) ++ ([true,false,false,true,false]) ++ (L),([false,false,false,false,true,false,false,false,true]) ++ (R)⟩ := by rfl

theorem phase1 (n : Nat) : run0 table (75*n) ⟨1,([false,true]),([false,false,false,false,true,false,false,false,true]) ++ (rep [true,false,false,false,true] (n))⟩ = some ⟨1,([false,true]) ++ (rep [true,false,false,true,false] (n)),([false,false,false,false,true,false,false,false,true])⟩ := by
  simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using sweepR table 1 [false,true] [false,false,false,false,true,false,false,false,true] [true,false,false,false,true] [true,false,false,true,false] 75 local1 n ([]) ([])

theorem phase2 (n : Nat) : run0 table 111 ⟨1,([false,true]) ++ (rep [true,false,false,true,false] (n)),([false,false,false,false,true,false,false,false,true])⟩ = some ⟨5,([false,true,true,true,false,false,true,false,true,false,false,true,false]) ++ (rep [true,false,false,true,false] (n)),[]⟩ := by rfl

theorem local3 (L R : List Bool) : run0 table 27 ⟨5,([false,true,true,true,false,false,true,false,true,false,false,true,false]) ++ ([true,false,false,true,false]) ++ (L),(R)⟩ = some ⟨5,([false,true,true,true,false,false,true,false,true,false,false,true,false]) ++ (L),([true,false,false,false,true]) ++ (R)⟩ := by rfl

theorem phase3 (n : Nat) : run0 table (27*n) ⟨5,([false,true,true,true,false,false,true,false,true,false,false,true,false]) ++ (rep [true,false,false,true,false] (n)),[]⟩ = some ⟨5,([false,true,true,true,false,false,true,false,true,false,false,true,false]),(rep [true,false,false,false,true] (n))⟩ := by
  simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using sweepL table 5 [false,true,true,true,false,false,true,false,true,false,false,true,false] [] [true,false,false,true,false] [true,false,false,false,true] 27 local3 n ([]) ([])

theorem phase4 (n : Nat) : run0 table 68 ⟨5,([false,true,true,true,false,false,true,false,true,false,false,true,false]),(rep [true,false,false,false,true] (n))⟩ = some ⟨5,[],([false,false,false,false,true,false,false,false,true,true,false,false,false,true]) ++ (rep [true,false,false,false,true] (n))⟩ := by rfl

theorem finalL (n : Nat) : ([] : List Bool) = [] := by
  rfl

theorem finalR (n : Nat) : ([false,false,false,false,true,false,false,false,true,true,false,false,false,true]) ++ (rep [true,false,false,false,true] (n)) = ([false,false,false,false,true,false,false,false,true,true,false,false,false,true]) ++ (rep [true,false,false,false,true] (n)) := by
  rfl

theorem growth (n : Nat) : run0 table (181+102*n) (family n) = some (family (n+1)) := by
  have H := (join0 (join0 (join0 (join0 (phase0 n) (phase1 n)) (phase2 n)) (phase3 n)) (phase4 n))
  rw [show 2+75*n+111+27*n+68=181+102*n by omega] at H
  simpa only [family,rep,List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using H

theorem never (m : Machine) (hm : compatible table m) : NeverHalts m :=
  never_of_growth table family 78 (fun n => 181+102*n) entry (by intro n; omega) growth m hm

#print axioms never

end M521

namespace M531

-- 1RB0RE_1RC---_0RD1RF_1LD0RA_1LB0RC_0LE0RF

def table : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 0,true => some (some ⟨false,true,4⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 2,false => some (some ⟨false,true,3⟩)
  | 2,true => some (some ⟨true,true,5⟩)
  | 3,false => some (some ⟨true,false,3⟩)
  | 3,true => some (some ⟨false,true,0⟩)
  | 4,false => some (some ⟨true,false,1⟩)
  | 4,true => some (some ⟨false,true,2⟩)
  | 5,false => some (some ⟨false,false,4⟩)
  | 5,true => some (some ⟨false,true,5⟩)
  | _,_ => none

def family (n : Nat) : Z0 := ⟨3,([false,false,false,false,false]) ++ (rep [false] (n)) ++ ([true]) ++ (rep [false,false,false] (n)),[]⟩

theorem entry : run0 table 9 ⟨0,[],[]⟩ = some (family 0) := by rfl

theorem local0 (L R : List Bool) : run0 table 1 ⟨3,([false,false,false,false,false]) ++ ([false]) ++ (L),(R)⟩ = some ⟨3,([false,false,false,false,false]) ++ (L),([true]) ++ (R)⟩ := by rfl

theorem phase0 (n : Nat) : run0 table (1*n) ⟨3,([false,false,false,false,false]) ++ (rep [false] (n)) ++ ([true]) ++ (rep [false,false,false] (n)),[]⟩ = some ⟨3,([false,false,false,false,false,true]) ++ (rep [false,false,false] (n)),(rep [true] (n))⟩ := by
  simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using sweepL table 3 [false,false,false,false,false] [] [false] [true] 1 local0 n (([true]) ++ (rep [false,false,false] (n))) ([])

theorem phase1 (n : Nat) : run0 table 9 ⟨3,([false,false,false,false,false,true]) ++ (rep [false,false,false] (n)),(rep [true] (n))⟩ = some ⟨5,([true,true,false,false,false]) ++ (rep [false,false,false] (n)),([true]) ++ (rep [true] (n))⟩ := by rfl

theorem local2 (L R : List Bool) : run0 table 1 ⟨5,([true]) ++ (L),([true]) ++ ([true]) ++ (R)⟩ = some ⟨5,([true]) ++ ([false]) ++ (L),([true]) ++ (R)⟩ := by rfl

theorem phase2 (n : Nat) : run0 table (1*n) ⟨5,([true,true,false,false,false]) ++ (rep [false,false,false] (n)),([true]) ++ (rep [true] (n))⟩ = some ⟨5,([true]) ++ (rep [false] (n)) ++ ([true,false,false,false]) ++ (rep [false,false,false] (n)),([true])⟩ := by
  simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using sweepR table 5 [true] [true] [true] [false] 1 local2 n (([true,false,false,false]) ++ (rep [false,false,false] (n))) ([])

theorem phase3 (n : Nat) : run0 table 19 ⟨5,([true]) ++ (rep [false] (n)) ++ ([true,false,false,false]) ++ (rep [false,false,false] (n)),([true])⟩ = some ⟨3,([false,false,false,false,false,false]) ++ (rep [false] (n)) ++ ([true,false,false,false]) ++ (rep [false,false,false] (n)),[]⟩ := by rfl

theorem finalL (n : Nat) : ([false,false,false,false,false,false]) ++ (rep [false] (n)) ++ ([true,false,false,false]) ++ (rep [false,false,false] (n)) = ([false,false,false,false,false,false]) ++ (rep [false] (n)) ++ ([true,false,false,false]) ++ (rep [false,false,false] (n)) := by
  rfl

theorem finalR (n : Nat) : ([] : List Bool) = [] := by
  rfl

theorem growth (n : Nat) : run0 table (28+2*n) (family n) = some (family (n+1)) := by
  have H := (join0 (join0 (join0 (phase0 n) (phase1 n)) (phase2 n)) (phase3 n))
  rw [show 1*n+9+1*n+19=28+2*n by omega] at H
  simpa only [family,rep,List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using H

theorem never (m : Machine) (hm : compatible table m) : NeverHalts m :=
  never_of_growth table family 9 (fun n => 28+2*n) entry (by intro n; omega) growth m hm

#print axioms never

end M531

namespace M959

-- 1RB0RE_1RC0LF_0RD0RB_1LD0RA_---1LA_1LB1LF

def table : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 0,true => some (some ⟨false,true,4⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 1,true => some (some ⟨false,false,5⟩)
  | 2,false => some (some ⟨false,true,3⟩)
  | 2,true => some (some ⟨false,true,1⟩)
  | 3,false => some (some ⟨true,false,3⟩)
  | 3,true => some (some ⟨false,true,0⟩)
  | 4,true => some (some ⟨true,false,0⟩)
  | 5,false => some (some ⟨true,false,1⟩)
  | 5,true => some (some ⟨true,false,5⟩)
  | _,_ => none

def family (n : Nat) : Z0 := ⟨5,[],([false,true,false,true,false,true,false,true]) ++ (rep [false,true,false,true,false,true,false,true] (n)) ++ ([true,false,true,false,true,false,false])⟩

theorem entry : run0 table 109 ⟨0,[],[]⟩ = some (family 0) := by rfl

theorem phase0 (n : Nat) : run0 table 2 ⟨5,[],([false,true,false,true,false,true,false,true]) ++ (rep [false,true,false,true,false,true,false,true] (n)) ++ ([true,false,true,false,true,false,false])⟩ = some ⟨2,([true,true]),([false,true,false,true,false,true,false,true]) ++ (rep [false,true,false,true,false,true,false,true] (n)) ++ ([true,false,true,false,true,false,false])⟩ := by rfl

theorem local1 (L R : List Bool) : run0 table 8 ⟨2,([true]) ++ (L),([false,true,false,true,false,true,false,true]) ++ ([false,true,false,true,false,true,false,true]) ++ (R)⟩ = some ⟨2,([true]) ++ ([true,false,true,false,true,false,true,false]) ++ (L),([false,true,false,true,false,true,false,true]) ++ (R)⟩ := by rfl

theorem phase1 (n : Nat) : run0 table (8*n) ⟨2,([true,true]),([false,true,false,true,false,true,false,true]) ++ (rep [false,true,false,true,false,true,false,true] (n)) ++ ([true,false,true,false,true,false,false])⟩ = some ⟨2,([true]) ++ (rep [true,false,true,false,true,false,true,false] (n)) ++ ([true]),([false,true,false,true,false,true,false,true,true,false,true,false,true,false,false])⟩ := by
  simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using sweepR table 2 [true] [false,true,false,true,false,true,false,true] [false,true,false,true,false,true,false,true] [true,false,true,false,true,false,true,false] 8 local1 n (([true])) (([true,false,true,false,true,false,false]))

theorem phase2 (n : Nat) : run0 table 9 ⟨2,([true]) ++ (rep [true,false,true,false,true,false,true,false] (n)) ++ ([true]),([false,true,false,true,false,true,false,true,true,false,true,false,true,false,false])⟩ = some ⟨1,([true,false,true,false,true,false,true,false,true,false]) ++ (rep [true,false,true,false,true,false,true,false] (n)) ++ ([true]),([false,true,false,true,false,false])⟩ := by rfl

theorem local3 (L R : List Bool) : run0 table 8 ⟨1,([true,false,true,false,true,false,true,false,true,false]) ++ ([true,false,true,false,true,false,true,false]) ++ (L),(R)⟩ = some ⟨1,([true,false,true,false,true,false,true,false,true,false]) ++ (L),([true,false,true,false,true,false,true,false]) ++ (R)⟩ := by rfl

theorem phase3 (n : Nat) : run0 table (8*n) ⟨1,([true,false,true,false,true,false,true,false,true,false]) ++ (rep [true,false,true,false,true,false,true,false] (n)) ++ ([true]),([false,true,false,true,false,false])⟩ = some ⟨1,([true,false,true,false,true,false,true,false,true,false,true]),(rep [true,false,true,false,true,false,true,false] (n)) ++ ([false,true,false,true,false,false])⟩ := by
  simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using sweepL table 1 [true,false,true,false,true,false,true,false,true,false] [] [true,false,true,false,true,false,true,false] [true,false,true,false,true,false,true,false] 8 local3 n (([true])) (([false,true,false,true,false,false]))

theorem phase4 (n : Nat) : run0 table 13 ⟨1,([true,false,true,false,true,false,true,false,true,false,true]),(rep [true,false,true,false,true,false,true,false] (n)) ++ ([false,true,false,true,false,false])⟩ = some ⟨2,([true,true]),([false,true,false,true,false,true,false,true,false,true,false]) ++ (rep [true,false,true,false,true,false,true,false] (n)) ++ ([false,true,false,true,false,false])⟩ := by rfl

theorem local5 (L R : List Bool) : run0 table 8 ⟨2,([true]) ++ (L),([false,true,false,true,false,true,false,true,false,true,false]) ++ ([true,false,true,false,true,false,true,false]) ++ (R)⟩ = some ⟨2,([true]) ++ ([true,false,true,false,true,false,true,false]) ++ (L),([false,true,false,true,false,true,false,true,false,true,false]) ++ (R)⟩ := by rfl

theorem phase5 (n : Nat) : run0 table (8*n) ⟨2,([true,true]),([false,true,false,true,false,true,false,true,false,true,false]) ++ (rep [true,false,true,false,true,false,true,false] (n)) ++ ([false,true,false,true,false,false])⟩ = some ⟨2,([true]) ++ (rep [true,false,true,false,true,false,true,false] (n)) ++ ([true]),([false,true,false,true,false,true,false,true,false,true,false,false,true,false,true,false,false])⟩ := by
  simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using sweepR table 2 [true] [false,true,false,true,false,true,false,true,false,true,false] [true,false,true,false,true,false,true,false] [true,false,true,false,true,false,true,false] 8 local5 n (([true])) (([false,true,false,true,false,false]))

theorem phase6 (n : Nat) : run0 table 24 ⟨2,([true]) ++ (rep [true,false,true,false,true,false,true,false] (n)) ++ ([true]),([false,true,false,true,false,true,false,true,false,true,false,false,true,false,true,false,false])⟩ = some ⟨5,([false,true,false,true,false,true,false,true,false,true,false]) ++ (rep [true,false,true,false,true,false,true,false] (n)) ++ ([true]),([true,false,true,false,false,false,false])⟩ := by rfl

theorem local7 (L R : List Bool) : run0 table 8 ⟨5,([false,true,false,true,false,true,false,true,false,true,false]) ++ ([true,false,true,false,true,false,true,false]) ++ (L),(R)⟩ = some ⟨5,([false,true,false,true,false,true,false,true,false,true,false]) ++ (L),([false,true,false,true,false,true,false,true]) ++ (R)⟩ := by rfl

theorem phase7 (n : Nat) : run0 table (8*n) ⟨5,([false,true,false,true,false,true,false,true,false,true,false]) ++ (rep [true,false,true,false,true,false,true,false] (n)) ++ ([true]),([true,false,true,false,false,false,false])⟩ = some ⟨5,([false,true,false,true,false,true,false,true,false,true,false,true]),(rep [false,true,false,true,false,true,false,true] (n)) ++ ([true,false,true,false,false,false,false])⟩ := by
  simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using sweepL table 5 [false,true,false,true,false,true,false,true,false,true,false] [] [true,false,true,false,true,false,true,false] [false,true,false,true,false,true,false,true] 8 local7 n (([true])) (([true,false,true,false,false,false,false]))

theorem phase8 (n : Nat) : run0 table 14 ⟨5,([false,true,false,true,false,true,false,true,false,true,false,true]),(rep [false,true,false,true,false,true,false,true] (n)) ++ ([true,false,true,false,false,false,false])⟩ = some ⟨2,([true,true]),([false,true,false,true,false,true,false,true,false,true,false,true]) ++ (rep [false,true,false,true,false,true,false,true] (n)) ++ ([true,false,true,false,false,false,false])⟩ := by rfl

theorem local9 (L R : List Bool) : run0 table 8 ⟨2,([true]) ++ (L),([false,true,false,true,false,true,false,true,false,true,false,true]) ++ ([false,true,false,true,false,true,false,true]) ++ (R)⟩ = some ⟨2,([true]) ++ ([true,false,true,false,true,false,true,false]) ++ (L),([false,true,false,true,false,true,false,true,false,true,false,true]) ++ (R)⟩ := by rfl

theorem phase9 (n : Nat) : run0 table (8*n) ⟨2,([true,true]),([false,true,false,true,false,true,false,true,false,true,false,true]) ++ (rep [false,true,false,true,false,true,false,true] (n)) ++ ([true,false,true,false,false,false,false])⟩ = some ⟨2,([true]) ++ (rep [true,false,true,false,true,false,true,false] (n)) ++ ([true]),([false,true,false,true,false,true,false,true,false,true,false,true,true,false,true,false,false,false,false])⟩ := by
  simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using sweepR table 2 [true] [false,true,false,true,false,true,false,true,false,true,false,true] [false,true,false,true,false,true,false,true] [true,false,true,false,true,false,true,false] 8 local9 n (([true])) (([true,false,true,false,false,false,false]))

theorem phase10 (n : Nat) : run0 table 13 ⟨2,([true]) ++ (rep [true,false,true,false,true,false,true,false] (n)) ++ ([true]),([false,true,false,true,false,true,false,true,false,true,false,true,true,false,true,false,false,false,false])⟩ = some ⟨1,([true,false,true,false,true,false,true,false,true,false,true,false,true,false]) ++ (rep [true,false,true,false,true,false,true,false] (n)) ++ ([true]),([false,true,false,false,false,false])⟩ := by rfl

theorem local11 (L R : List Bool) : run0 table 8 ⟨1,([true,false,true,false,true,false,true,false,true,false,true,false,true,false]) ++ ([true,false,true,false,true,false,true,false]) ++ (L),(R)⟩ = some ⟨1,([true,false,true,false,true,false,true,false,true,false,true,false,true,false]) ++ (L),([true,false,true,false,true,false,true,false]) ++ (R)⟩ := by rfl

theorem phase11 (n : Nat) : run0 table (8*n) ⟨1,([true,false,true,false,true,false,true,false,true,false,true,false,true,false]) ++ (rep [true,false,true,false,true,false,true,false] (n)) ++ ([true]),([false,true,false,false,false,false])⟩ = some ⟨1,([true,false,true,false,true,false,true,false,true,false,true,false,true,false,true]),(rep [true,false,true,false,true,false,true,false] (n)) ++ ([false,true,false,false,false,false])⟩ := by
  simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using sweepL table 1 [true,false,true,false,true,false,true,false,true,false,true,false,true,false] [] [true,false,true,false,true,false,true,false] [true,false,true,false,true,false,true,false] 8 local11 n (([true])) (([false,true,false,false,false,false]))

theorem phase12 (n : Nat) : run0 table 17 ⟨1,([true,false,true,false,true,false,true,false,true,false,true,false,true,false,true]),(rep [true,false,true,false,true,false,true,false] (n)) ++ ([false,true,false,false,false,false])⟩ = some ⟨2,([true,true]),([false,true,false,true,false,true,false,true,false,true,false,true,false,true,false]) ++ (rep [true,false,true,false,true,false,true,false] (n)) ++ ([false,true,false,false,false,false])⟩ := by rfl

theorem local13 (L R : List Bool) : run0 table 8 ⟨2,([true]) ++ (L),([false,true,false,true,false,true,false,true,false,true,false,true,false,true,false]) ++ ([true,false,true,false,true,false,true,false]) ++ (R)⟩ = some ⟨2,([true]) ++ ([true,false,true,false,true,false,true,false]) ++ (L),([false,true,false,true,false,true,false,true,false,true,false,true,false,true,false]) ++ (R)⟩ := by rfl

theorem phase13 (n : Nat) : run0 table (8*n) ⟨2,([true,true]),([false,true,false,true,false,true,false,true,false,true,false,true,false,true,false]) ++ (rep [true,false,true,false,true,false,true,false] (n)) ++ ([false,true,false,false,false,false])⟩ = some ⟨2,([true]) ++ (rep [true,false,true,false,true,false,true,false] (n)) ++ ([true]),([false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,false,true,false,false,false,false])⟩ := by
  simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using sweepR table 2 [true] [false,true,false,true,false,true,false,true,false,true,false,true,false,true,false] [true,false,true,false,true,false,true,false] [true,false,true,false,true,false,true,false] 8 local13 n (([true])) (([false,true,false,false,false,false]))

theorem phase14 (n : Nat) : run0 table 42 ⟨2,([true]) ++ (rep [true,false,true,false,true,false,true,false] (n)) ++ ([true]),([false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,false,true,false,false,false,false])⟩ = some ⟨5,([false,true,false,true,false,true,false,true,false,true,false,true,false,true,false]) ++ (rep [true,false,true,false,true,false,true,false] (n)) ++ ([true]),([true,false,true,false,true,false,false])⟩ := by rfl

theorem local15 (L R : List Bool) : run0 table 8 ⟨5,([false,true,false,true,false,true,false,true,false,true,false,true,false,true,false]) ++ ([true,false,true,false,true,false,true,false]) ++ (L),(R)⟩ = some ⟨5,([false,true,false,true,false,true,false,true,false,true,false,true,false,true,false]) ++ (L),([false,true,false,true,false,true,false,true]) ++ (R)⟩ := by rfl

theorem phase15 (n : Nat) : run0 table (8*n) ⟨5,([false,true,false,true,false,true,false,true,false,true,false,true,false,true,false]) ++ (rep [true,false,true,false,true,false,true,false] (n)) ++ ([true]),([true,false,true,false,true,false,false])⟩ = some ⟨5,([false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true]),(rep [false,true,false,true,false,true,false,true] (n)) ++ ([true,false,true,false,true,false,false])⟩ := by
  simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using sweepL table 5 [false,true,false,true,false,true,false,true,false,true,false,true,false,true,false] [] [true,false,true,false,true,false,true,false] [false,true,false,true,false,true,false,true] 8 local15 n (([true])) (([true,false,true,false,true,false,false]))

theorem phase16 (n : Nat) : run0 table 16 ⟨5,([false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true]),(rep [false,true,false,true,false,true,false,true] (n)) ++ ([true,false,true,false,true,false,false])⟩ = some ⟨5,[],([false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true]) ++ (rep [false,true,false,true,false,true,false,true] (n)) ++ ([true,false,true,false,true,false,false])⟩ := by rfl

theorem finalL (n : Nat) : ([] : List Bool) = [] := by
  rfl

theorem finalR (n : Nat) : ([false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true]) ++ (rep [false,true,false,true,false,true,false,true] (n)) ++ ([true,false,true,false,true,false,false]) = ([false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true]) ++ (rep [false,true,false,true,false,true,false,true] (n)) ++ ([true,false,true,false,true,false,false]) := by
  rfl

theorem growth (n : Nat) : run0 table (150+64*n) (family n) = some (family (n+1)) := by
  have H := (join0 (join0 (join0 (join0 (join0 (join0 (join0 (join0 (join0 (join0 (join0 (join0 (join0 (join0 (join0 (join0 (phase0 n) (phase1 n)) (phase2 n)) (phase3 n)) (phase4 n)) (phase5 n)) (phase6 n)) (phase7 n)) (phase8 n)) (phase9 n)) (phase10 n)) (phase11 n)) (phase12 n)) (phase13 n)) (phase14 n)) (phase15 n)) (phase16 n))
  rw [show 2+8*n+9+8*n+13+8*n+24+8*n+14+8*n+13+8*n+17+8*n+42+8*n+16=150+64*n by omega] at H
  simpa only [family,rep,List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using H

theorem never (m : Machine) (hm : compatible table m) : NeverHalts m :=
  never_of_growth table family 109 (fun n => 150+64*n) entry (by intro n; omega) growth m hm

#print axioms never

end M959

namespace M1281

-- 1RB0RE_1RC1RB_0RD1LF_1LD0RA_---1LB_1LA0LF

def table : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 0,true => some (some ⟨false,true,4⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 1,true => some (some ⟨true,true,1⟩)
  | 2,false => some (some ⟨false,true,3⟩)
  | 2,true => some (some ⟨true,false,5⟩)
  | 3,false => some (some ⟨true,false,3⟩)
  | 3,true => some (some ⟨false,true,0⟩)
  | 4,true => some (some ⟨true,false,1⟩)
  | 5,false => some (some ⟨true,false,0⟩)
  | 5,true => some (some ⟨false,false,5⟩)
  | _,_ => none

def family (n : Nat) : Z0 := ⟨1,([false,true,true,true,false,false,true,true,true,false,false,true,true,true,false,false,true,true,true]) ++ (rep [false,false,true,true,true,false,false,true,true,true,false,false,true,true,true] (n)),[]⟩

theorem entry : run0 table 206 ⟨0,[],[]⟩ = some (family 0) := by rfl

theorem phase0 (n : Nat) : run0 table 15 ⟨1,([false,true,true,true,false,false,true,true,true,false,false,true,true,true,false,false,true,true,true]) ++ (rep [false,false,true,true,true,false,false,true,true,true,false,false,true,true,true] (n)),[]⟩ = some ⟨5,([true,true,true,false,false,true,true,true,false,false,true,true,true,false,false,true,true,true]) ++ (rep [false,false,true,true,true,false,false,true,true,true,false,false,true,true,true] (n)),([true,false,true])⟩ := by rfl

theorem local1 (L R : List Bool) : run0 table 69 ⟨5,([true,true,true,false,false,true,true,true,false,false,true,true,true,false,false,true,true,true]) ++ ([false,false,true,true,true,false,false,true,true,true,false,false,true,true,true]) ++ (L),(R)⟩ = some ⟨5,([true,true,true,false,false,true,true,true,false,false,true,true,true,false,false,true,true,true]) ++ (L),([false,false,true,false,true,false,false,true,false,true,false,false,true,false,true]) ++ (R)⟩ := by rfl

theorem phase1 (n : Nat) : run0 table (69*n) ⟨5,([true,true,true,false,false,true,true,true,false,false,true,true,true,false,false,true,true,true]) ++ (rep [false,false,true,true,true,false,false,true,true,true,false,false,true,true,true] (n)),([true,false,true])⟩ = some ⟨5,([true,true,true,false,false,true,true,true,false,false,true,true,true,false,false,true,true,true]),(rep [false,false,true,false,true,false,false,true,false,true,false,false,true,false,true] (n)) ++ ([true,false,true])⟩ := by
  simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using sweepL table 5 [true,true,true,false,false,true,true,true,false,false,true,true,true,false,false,true,true,true] [] [false,false,true,true,true,false,false,true,true,true,false,false,true,true,true] [false,false,true,false,true,false,false,true,false,true,false,false,true,false,true] 69 local1 n ([]) (([true,false,true]))

theorem phase2 (n : Nat) : run0 table 94 ⟨5,([true,true,true,false,false,true,true,true,false,false,true,true,true,false,false,true,true,true]),(rep [false,false,true,false,true,false,false,true,false,true,false,false,true,false,true] (n)) ++ ([true,false,true])⟩ = some ⟨1,([true,true]),([false,false,true,false,true,false,false,true,false,true,false,false,true,false,true,false,false,true,false,true]) ++ (rep [false,false,true,false,true,false,false,true,false,true,false,false,true,false,true] (n)) ++ ([true,false,true])⟩ := by rfl

theorem local3 (L R : List Bool) : run0 table 15 ⟨1,([true]) ++ (L),([false,false,true,false,true,false,false,true,false,true,false,false,true,false,true,false,false,true,false,true]) ++ ([false,false,true,false,true,false,false,true,false,true,false,false,true,false,true]) ++ (R)⟩ = some ⟨1,([true]) ++ ([true,false,false,true,true,true,false,false,true,true,true,false,false,true,true]) ++ (L),([false,false,true,false,true,false,false,true,false,true,false,false,true,false,true,false,false,true,false,true]) ++ (R)⟩ := by rfl

theorem phase3 (n : Nat) : run0 table (15*n) ⟨1,([true,true]),([false,false,true,false,true,false,false,true,false,true,false,false,true,false,true,false,false,true,false,true]) ++ (rep [false,false,true,false,true,false,false,true,false,true,false,false,true,false,true] (n)) ++ ([true,false,true])⟩ = some ⟨1,([true]) ++ (rep [true,false,false,true,true,true,false,false,true,true,true,false,false,true,true] (n)) ++ ([true]),([false,false,true,false,true,false,false,true,false,true,false,false,true,false,true,false,false,true,false,true,true,false,true])⟩ := by
  simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using sweepR table 1 [true] [false,false,true,false,true,false,false,true,false,true,false,false,true,false,true,false,false,true,false,true] [false,false,true,false,true,false,false,true,false,true,false,false,true,false,true] [true,false,false,true,true,true,false,false,true,true,true,false,false,true,true] 15 local3 n (([true])) (([true,false,true]))

theorem phase4 (n : Nat) : run0 table 24 ⟨1,([true]) ++ (rep [true,false,false,true,true,true,false,false,true,true,true,false,false,true,true] (n)) ++ ([true]),([false,false,true,false,true,false,false,true,false,true,false,false,true,false,true,false,false,true,false,true,true,false,true])⟩ = some ⟨5,([true,true,true,true,false,false,true,true,true,false,false,true,true,true,false,false,true,true,true,false,false,true,true]) ++ (rep [true,false,false,true,true,true,false,false,true,true,true,false,false,true,true] (n)) ++ ([true]),([true])⟩ := by rfl

theorem local5 (L R : List Bool) : run0 table 69 ⟨5,([true,true,true,true,false,false,true,true,true,false,false,true,true,true,false,false,true,true,true,false,false,true,true]) ++ ([true,false,false,true,true,true,false,false,true,true,true,false,false,true,true]) ++ (L),(R)⟩ = some ⟨5,([true,true,true,true,false,false,true,true,true,false,false,true,true,true,false,false,true,true,true,false,false,true,true]) ++ (L),([false,true,false,true,false,false,true,false,true,false,false,true,false,true,false]) ++ (R)⟩ := by rfl

theorem phase5 (n : Nat) : run0 table (69*n) ⟨5,([true,true,true,true,false,false,true,true,true,false,false,true,true,true,false,false,true,true,true,false,false,true,true]) ++ (rep [true,false,false,true,true,true,false,false,true,true,true,false,false,true,true] (n)) ++ ([true]),([true])⟩ = some ⟨5,([true,true,true,true,false,false,true,true,true,false,false,true,true,true,false,false,true,true,true,false,false,true,true,true]),(rep [false,true,false,true,false,false,true,false,true,false,false,true,false,true,false] (n)) ++ ([true])⟩ := by
  simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using sweepL table 5 [true,true,true,true,false,false,true,true,true,false,false,true,true,true,false,false,true,true,true,false,false,true,true] [] [true,false,false,true,true,true,false,false,true,true,true,false,false,true,true] [false,true,false,true,false,false,true,false,true,false,false,true,false,true,false] 69 local5 n (([true])) (([true]))

theorem phase6 (n : Nat) : run0 table 118 ⟨5,([true,true,true,true,false,false,true,true,true,false,false,true,true,true,false,false,true,true,true,false,false,true,true,true]),(rep [false,true,false,true,false,false,true,false,true,false,false,true,false,true,false] (n)) ++ ([true])⟩ = some ⟨1,([true,true]),([false,false,true,false,true,false,false,true,false,true,false,false,true,false,true,false,false,true,false,true,false,false,true,false,true,false]) ++ (rep [false,true,false,true,false,false,true,false,true,false,false,true,false,true,false] (n)) ++ ([true])⟩ := by rfl

theorem local7 (L R : List Bool) : run0 table 15 ⟨1,([true]) ++ (L),([false,false,true,false,true,false,false,true,false,true,false,false,true,false,true,false,false,true,false,true,false,false,true,false,true,false]) ++ ([false,true,false,true,false,false,true,false,true,false,false,true,false,true,false]) ++ (R)⟩ = some ⟨1,([true]) ++ ([true,false,false,true,true,true,false,false,true,true,true,false,false,true,true]) ++ (L),([false,false,true,false,true,false,false,true,false,true,false,false,true,false,true,false,false,true,false,true,false,false,true,false,true,false]) ++ (R)⟩ := by rfl

theorem phase7 (n : Nat) : run0 table (15*n) ⟨1,([true,true]),([false,false,true,false,true,false,false,true,false,true,false,false,true,false,true,false,false,true,false,true,false,false,true,false,true,false]) ++ (rep [false,true,false,true,false,false,true,false,true,false,false,true,false,true,false] (n)) ++ ([true])⟩ = some ⟨1,([true]) ++ (rep [true,false,false,true,true,true,false,false,true,true,true,false,false,true,true] (n)) ++ ([true]),([false,false,true,false,true,false,false,true,false,true,false,false,true,false,true,false,false,true,false,true,false,false,true,false,true,false,true])⟩ := by
  simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using sweepR table 1 [true] [false,false,true,false,true,false,false,true,false,true,false,false,true,false,true,false,false,true,false,true,false,false,true,false,true,false] [false,true,false,true,false,false,true,false,true,false,false,true,false,true,false] [true,false,false,true,true,true,false,false,true,true,true,false,false,true,true] 15 local7 n (([true])) (([true]))

theorem phase8 (n : Nat) : run0 table 28 ⟨1,([true]) ++ (rep [true,false,false,true,true,true,false,false,true,true,true,false,false,true,true] (n)) ++ ([true]),([false,false,true,false,true,false,false,true,false,true,false,false,true,false,true,false,false,true,false,true,false,false,true,false,true,false,true])⟩ = some ⟨5,([true,true,true,false,false,true,true,true,false,false,true,true,true,false,false,true,true,true,false,false,true,true,true,false,false,true,true]) ++ (rep [true,false,false,true,true,true,false,false,true,true,true,false,false,true,true] (n)) ++ ([true]),([true])⟩ := by rfl

theorem local9 (L R : List Bool) : run0 table 69 ⟨5,([true,true,true,false,false,true,true,true,false,false,true,true,true,false,false,true,true,true,false,false,true,true,true,false,false,true,true]) ++ ([true,false,false,true,true,true,false,false,true,true,true,false,false,true,true]) ++ (L),(R)⟩ = some ⟨5,([true,true,true,false,false,true,true,true,false,false,true,true,true,false,false,true,true,true,false,false,true,true,true,false,false,true,true]) ++ (L),([false,false,true,false,true,false,false,true,false,true,false,false,true,false,true]) ++ (R)⟩ := by rfl

theorem phase9 (n : Nat) : run0 table (69*n) ⟨5,([true,true,true,false,false,true,true,true,false,false,true,true,true,false,false,true,true,true,false,false,true,true,true,false,false,true,true]) ++ (rep [true,false,false,true,true,true,false,false,true,true,true,false,false,true,true] (n)) ++ ([true]),([true])⟩ = some ⟨5,([true,true,true,false,false,true,true,true,false,false,true,true,true,false,false,true,true,true,false,false,true,true,true,false,false,true,true,true]),(rep [false,false,true,false,true,false,false,true,false,true,false,false,true,false,true] (n)) ++ ([true])⟩ := by
  simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using sweepL table 5 [true,true,true,false,false,true,true,true,false,false,true,true,true,false,false,true,true,true,false,false,true,true,true,false,false,true,true] [] [true,false,false,true,true,true,false,false,true,true,true,false,false,true,true] [false,false,true,false,true,false,false,true,false,true,false,false,true,false,true] 69 local9 n (([true])) (([true]))

theorem phase10 (n : Nat) : run0 table 140 ⟨5,([true,true,true,false,false,true,true,true,false,false,true,true,true,false,false,true,true,true,false,false,true,true,true,false,false,true,true,true]),(rep [false,false,true,false,true,false,false,true,false,true,false,false,true,false,true] (n)) ++ ([true])⟩ = some ⟨1,([true,true]),([false,false,true,false,true,false,false,true,false,true,false,false,true,false,true,false,false,true,false,true,false,false,true,false,true,false,false,true,false,true]) ++ (rep [false,false,true,false,true,false,false,true,false,true,false,false,true,false,true] (n)) ++ ([true])⟩ := by rfl

theorem local11 (L R : List Bool) : run0 table 15 ⟨1,([true]) ++ (L),([false,false,true,false,true,false,false,true,false,true,false,false,true,false,true,false,false,true,false,true,false,false,true,false,true,false,false,true,false,true]) ++ ([false,false,true,false,true,false,false,true,false,true,false,false,true,false,true]) ++ (R)⟩ = some ⟨1,([true]) ++ ([true,false,false,true,true,true,false,false,true,true,true,false,false,true,true]) ++ (L),([false,false,true,false,true,false,false,true,false,true,false,false,true,false,true,false,false,true,false,true,false,false,true,false,true,false,false,true,false,true]) ++ (R)⟩ := by rfl

theorem phase11 (n : Nat) : run0 table (15*n) ⟨1,([true,true]),([false,false,true,false,true,false,false,true,false,true,false,false,true,false,true,false,false,true,false,true,false,false,true,false,true,false,false,true,false,true]) ++ (rep [false,false,true,false,true,false,false,true,false,true,false,false,true,false,true] (n)) ++ ([true])⟩ = some ⟨1,([true]) ++ (rep [true,false,false,true,true,true,false,false,true,true,true,false,false,true,true] (n)) ++ ([true]),([false,false,true,false,true,false,false,true,false,true,false,false,true,false,true,false,false,true,false,true,false,false,true,false,true,false,false,true,false,true,true])⟩ := by
  simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using sweepR table 1 [true] [false,false,true,false,true,false,false,true,false,true,false,false,true,false,true,false,false,true,false,true,false,false,true,false,true,false,false,true,false,true] [false,false,true,false,true,false,false,true,false,true,false,false,true,false,true] [true,false,false,true,true,true,false,false,true,true,true,false,false,true,true] 15 local11 n (([true])) (([true]))

theorem phase12 (n : Nat) : run0 table 32 ⟨1,([true]) ++ (rep [true,false,false,true,true,true,false,false,true,true,true,false,false,true,true] (n)) ++ ([true]),([false,false,true,false,true,false,false,true,false,true,false,false,true,false,true,false,false,true,false,true,false,false,true,false,true,false,false,true,false,true,true])⟩ = some ⟨1,([false,true,true,true,false,false,true,true,true,false,false,true,true,true,false,false,true,true,true,false,false,true,true,true,false,false,true,true,true,false,false,true,true]) ++ (rep [true,false,false,true,true,true,false,false,true,true,true,false,false,true,true] (n)) ++ ([true]),[]⟩ := by rfl

theorem finalL (n : Nat) : ([false,true,true,true,false,false,true,true,true,false,false,true,true,true,false,false,true,true,true,false,false,true,true,true,false,false,true,true,true,false,false,true,true]) ++ (rep [true,false,false,true,true,true,false,false,true,true,true,false,false,true,true] (n)) ++ ([true]) = ([false,true,true,true,false,false,true,true,true,false,false,true,true,true,false,false,true,true,true,false,false,true,true,true,false,false,true,true,true,false,false,true,true,true]) ++ (rep [false,false,true,true,true,false,false,true,true,true,false,false,true,true,true] (n)) := by
  calc
    _ = ([false,true,true,true,false,false,true,true,true,false,false,true,true,true,false,false,true,true,true,false,false,true,true,true,false,false,true,true,true,false,false,true,true,true]) ++ (rep [false,false,true,true,true,false,false,true,true,true,false,false,true,true,true] (n)) := by symm; simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using moveCut (([false,true,true,true,false,false,true,true,true,false,false,true,true,true,false,false,true,true,true,false,false,true,true,true,false,false,true,true,true,false,false,true,true])) ([]) [false,false,true,true,true,false,false,true,true,true,false,false,true,true] true n

theorem finalR (n : Nat) : ([] : List Bool) = [] := by
  rfl

theorem growth (n : Nat) : run0 table (451+252*n) (family n) = some (family (n+1)) := by
  have H := (join0 (join0 (join0 (join0 (join0 (join0 (join0 (join0 (join0 (join0 (join0 (join0 (phase0 n) (phase1 n)) (phase2 n)) (phase3 n)) (phase4 n)) (phase5 n)) (phase6 n)) (phase7 n)) (phase8 n)) (phase9 n)) (phase10 n)) (phase11 n)) (phase12 n))
  rw [finalL n] at H
  rw [show 15+69*n+94+15*n+24+69*n+118+15*n+28+69*n+140+15*n+32=451+252*n by omega] at H
  simpa only [family,rep,List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using H

theorem never (m : Machine) (hm : compatible table m) : NeverHalts m :=
  never_of_growth table family 206 (fun n => 451+252*n) entry (by intro n; omega) growth m hm

#print axioms never

end M1281

namespace M1303

-- 1RB0RE_1RC1LF_0RD1RD_1LD0RA_0LE1LB_0LA---

def table : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 0,true => some (some ⟨false,true,4⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 1,true => some (some ⟨true,false,5⟩)
  | 2,false => some (some ⟨false,true,3⟩)
  | 2,true => some (some ⟨true,true,3⟩)
  | 3,false => some (some ⟨true,false,3⟩)
  | 3,true => some (some ⟨false,true,0⟩)
  | 4,false => some (some ⟨false,false,4⟩)
  | 4,true => some (some ⟨true,false,1⟩)
  | 5,false => some (some ⟨false,false,0⟩)
  | _,_ => none

def family (n : Nat) : Z0 := ⟨3,([false,true,true,false,true]) ++ (rep [false,true,true,true] (n)),[]⟩

theorem entry : run0 table 10 ⟨0,[],[]⟩ = some (family 0) := by rfl

theorem phase0 (n : Nat) : run0 table 13 ⟨3,([false,true,true,false,true]) ++ (rep [false,true,true,true] (n)),[]⟩ = some ⟨4,([false,false,true,true]) ++ (rep [false,true,true,true] (n)),([false,false])⟩ := by rfl

theorem local1 (L R : List Bool) : run0 table 6 ⟨4,([false,false,true,true]) ++ ([false,true,true,true]) ++ (L),(R)⟩ = some ⟨4,([false,false,true,true]) ++ (L),([true,true,false,false]) ++ (R)⟩ := by rfl

theorem phase1 (n : Nat) : run0 table (6*n) ⟨4,([false,false,true,true]) ++ (rep [false,true,true,true] (n)),([false,false])⟩ = some ⟨4,([false,false,true,true]),(rep [true,true,false,false] (n)) ++ ([false,false])⟩ := by
  simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using sweepL table 4 [false,false,true,true] [] [false,true,true,true] [true,true,false,false] 6 local1 n ([]) (([false,false]))

theorem phase2 (n : Nat) : run0 table 6 ⟨4,([false,false,true,true]),(rep [true,true,false,false] (n)) ++ ([false,false])⟩ = some ⟨1,([false,true]),([true,true,false,false]) ++ (rep [true,true,false,false] (n)) ++ ([false,false])⟩ := by rfl

theorem local3 (L R : List Bool) : run0 table 4 ⟨1,([false]) ++ (L),([true,true,false,false]) ++ ([true,true,false,false]) ++ (R)⟩ = some ⟨1,([false]) ++ ([true,false,true,true]) ++ (L),([true,true,false,false]) ++ (R)⟩ := by rfl

theorem phase3 (n : Nat) : run0 table (4*n) ⟨1,([false,true]),([true,true,false,false]) ++ (rep [true,true,false,false] (n)) ++ ([false,false])⟩ = some ⟨1,([false]) ++ (rep [true,false,true,true] (n)) ++ ([true]),([true,true,false,false,false,false])⟩ := by
  simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using sweepR table 1 [false] [true,true,false,false] [true,true,false,false] [true,false,true,true] 4 local3 n (([true])) (([false,false]))

theorem phase4 (n : Nat) : run0 table 13 ⟨1,([false]) ++ (rep [true,false,true,true] (n)) ++ ([true]),([true,true,false,false,false,false])⟩ = some ⟨3,([false,true,true,false,true,false,true,true]) ++ (rep [true,false,true,true] (n)) ++ ([true]),[]⟩ := by rfl

theorem finalL (n : Nat) : ([false,true,true,false,true,false,true,true]) ++ (rep [true,false,true,true] (n)) ++ ([true]) = ([false,true,true,false,true,false,true,true,true]) ++ (rep [false,true,true,true] (n)) := by
  calc
    _ = ([false,true,true,false,true,false,true,true,true]) ++ (rep [false,true,true,true] (n)) := by symm; simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using moveCut (([false,true,true,false,true,false,true,true])) ([]) [false,true,true] true n

theorem finalR (n : Nat) : ([] : List Bool) = [] := by
  rfl

theorem growth (n : Nat) : run0 table (32+10*n) (family n) = some (family (n+1)) := by
  have H := (join0 (join0 (join0 (join0 (phase0 n) (phase1 n)) (phase2 n)) (phase3 n)) (phase4 n))
  rw [finalL n] at H
  rw [show 13+6*n+6+4*n+13=32+10*n by omega] at H
  simpa only [family,rep,List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using H

theorem never (m : Machine) (hm : compatible table m) : NeverHalts m :=
  never_of_growth table family 10 (fun n => 32+10*n) entry (by intro n; omega) growth m hm

#print axioms never

end M1303

namespace M1394

-- 1RB0RE_1RC1LF_0RD0RC_1LD0RA_0LF1LE_0LB---

def table : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 0,true => some (some ⟨false,true,4⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 1,true => some (some ⟨true,false,5⟩)
  | 2,false => some (some ⟨false,true,3⟩)
  | 2,true => some (some ⟨false,true,2⟩)
  | 3,false => some (some ⟨true,false,3⟩)
  | 3,true => some (some ⟨false,true,0⟩)
  | 4,false => some (some ⟨false,false,5⟩)
  | 4,true => some (some ⟨true,false,4⟩)
  | 5,false => some (some ⟨false,false,1⟩)
  | _,_ => none

def family (n : Nat) : Z0 := ⟨2,([false,false]) ++ (rep [false] (n)) ++ ([true,true,false,false,true]) ++ (rep [true] (n)),[]⟩

theorem entry : run0 table 18 ⟨0,[],[]⟩ = some (family 0) := by rfl

theorem phase0 (n : Nat) : run0 table 1 ⟨2,([false,false]) ++ (rep [false] (n)) ++ ([true,true,false,false,true]) ++ (rep [true] (n)),[]⟩ = some ⟨3,([false,false,false]) ++ (rep [false] (n)) ++ ([true,true,false,false,true]) ++ (rep [true] (n)),[]⟩ := by rfl

theorem local1 (L R : List Bool) : run0 table 1 ⟨3,([false,false,false]) ++ ([false]) ++ (L),(R)⟩ = some ⟨3,([false,false,false]) ++ (L),([true]) ++ (R)⟩ := by rfl

theorem phase1 (n : Nat) : run0 table (1*n) ⟨3,([false,false,false]) ++ (rep [false] (n)) ++ ([true,true,false,false,true]) ++ (rep [true] (n)),[]⟩ = some ⟨3,([false,false,false,true,true,false,false,true]) ++ (rep [true] (n)),(rep [true] (n))⟩ := by
  simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using sweepL table 3 [false,false,false] [] [false] [true] 1 local1 n (([true,true,false,false,true]) ++ (rep [true] (n))) ([])

theorem phase2 (n : Nat) : run0 table 15 ⟨3,([false,false,false,true,true,false,false,true]) ++ (rep [true] (n)),(rep [true] (n))⟩ = some ⟨2,([true,true,true,false,false,true,true]) ++ (rep [true] (n)),([true]) ++ (rep [true] (n))⟩ := by rfl

theorem local3 (L R : List Bool) : run0 table 1 ⟨2,([true]) ++ (L),([true]) ++ ([true]) ++ (R)⟩ = some ⟨2,([true]) ++ ([false]) ++ (L),([true]) ++ (R)⟩ := by rfl

theorem phase3 (n : Nat) : run0 table (1*n) ⟨2,([true,true,true,false,false,true,true]) ++ (rep [true] (n)),([true]) ++ (rep [true] (n))⟩ = some ⟨2,([true]) ++ (rep [false] (n)) ++ ([true,true,false,false,true,true]) ++ (rep [true] (n)),([true])⟩ := by
  simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using sweepR table 2 [true] [true] [true] [false] 1 local3 n (([true,true,false,false,true,true]) ++ (rep [true] (n))) ([])

theorem phase4 (n : Nat) : run0 table 2 ⟨2,([true]) ++ (rep [false] (n)) ++ ([true,true,false,false,true,true]) ++ (rep [true] (n)),([true])⟩ = some ⟨2,([false,false,false]) ++ (rep [false] (n)) ++ ([true,true,false,false,true,true]) ++ (rep [true] (n)),[]⟩ := by rfl

theorem finalL (n : Nat) : ([false,false,false]) ++ (rep [false] (n)) ++ ([true,true,false,false,true,true]) ++ (rep [true] (n)) = ([false,false,false]) ++ (rep [false] (n)) ++ ([true,true,false,false,true,true]) ++ (rep [true] (n)) := by
  rfl

theorem finalR (n : Nat) : ([] : List Bool) = [] := by
  rfl

theorem growth (n : Nat) : run0 table (18+2*n) (family n) = some (family (n+1)) := by
  have H := (join0 (join0 (join0 (join0 (phase0 n) (phase1 n)) (phase2 n)) (phase3 n)) (phase4 n))
  rw [show 1+1*n+15+1*n+2=18+2*n by omega] at H
  simpa only [family,rep,List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using H

theorem never (m : Machine) (hm : compatible table m) : NeverHalts m :=
  never_of_growth table family 18 (fun n => 18+2*n) entry (by intro n; omega) growth m hm

#print axioms never

end M1394

namespace M1411

-- 1RB0RE_1RC1LF_0RD---_1LD0RA_0LF1LE_1LA0LB

def table : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 0,true => some (some ⟨false,true,4⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 1,true => some (some ⟨true,false,5⟩)
  | 2,false => some (some ⟨false,true,3⟩)
  | 3,false => some (some ⟨true,false,3⟩)
  | 3,true => some (some ⟨false,true,0⟩)
  | 4,false => some (some ⟨false,false,5⟩)
  | 4,true => some (some ⟨true,false,4⟩)
  | 5,false => some (some ⟨true,false,0⟩)
  | 5,true => some (some ⟨false,false,1⟩)
  | _,_ => none

def family (n : Nat) : Z0 := ⟨5,[],([false,true]) ++ (rep [false,true] (n)) ++ (rep [true,false,true,false,true] (n)) ++ ([false,true])⟩

theorem entry : run0 table 13 ⟨0,[],[]⟩ = some (family 0) := by rfl

theorem phase0 (n : Nat) : run0 table 5 ⟨5,[],([false,true]) ++ (rep [false,true] (n)) ++ (rep [true,false,true,false,true] (n)) ++ ([false,true])⟩ = some ⟨2,([false,true]),([true,false,true]) ++ (rep [false,true] (n)) ++ (rep [true,false,true,false,true] (n)) ++ ([false,true])⟩ := by rfl

theorem local1 (L R : List Bool) : run0 table 6 ⟨2,([false]) ++ (L),([true,false,true]) ++ ([false,true]) ++ (R)⟩ = some ⟨2,([false]) ++ ([true,false]) ++ (L),([true,false,true]) ++ (R)⟩ := by rfl

theorem phase1 (n : Nat) : run0 table (6*n) ⟨2,([false,true]),([true,false,true]) ++ (rep [false,true] (n)) ++ (rep [true,false,true,false,true] (n)) ++ ([false,true])⟩ = some ⟨2,([false]) ++ (rep [true,false] (n)) ++ ([true]),([true,false,true]) ++ (rep [true,false,true,false,true] (n)) ++ ([false,true])⟩ := by
  simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using sweepR table 2 [false] [true,false,true] [false,true] [true,false] 6 local1 n (([true])) ((rep [true,false,true,false,true] (n)) ++ ([false,true]))

theorem local2 (L R : List Bool) : run0 table 21 ⟨2,([false]) ++ (L),([true,false,true]) ++ ([true,false,true,false,true]) ++ (R)⟩ = some ⟨2,([false]) ++ ([true,false,true,true,false]) ++ (L),([true,false,true]) ++ (R)⟩ := by rfl

theorem phase2 (n : Nat) : run0 table (21*n) ⟨2,([false]) ++ (rep [true,false] (n)) ++ ([true]),([true,false,true]) ++ (rep [true,false,true,false,true] (n)) ++ ([false,true])⟩ = some ⟨2,([false]) ++ (rep [true,false,true,true,false] (n)) ++ (rep [true,false] (n)) ++ ([true]),([true,false,true,false,true])⟩ := by
  simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using sweepR table 2 [false] [true,false,true] [true,false,true,false,true] [true,false,true,true,false] 21 local2 n ((rep [true,false] (n)) ++ ([true])) (([false,true]))

theorem phase3 (n : Nat) : run0 table 33 ⟨2,([false]) ++ (rep [true,false,true,true,false] (n)) ++ (rep [true,false] (n)) ++ ([true]),([true,false,true,false,true])⟩ = some ⟨0,([true,false]) ++ (rep [true,false,true,true,false] (n)) ++ (rep [true,false] (n)) ++ ([true]),([true,true,false,true,false,true,false,true])⟩ := by rfl

theorem local4 (L R : List Bool) : run0 table 17 ⟨0,([true,false]) ++ ([true,false,true,true,false]) ++ (L),([true]) ++ (R)⟩ = some ⟨0,([true,false]) ++ (L),([true]) ++ ([true,false,true,false,true]) ++ (R)⟩ := by rfl

theorem phase4 (n : Nat) : run0 table (17*n) ⟨0,([true,false]) ++ (rep [true,false,true,true,false] (n)) ++ (rep [true,false] (n)) ++ ([true]),([true,true,false,true,false,true,false,true])⟩ = some ⟨0,([true,false]) ++ (rep [true,false] (n)) ++ ([true]),([true]) ++ (rep [true,false,true,false,true] (n)) ++ ([true,false,true,false,true,false,true])⟩ := by
  simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using sweepL table 0 [true,false] [true] [true,false,true,true,false] [true,false,true,false,true] 17 local4 n ((rep [true,false] (n)) ++ ([true])) (([true,false,true,false,true,false,true]))

theorem local5 (L R : List Bool) : run0 table 4 ⟨0,([true,false]) ++ ([true,false]) ++ (L),([true]) ++ (R)⟩ = some ⟨0,([true,false]) ++ (L),([true]) ++ ([false,true]) ++ (R)⟩ := by rfl

theorem phase5 (n : Nat) : run0 table (4*n) ⟨0,([true,false]) ++ (rep [true,false] (n)) ++ ([true]),([true]) ++ (rep [true,false,true,false,true] (n)) ++ ([true,false,true,false,true,false,true])⟩ = some ⟨0,([true,false,true]),([true]) ++ (rep [false,true] (n)) ++ (rep [true,false,true,false,true] (n)) ++ ([true,false,true,false,true,false,true])⟩ := by
  simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using sweepL table 0 [true,false] [true] [true,false] [false,true] 4 local5 n (([true])) ((rep [true,false,true,false,true] (n)) ++ ([true,false,true,false,true,false,true]))

theorem phase6 (n : Nat) : run0 table 7 ⟨0,([true,false,true]),([true]) ++ (rep [false,true] (n)) ++ (rep [true,false,true,false,true] (n)) ++ ([true,false,true,false,true,false,true])⟩ = some ⟨5,[],([false,true,false,true]) ++ (rep [false,true] (n)) ++ (rep [true,false,true,false,true] (n)) ++ ([true,false,true,false,true,false,true])⟩ := by rfl

theorem finalL (n : Nat) : ([] : List Bool) = [] := by
  rfl

theorem finalR (n : Nat) : ([false,true,false,true]) ++ (rep [false,true] (n)) ++ (rep [true,false,true,false,true] (n)) ++ ([true,false,true,false,true,false,true]) = ([false,true,false,true]) ++ (rep [false,true] (n)) ++ ([true,false,true,false,true]) ++ (rep [true,false,true,false,true] (n)) ++ ([false,true]) := by
  calc
    _ = ([false,true,false]) ++ (rep [true,false] (n)) ++ ([true]) ++ (rep [true,false,true,false,true] (n)) ++ ([true,false,true,false,true,false,true]) := by simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using moveCut (([false,true,false])) ((rep [true,false,true,false,true] (n)) ++ ([true,false,true,false,true,false,true])) [false] true n
    _ = ([false,true]) ++ (rep [false,true] (n)) ++ ([false,true]) ++ (rep [true,false,true,false,true] (n)) ++ ([true,false,true,false,true,false,true]) := by simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using moveCut (([false,true])) (([true]) ++ (rep [true,false,true,false,true] (n)) ++ ([true,false,true,false,true,false,true])) [true] false n
    _ = ([false]) ++ (rep [true,false] (n)) ++ ([true,false,true]) ++ (rep [true,false,true,false,true] (n)) ++ ([true,false,true,false,true,false,true]) := by simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using moveCut (([false])) (([false,true]) ++ (rep [true,false,true,false,true] (n)) ++ ([true,false,true,false,true,false,true])) [false] true n
    _ = (rep [false,true] (n)) ++ ([false,true,false,true]) ++ (rep [true,false,true,false,true] (n)) ++ ([true,false,true,false,true,false,true]) := by simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using moveCut ([]) (([true,false,true]) ++ (rep [true,false,true,false,true] (n)) ++ ([true,false,true,false,true,false,true])) [true] false n
    _ = (rep [false,true] (n)) ++ ([false,true,false,true,true]) ++ (rep [false,true,false,true,true] (n)) ++ ([false,true,false,true,false,true]) := by symm; simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using moveCut ((rep [false,true] (n)) ++ ([false,true,false,true])) (([false,true,false,true,false,true])) [false,true,false,true] true n
    _ = (rep [false,true] (n)) ++ ([false,true,false,true,true,false]) ++ (rep [true,false,true,true,false] (n)) ++ ([true,false,true,false,true]) := by symm; simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using moveCut ((rep [false,true] (n)) ++ ([false,true,false,true,true])) (([true,false,true,false,true])) [true,false,true,true] false n
    _ = (rep [false,true] (n)) ++ ([false,true,false,true,true,false,true]) ++ (rep [false,true,true,false,true] (n)) ++ ([false,true,false,true]) := by symm; simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using moveCut ((rep [false,true] (n)) ++ ([false,true,false,true,true,false])) (([false,true,false,true])) [false,true,true,false] true n
    _ = (rep [false,true] (n)) ++ ([false,true,false,true,true,false,true,false]) ++ (rep [true,true,false,true,false] (n)) ++ ([true,false,true]) := by symm; simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using moveCut ((rep [false,true] (n)) ++ ([false,true,false,true,true,false,true])) (([true,false,true])) [true,true,false,true] false n
    _ = (rep [false,true] (n)) ++ ([false,true,false,true,true,false,true,false,true]) ++ (rep [true,false,true,false,true] (n)) ++ ([false,true]) := by symm; simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using moveCut ((rep [false,true] (n)) ++ ([false,true,false,true,true,false,true,false])) (([false,true])) [true,false,true,false] true n
    _ = ([false]) ++ (rep [true,false] (n)) ++ ([true,false,true,true,false,true,false,true]) ++ (rep [true,false,true,false,true] (n)) ++ ([false,true]) := by symm; simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using moveCut ([]) (([true,false,true,true,false,true,false,true]) ++ (rep [true,false,true,false,true] (n)) ++ ([false,true])) [true] false n
    _ = ([false,true]) ++ (rep [false,true] (n)) ++ ([false,true,true,false,true,false,true]) ++ (rep [true,false,true,false,true] (n)) ++ ([false,true]) := by symm; simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using moveCut (([false])) (([false,true,true,false,true,false,true]) ++ (rep [true,false,true,false,true] (n)) ++ ([false,true])) [false] true n
    _ = ([false,true,false]) ++ (rep [true,false] (n)) ++ ([true,true,false,true,false,true]) ++ (rep [true,false,true,false,true] (n)) ++ ([false,true]) := by symm; simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using moveCut (([false,true])) (([true,true,false,true,false,true]) ++ (rep [true,false,true,false,true] (n)) ++ ([false,true])) [true] false n
    _ = ([false,true,false,true]) ++ (rep [false,true] (n)) ++ ([true,false,true,false,true]) ++ (rep [true,false,true,false,true] (n)) ++ ([false,true]) := by symm; simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using moveCut (([false,true,false])) (([true,false,true,false,true]) ++ (rep [true,false,true,false,true] (n)) ++ ([false,true])) [false] true n

theorem growth (n : Nat) : run0 table (45+48*n) (family n) = some (family (n+1)) := by
  have H := (join0 (join0 (join0 (join0 (join0 (join0 (phase0 n) (phase1 n)) (phase2 n)) (phase3 n)) (phase4 n)) (phase5 n)) (phase6 n))
  rw [finalR n] at H
  rw [show 5+6*n+21*n+33+17*n+4*n+7=45+48*n by omega] at H
  simpa only [family,rep,List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using H

theorem never (m : Machine) (hm : compatible table m) : NeverHalts m :=
  never_of_growth table family 13 (fun n => 45+48*n) entry (by intro n; omega) growth m hm

#print axioms never

end M1411

end BB6.Agent11Raw39B0REPumps
