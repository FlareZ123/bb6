import SweepPumping
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedVariables false
namespace BB6.Agent11Raw39B1RCPumps
open BB6Coverage BB6Coverage.Agent31Pump


namespace M324

-- 1RB1RC_1RC1LE_0RD0LF_1LD0RA_1LF---_0LB1LE

def table : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 0,true => some (some ⟨true,true,2⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 1,true => some (some ⟨true,false,4⟩)
  | 2,false => some (some ⟨false,true,3⟩)
  | 2,true => some (some ⟨false,false,5⟩)
  | 3,false => some (some ⟨true,false,3⟩)
  | 3,true => some (some ⟨false,true,0⟩)
  | 4,false => some (some ⟨true,false,5⟩)
  | 5,false => some (some ⟨false,false,1⟩)
  | 5,true => some (some ⟨true,false,4⟩)
  | _,_ => none

def family (n : Nat) : Z0 := ⟨1,([false,true]) ++ (rep [false,false,true,false,false,true,false,false,true] (n)),[]⟩

theorem entry : run0 table 1 ⟨0,[],[]⟩ = some (family 0) := by rfl

theorem phase0 (n : Nat) : run0 table 10 ⟨1,([false,true]) ++ (rep [false,false,true,false,false,true,false,false,true] (n)),[]⟩ = some ⟨4,(rep [false,false,true,false,false,true,false,false,true] (n)),([true,true,true,false])⟩ := by rfl

theorem local1 (L R : List Bool) : run0 table 9 ⟨4,([false,false,true,false,false,true,false,false,true]) ++ (L),(R)⟩ = some ⟨4,(L),([true,false,true,true,false,true,true,false,true]) ++ (R)⟩ := by rfl

theorem phase1 (n : Nat) : run0 table (9*n) ⟨4,(rep [false,false,true,false,false,true,false,false,true] (n)),([true,true,true,false])⟩ = some ⟨4,[],(rep [true,false,true,true,false,true,true,false,true] (n)) ++ ([true,true,true,false])⟩ := by
  simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using sweepL table 4 [] [] [false,false,true,false,false,true,false,false,true] [true,false,true,true,false,true,true,false,true] 9 local1 n ([]) (([true,true,true,false]))

theorem phase2 (n : Nat) : run0 table 3 ⟨4,[],(rep [true,false,true,true,false,true,true,false,true] (n)) ++ ([true,true,true,false])⟩ = some ⟨2,([false,true]),([true]) ++ (rep [true,false,true,true,false,true,true,false,true] (n)) ++ ([true,true,true,false])⟩ := by rfl

theorem local3 (L R : List Bool) : run0 table 9 ⟨2,([false]) ++ (L),([true]) ++ ([true,false,true,true,false,true,true,false,true]) ++ (R)⟩ = some ⟨2,([false]) ++ ([true,false,false,true,false,false,true,false,false]) ++ (L),([true]) ++ (R)⟩ := by rfl

theorem phase3 (n : Nat) : run0 table (9*n) ⟨2,([false,true]),([true]) ++ (rep [true,false,true,true,false,true,true,false,true] (n)) ++ ([true,true,true,false])⟩ = some ⟨2,([false]) ++ (rep [true,false,false,true,false,false,true,false,false] (n)) ++ ([true]),([true,true,true,true,false])⟩ := by
  simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using sweepR table 2 [false] [true] [true,false,true,true,false,true,true,false,true] [true,false,false,true,false,false,true,false,false] 9 local3 n (([true])) (([true,true,true,false]))

theorem phase4 (n : Nat) : run0 table 5 ⟨2,([false]) ++ (rep [true,false,false,true,false,false,true,false,false] (n)) ++ ([true]),([true,true,true,true,false])⟩ = some ⟨4,([false,false]) ++ (rep [true,false,false,true,false,false,true,false,false] (n)) ++ ([true]),([true,false,true,false])⟩ := by rfl

theorem local5 (L R : List Bool) : run0 table 9 ⟨4,([false,false]) ++ ([true,false,false,true,false,false,true,false,false]) ++ (L),(R)⟩ = some ⟨4,([false,false]) ++ (L),([true,false,true,true,false,true,true,false,true]) ++ (R)⟩ := by rfl

theorem phase5 (n : Nat) : run0 table (9*n) ⟨4,([false,false]) ++ (rep [true,false,false,true,false,false,true,false,false] (n)) ++ ([true]),([true,false,true,false])⟩ = some ⟨4,([false,false,true]),(rep [true,false,true,true,false,true,true,false,true] (n)) ++ ([true,false,true,false])⟩ := by
  simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using sweepL table 4 [false,false] [] [true,false,false,true,false,false,true,false,false] [true,false,true,true,false,true,true,false,true] 9 local5 n (([true])) (([true,false,true,false]))

theorem phase6 (n : Nat) : run0 table 6 ⟨4,([false,false,true]),(rep [true,false,true,true,false,true,true,false,true] (n)) ++ ([true,false,true,false])⟩ = some ⟨2,([false,true]),([true,true,false,true]) ++ (rep [true,false,true,true,false,true,true,false,true] (n)) ++ ([true,false,true,false])⟩ := by rfl

theorem local7 (L R : List Bool) : run0 table 9 ⟨2,([false]) ++ (L),([true,true,false,true]) ++ ([true,false,true,true,false,true,true,false,true]) ++ (R)⟩ = some ⟨2,([false]) ++ ([true,false,false,true,false,false,true,false,false]) ++ (L),([true,true,false,true]) ++ (R)⟩ := by rfl

theorem phase7 (n : Nat) : run0 table (9*n) ⟨2,([false,true]),([true,true,false,true]) ++ (rep [true,false,true,true,false,true,true,false,true] (n)) ++ ([true,false,true,false])⟩ = some ⟨2,([false]) ++ (rep [true,false,false,true,false,false,true,false,false] (n)) ++ ([true]),([true,true,false,true,true,false,true,false])⟩ := by
  simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using sweepR table 2 [false] [true,true,false,true] [true,false,true,true,false,true,true,false,true] [true,false,false,true,false,false,true,false,false] 9 local7 n (([true])) (([true,false,true,false]))

theorem phase8 (n : Nat) : run0 table 9 ⟨2,([false]) ++ (rep [true,false,false,true,false,false,true,false,false] (n)) ++ ([true]),([true,true,false,true,true,false,true,false])⟩ = some ⟨1,([false,true,false,false,true,false,false,true,false,false]) ++ (rep [true,false,false,true,false,false,true,false,false] (n)) ++ ([true]),[]⟩ := by rfl

theorem finalL (n : Nat) : ([false,true,false,false,true,false,false,true,false,false]) ++ (rep [true,false,false,true,false,false,true,false,false] (n)) ++ ([true]) = ([false,true,false,false,true,false,false,true,false,false,true]) ++ (rep [false,false,true,false,false,true,false,false,true] (n)) := by
  calc
    _ = ([false,true,false,false,true,false,false,true,false,false,true]) ++ (rep [false,false,true,false,false,true,false,false,true] (n)) := by symm; simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using moveCut (([false,true,false,false,true,false,false,true,false,false])) ([]) [false,false,true,false,false,true,false,false] true n

theorem finalR (n : Nat) : ([] : List Bool) = [] := by
  rfl

theorem growth (n : Nat) : run0 table (33+36*n) (family n) = some (family (n+1)) := by
  have H := (join0 (join0 (join0 (join0 (join0 (join0 (join0 (join0 (phase0 n) (phase1 n)) (phase2 n)) (phase3 n)) (phase4 n)) (phase5 n)) (phase6 n)) (phase7 n)) (phase8 n))
  rw [finalL n] at H
  rw [show 10+9*n+3+9*n+5+9*n+6+9*n+9=33+36*n by omega] at H
  simpa only [family,rep,List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using H

theorem never (m : Machine) (hm : compatible table m) : NeverHalts m :=
  never_of_growth table family 1 (fun n => 33+36*n) entry (by intro n; omega) growth m hm

#print axioms never

end M324

namespace M325

-- 1RB1RC_1RC0LA_0RD0LF_1LD0RA_1LF---_1LA1LE

def table : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 0,true => some (some ⟨true,true,2⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 1,true => some (some ⟨false,false,0⟩)
  | 2,false => some (some ⟨false,true,3⟩)
  | 2,true => some (some ⟨false,false,5⟩)
  | 3,false => some (some ⟨true,false,3⟩)
  | 3,true => some (some ⟨false,true,0⟩)
  | 4,false => some (some ⟨true,false,5⟩)
  | 5,false => some (some ⟨true,false,0⟩)
  | 5,true => some (some ⟨true,false,4⟩)
  | _,_ => none

def family (n : Nat) : Z0 := ⟨1,([false,true]) ++ (rep [false,false,true,false,false,true,false,false,true] (n)),[]⟩

theorem entry : run0 table 1 ⟨0,[],[]⟩ = some (family 0) := by rfl

theorem phase0 (n : Nat) : run0 table 9 ⟨1,([false,true]) ++ (rep [false,false,true,false,false,true,false,false,true] (n)),[]⟩ = some ⟨5,([true]) ++ (rep [false,false,true,false,false,true,false,false,true] (n)),([true,true,false])⟩ := by rfl

theorem local1 (L R : List Bool) : run0 table 15 ⟨5,([true]) ++ ([false,false,true,false,false,true,false,false,true]) ++ (L),(R)⟩ = some ⟨5,([true]) ++ (L),([false,true,true,false,true,true,false,true,true]) ++ (R)⟩ := by rfl

theorem phase1 (n : Nat) : run0 table (15*n) ⟨5,([true]) ++ (rep [false,false,true,false,false,true,false,false,true] (n)),([true,true,false])⟩ = some ⟨5,([true]),(rep [false,true,true,false,true,true,false,true,true] (n)) ++ ([true,true,false])⟩ := by
  simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using sweepL table 5 [true] [] [false,false,true,false,false,true,false,false,true] [false,true,true,false,true,true,false,true,true] 15 local1 n ([]) (([true,true,false]))

theorem phase2 (n : Nat) : run0 table 5 ⟨5,([true]),(rep [false,true,true,false,true,true,false,true,true] (n)) ++ ([true,true,false])⟩ = some ⟨0,([true]),([false,true,true]) ++ (rep [false,true,true,false,true,true,false,true,true] (n)) ++ ([true,true,false])⟩ := by rfl

theorem local3 (L R : List Bool) : run0 table 9 ⟨0,([true]) ++ (L),([false,true,true]) ++ ([false,true,true,false,true,true,false,true,true]) ++ (R)⟩ = some ⟨0,([true]) ++ ([false,false,true,false,false,true,false,false,true]) ++ (L),([false,true,true]) ++ (R)⟩ := by rfl

theorem phase3 (n : Nat) : run0 table (9*n) ⟨0,([true]),([false,true,true]) ++ (rep [false,true,true,false,true,true,false,true,true] (n)) ++ ([true,true,false])⟩ = some ⟨0,([true]) ++ (rep [false,false,true,false,false,true,false,false,true] (n)),([false,true,true,true,true,false])⟩ := by
  simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using sweepR table 0 [true] [false,true,true] [false,true,true,false,true,true,false,true,true] [false,false,true,false,false,true,false,false,true] 9 local3 n ([]) (([true,true,false]))

theorem phase4 (n : Nat) : run0 table 3 ⟨0,([true]) ++ (rep [false,false,true,false,false,true,false,false,true] (n)),([false,true,true,true,true,false])⟩ = some ⟨0,([true,false,false,true]) ++ (rep [false,false,true,false,false,true,false,false,true] (n)),([true,true,false])⟩ := by rfl

theorem local5 (L R : List Bool) : run0 table 15 ⟨0,([true,false,false,true]) ++ ([false,false,true,false,false,true,false,false,true]) ++ (L),([true]) ++ (R)⟩ = some ⟨0,([true,false,false,true]) ++ (L),([true]) ++ ([true,true,false,true,true,false,true,true,false]) ++ (R)⟩ := by rfl

theorem phase5 (n : Nat) : run0 table (15*n) ⟨0,([true,false,false,true]) ++ (rep [false,false,true,false,false,true,false,false,true] (n)),([true,true,false])⟩ = some ⟨0,([true,false,false,true]),([true]) ++ (rep [true,true,false,true,true,false,true,true,false] (n)) ++ ([true,false])⟩ := by
  simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using sweepL table 0 [true,false,false,true] [true] [false,false,true,false,false,true,false,false,true] [true,true,false,true,true,false,true,true,false] 15 local5 n ([]) (([true,false]))

theorem phase6 (n : Nat) : run0 table 12 ⟨0,([true,false,false,true]),([true]) ++ (rep [true,true,false,true,true,false,true,true,false] (n)) ++ ([true,false])⟩ = some ⟨0,([true]),([false,true,true,false,true,true,false]) ++ (rep [true,true,false,true,true,false,true,true,false] (n)) ++ ([true,false])⟩ := by rfl

theorem local7 (L R : List Bool) : run0 table 9 ⟨0,([true]) ++ (L),([false,true,true,false,true,true,false]) ++ ([true,true,false,true,true,false,true,true,false]) ++ (R)⟩ = some ⟨0,([true]) ++ ([false,false,true,false,false,true,false,false,true]) ++ (L),([false,true,true,false,true,true,false]) ++ (R)⟩ := by rfl

theorem phase7 (n : Nat) : run0 table (9*n) ⟨0,([true]),([false,true,true,false,true,true,false]) ++ (rep [true,true,false,true,true,false,true,true,false] (n)) ++ ([true,false])⟩ = some ⟨0,([true]) ++ (rep [false,false,true,false,false,true,false,false,true] (n)),([false,true,true,false,true,true,false,true,false])⟩ := by
  simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using sweepR table 0 [true] [false,true,true,false,true,true,false] [true,true,false,true,true,false,true,true,false] [false,false,true,false,false,true,false,false,true] 9 local7 n ([]) (([true,false]))

theorem phase8 (n : Nat) : run0 table 10 ⟨0,([true]) ++ (rep [false,false,true,false,false,true,false,false,true] (n)),([false,true,true,false,true,true,false,true,false])⟩ = some ⟨1,([false,true,false,false,true,false,false,true,false,false,true]) ++ (rep [false,false,true,false,false,true,false,false,true] (n)),[]⟩ := by rfl

theorem finalL (n : Nat) : ([false,true,false,false,true,false,false,true,false,false,true]) ++ (rep [false,false,true,false,false,true,false,false,true] (n)) = ([false,true,false,false,true,false,false,true,false,false,true]) ++ (rep [false,false,true,false,false,true,false,false,true] (n)) := by
  rfl

theorem finalR (n : Nat) : ([] : List Bool) = [] := by
  rfl

theorem growth (n : Nat) : run0 table (39+48*n) (family n) = some (family (n+1)) := by
  have H := (join0 (join0 (join0 (join0 (join0 (join0 (join0 (join0 (phase0 n) (phase1 n)) (phase2 n)) (phase3 n)) (phase4 n)) (phase5 n)) (phase6 n)) (phase7 n)) (phase8 n))
  rw [show 9+15*n+5+9*n+3+15*n+12+9*n+10=39+48*n by omega] at H
  simpa only [family,rep,List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using H

theorem never (m : Machine) (hm : compatible table m) : NeverHalts m :=
  never_of_growth table family 1 (fun n => 39+48*n) entry (by intro n; omega) growth m hm

#print axioms never

end M325

namespace M326

-- 1RB1RC_1RC0RD_0RD0LF_1LD0RA_1LF---_1LA1LE

def table : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 0,true => some (some ⟨true,true,2⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 1,true => some (some ⟨false,true,3⟩)
  | 2,false => some (some ⟨false,true,3⟩)
  | 2,true => some (some ⟨false,false,5⟩)
  | 3,false => some (some ⟨true,false,3⟩)
  | 3,true => some (some ⟨false,true,0⟩)
  | 4,false => some (some ⟨true,false,5⟩)
  | 5,false => some (some ⟨true,false,0⟩)
  | 5,true => some (some ⟨true,false,4⟩)
  | _,_ => none

def family (n : Nat) : Z0 := ⟨1,([false,true]) ++ (rep [false,false,true,false,false,true,false,false,true] (n)),[]⟩

theorem entry : run0 table 1 ⟨0,[],[]⟩ = some (family 0) := by rfl

theorem phase0 (n : Nat) : run0 table 9 ⟨1,([false,true]) ++ (rep [false,false,true,false,false,true,false,false,true] (n)),[]⟩ = some ⟨5,([true]) ++ (rep [false,false,true,false,false,true,false,false,true] (n)),([true,true,false])⟩ := by rfl

theorem local1 (L R : List Bool) : run0 table 15 ⟨5,([true]) ++ ([false,false,true,false,false,true,false,false,true]) ++ (L),(R)⟩ = some ⟨5,([true]) ++ (L),([false,true,true,false,true,true,false,true,true]) ++ (R)⟩ := by rfl

theorem phase1 (n : Nat) : run0 table (15*n) ⟨5,([true]) ++ (rep [false,false,true,false,false,true,false,false,true] (n)),([true,true,false])⟩ = some ⟨5,([true]),(rep [false,true,true,false,true,true,false,true,true] (n)) ++ ([true,true,false])⟩ := by
  simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using sweepL table 5 [true] [] [false,false,true,false,false,true,false,false,true] [false,true,true,false,true,true,false,true,true] 15 local1 n ([]) (([true,true,false]))

theorem phase2 (n : Nat) : run0 table 5 ⟨5,([true]),(rep [false,true,true,false,true,true,false,true,true] (n)) ++ ([true,true,false])⟩ = some ⟨3,([true,false,true]),([true]) ++ (rep [false,true,true,false,true,true,false,true,true] (n)) ++ ([true,true,false])⟩ := by rfl

theorem local3 (L R : List Bool) : run0 table 9 ⟨3,([true]) ++ (L),([true]) ++ ([false,true,true,false,true,true,false,true,true]) ++ (R)⟩ = some ⟨3,([true]) ++ ([false,true,false,false,true,false,false,true,false]) ++ (L),([true]) ++ (R)⟩ := by rfl

theorem phase3 (n : Nat) : run0 table (9*n) ⟨3,([true,false,true]),([true]) ++ (rep [false,true,true,false,true,true,false,true,true] (n)) ++ ([true,true,false])⟩ = some ⟨3,([true]) ++ (rep [false,true,false,false,true,false,false,true,false] (n)) ++ ([false,true]),([true,true,true,false])⟩ := by
  simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using sweepR table 3 [true] [true] [false,true,true,false,true,true,false,true,true] [false,true,false,false,true,false,false,true,false] 9 local3 n (([false,true])) (([true,true,false]))

theorem phase4 (n : Nat) : run0 table 1 ⟨3,([true]) ++ (rep [false,true,false,false,true,false,false,true,false] (n)) ++ ([false,true]),([true,true,true,false])⟩ = some ⟨0,([true,false]) ++ (rep [false,true,false,false,true,false,false,true,false] (n)) ++ ([false,true]),([true,true,false])⟩ := by rfl

theorem local5 (L R : List Bool) : run0 table 15 ⟨0,([true,false]) ++ ([false,true,false,false,true,false,false,true,false]) ++ (L),([true]) ++ (R)⟩ = some ⟨0,([true,false]) ++ (L),([true]) ++ ([true,true,false,true,true,false,true,true,false]) ++ (R)⟩ := by rfl

theorem phase5 (n : Nat) : run0 table (15*n) ⟨0,([true,false]) ++ (rep [false,true,false,false,true,false,false,true,false] (n)) ++ ([false,true]),([true,true,false])⟩ = some ⟨0,([true,false,false,true]),([true]) ++ (rep [true,true,false,true,true,false,true,true,false] (n)) ++ ([true,false])⟩ := by
  simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using sweepL table 0 [true,false] [true] [false,true,false,false,true,false,false,true,false] [true,true,false,true,true,false,true,true,false] 15 local5 n (([false,true])) (([true,false]))

theorem phase6 (n : Nat) : run0 table 12 ⟨0,([true,false,false,true]),([true]) ++ (rep [true,true,false,true,true,false,true,true,false] (n)) ++ ([true,false])⟩ = some ⟨3,([true,false,true]),([true,false,true,true,false]) ++ (rep [true,true,false,true,true,false,true,true,false] (n)) ++ ([true,false])⟩ := by rfl

theorem local7 (L R : List Bool) : run0 table 9 ⟨3,([true]) ++ (L),([true,false,true,true,false]) ++ ([true,true,false,true,true,false,true,true,false]) ++ (R)⟩ = some ⟨3,([true]) ++ ([false,true,false,false,true,false,false,true,false]) ++ (L),([true,false,true,true,false]) ++ (R)⟩ := by rfl

theorem phase7 (n : Nat) : run0 table (9*n) ⟨3,([true,false,true]),([true,false,true,true,false]) ++ (rep [true,true,false,true,true,false,true,true,false] (n)) ++ ([true,false])⟩ = some ⟨3,([true]) ++ (rep [false,true,false,false,true,false,false,true,false] (n)) ++ ([false,true]),([true,false,true,true,false,true,false])⟩ := by
  simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using sweepR table 3 [true] [true,false,true,true,false] [true,true,false,true,true,false,true,true,false] [false,true,false,false,true,false,false,true,false] 9 local7 n (([false,true])) (([true,false]))

theorem phase8 (n : Nat) : run0 table 8 ⟨3,([true]) ++ (rep [false,true,false,false,true,false,false,true,false] (n)) ++ ([false,true]),([true,false,true,true,false,true,false])⟩ = some ⟨1,([false,true,false,false,true,false,false,true,false]) ++ (rep [false,true,false,false,true,false,false,true,false] (n)) ++ ([false,true]),[]⟩ := by rfl

theorem finalL (n : Nat) : ([false,true,false,false,true,false,false,true,false]) ++ (rep [false,true,false,false,true,false,false,true,false] (n)) ++ ([false,true]) = ([false,true,false,false,true,false,false,true,false,false,true]) ++ (rep [false,false,true,false,false,true,false,false,true] (n)) := by
  calc
    _ = ([false,true,false,false,true,false,false,true,false,false]) ++ (rep [true,false,false,true,false,false,true,false,false] (n)) ++ ([true]) := by symm; simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using moveCut (([false,true,false,false,true,false,false,true,false])) (([true])) [true,false,false,true,false,false,true,false] false n
    _ = ([false,true,false,false,true,false,false,true,false,false,true]) ++ (rep [false,false,true,false,false,true,false,false,true] (n)) := by symm; simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using moveCut (([false,true,false,false,true,false,false,true,false,false])) ([]) [false,false,true,false,false,true,false,false] true n

theorem finalR (n : Nat) : ([] : List Bool) = [] := by
  rfl

theorem growth (n : Nat) : run0 table (35+48*n) (family n) = some (family (n+1)) := by
  have H := (join0 (join0 (join0 (join0 (join0 (join0 (join0 (join0 (phase0 n) (phase1 n)) (phase2 n)) (phase3 n)) (phase4 n)) (phase5 n)) (phase6 n)) (phase7 n)) (phase8 n))
  rw [finalL n] at H
  rw [show 9+15*n+5+9*n+1+15*n+12+9*n+8=35+48*n by omega] at H
  simpa only [family,rep,List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using H

theorem never (m : Machine) (hm : compatible table m) : NeverHalts m :=
  never_of_growth table family 1 (fun n => 35+48*n) entry (by intro n; omega) growth m hm

#print axioms never

end M326

namespace M330

-- 1RB1RC_1RC1LE_0RD0LF_1LD0RA_1LF---_0LB1LF

def table : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 0,true => some (some ⟨true,true,2⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 1,true => some (some ⟨true,false,4⟩)
  | 2,false => some (some ⟨false,true,3⟩)
  | 2,true => some (some ⟨false,false,5⟩)
  | 3,false => some (some ⟨true,false,3⟩)
  | 3,true => some (some ⟨false,true,0⟩)
  | 4,false => some (some ⟨true,false,5⟩)
  | 5,false => some (some ⟨false,false,1⟩)
  | 5,true => some (some ⟨true,false,5⟩)
  | _,_ => none

def family (n : Nat) : Z0 := ⟨1,([false,true]) ++ (rep [false,false,true,false,false,true] (n)),[]⟩

theorem entry : run0 table 1 ⟨0,[],[]⟩ = some (family 0) := by rfl

theorem phase0 (n : Nat) : run0 table 8 ⟨1,([false,true]) ++ (rep [false,false,true,false,false,true] (n)),[]⟩ = some ⟨5,([false,true]) ++ (rep [false,false,true,false,false,true] (n)),([true,false])⟩ := by rfl

theorem local1 (L R : List Bool) : run0 table 6 ⟨5,([false,true]) ++ ([false,false,true,false,false,true]) ++ (L),(R)⟩ = some ⟨5,([false,true]) ++ (L),([true,true,false,true,true,false]) ++ (R)⟩ := by rfl

theorem phase1 (n : Nat) : run0 table (6*n) ⟨5,([false,true]) ++ (rep [false,false,true,false,false,true] (n)),([true,false])⟩ = some ⟨5,([false,true]),(rep [true,true,false,true,true,false] (n)) ++ ([true,false])⟩ := by
  simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using sweepL table 5 [false,true] [] [false,false,true,false,false,true] [true,true,false,true,true,false] 6 local1 n ([]) (([true,false]))

theorem phase2 (n : Nat) : run0 table 5 ⟨5,([false,true]),(rep [true,true,false,true,true,false] (n)) ++ ([true,false])⟩ = some ⟨2,([false,true]),([true,true,false]) ++ (rep [true,true,false,true,true,false] (n)) ++ ([true,false])⟩ := by rfl

theorem local3 (L R : List Bool) : run0 table 6 ⟨2,([false]) ++ (L),([true,true,false]) ++ ([true,true,false,true,true,false]) ++ (R)⟩ = some ⟨2,([false]) ++ ([true,false,false,true,false,false]) ++ (L),([true,true,false]) ++ (R)⟩ := by rfl

theorem phase3 (n : Nat) : run0 table (6*n) ⟨2,([false,true]),([true,true,false]) ++ (rep [true,true,false,true,true,false] (n)) ++ ([true,false])⟩ = some ⟨2,([false]) ++ (rep [true,false,false,true,false,false] (n)) ++ ([true]),([true,true,false,true,false])⟩ := by
  simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using sweepR table 2 [false] [true,true,false] [true,true,false,true,true,false] [true,false,false,true,false,false] 6 local3 n (([true])) (([true,false]))

theorem phase4 (n : Nat) : run0 table 6 ⟨2,([false]) ++ (rep [true,false,false,true,false,false] (n)) ++ ([true]),([true,true,false,true,false])⟩ = some ⟨1,([false,true,false,false,true,false,false]) ++ (rep [true,false,false,true,false,false] (n)) ++ ([true]),[]⟩ := by rfl

theorem finalL (n : Nat) : ([false,true,false,false,true,false,false]) ++ (rep [true,false,false,true,false,false] (n)) ++ ([true]) = ([false,true,false,false,true,false,false,true]) ++ (rep [false,false,true,false,false,true] (n)) := by
  calc
    _ = ([false,true,false,false,true,false,false,true]) ++ (rep [false,false,true,false,false,true] (n)) := by symm; simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using moveCut (([false,true,false,false,true,false,false])) ([]) [false,false,true,false,false] true n

theorem finalR (n : Nat) : ([] : List Bool) = [] := by
  rfl

theorem growth (n : Nat) : run0 table (19+12*n) (family n) = some (family (n+1)) := by
  have H := (join0 (join0 (join0 (join0 (phase0 n) (phase1 n)) (phase2 n)) (phase3 n)) (phase4 n))
  rw [finalL n] at H
  rw [show 8+6*n+5+6*n+6=19+12*n by omega] at H
  simpa only [family,rep,List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using H

theorem never (m : Machine) (hm : compatible table m) : NeverHalts m :=
  never_of_growth table family 1 (fun n => 19+12*n) entry (by intro n; omega) growth m hm

#print axioms never

end M330

namespace M331

-- 1RB1RC_1RC1LE_0RD0LF_1LD0RA_1RF---_0LB1LF

def table : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 0,true => some (some ⟨true,true,2⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 1,true => some (some ⟨true,false,4⟩)
  | 2,false => some (some ⟨false,true,3⟩)
  | 2,true => some (some ⟨false,false,5⟩)
  | 3,false => some (some ⟨true,false,3⟩)
  | 3,true => some (some ⟨false,true,0⟩)
  | 4,false => some (some ⟨true,true,5⟩)
  | 5,false => some (some ⟨false,false,1⟩)
  | 5,true => some (some ⟨true,false,5⟩)
  | _,_ => none

def family (n : Nat) : Z0 := ⟨1,([false,true]) ++ (rep [false,false,true,false,false,true] (n)),[]⟩

theorem entry : run0 table 1 ⟨0,[],[]⟩ = some (family 0) := by rfl

theorem phase0 (n : Nat) : run0 table 7 ⟨1,([false,true]) ++ (rep [false,false,true,false,false,true] (n)),[]⟩ = some ⟨5,([true,false,true]) ++ (rep [false,false,true,false,false,true] (n)),([false])⟩ := by rfl

theorem local1 (L R : List Bool) : run0 table 10 ⟨5,([true,false,true]) ++ ([false,false,true,false,false,true]) ++ (L),(R)⟩ = some ⟨5,([true,false,true]) ++ (L),([true,false,true,true,false,true]) ++ (R)⟩ := by rfl

theorem phase1 (n : Nat) : run0 table (10*n) ⟨5,([true,false,true]) ++ (rep [false,false,true,false,false,true] (n)),([false])⟩ = some ⟨5,([true,false,true]),(rep [true,false,true,true,false,true] (n)) ++ ([false])⟩ := by
  simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using sweepL table 5 [true,false,true] [] [false,false,true,false,false,true] [true,false,true,true,false,true] 10 local1 n ([]) (([false]))

theorem phase2 (n : Nat) : run0 table 8 ⟨5,([true,false,true]),(rep [true,false,true,true,false,true] (n)) ++ ([false])⟩ = some ⟨2,([false,true]),([true,true,false,true]) ++ (rep [true,false,true,true,false,true] (n)) ++ ([false])⟩ := by rfl

theorem local3 (L R : List Bool) : run0 table 6 ⟨2,([false]) ++ (L),([true,true,false,true]) ++ ([true,false,true,true,false,true]) ++ (R)⟩ = some ⟨2,([false]) ++ ([true,false,false,true,false,false]) ++ (L),([true,true,false,true]) ++ (R)⟩ := by rfl

theorem phase3 (n : Nat) : run0 table (6*n) ⟨2,([false,true]),([true,true,false,true]) ++ (rep [true,false,true,true,false,true] (n)) ++ ([false])⟩ = some ⟨2,([false]) ++ (rep [true,false,false,true,false,false] (n)) ++ ([true]),([true,true,false,true,false])⟩ := by
  simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using sweepR table 2 [false] [true,true,false,true] [true,false,true,true,false,true] [true,false,false,true,false,false] 6 local3 n (([true])) (([false]))

theorem phase4 (n : Nat) : run0 table 6 ⟨2,([false]) ++ (rep [true,false,false,true,false,false] (n)) ++ ([true]),([true,true,false,true,false])⟩ = some ⟨1,([false,true,false,false,true,false,false]) ++ (rep [true,false,false,true,false,false] (n)) ++ ([true]),[]⟩ := by rfl

theorem finalL (n : Nat) : ([false,true,false,false,true,false,false]) ++ (rep [true,false,false,true,false,false] (n)) ++ ([true]) = ([false,true,false,false,true,false,false,true]) ++ (rep [false,false,true,false,false,true] (n)) := by
  calc
    _ = ([false,true,false,false,true,false,false,true]) ++ (rep [false,false,true,false,false,true] (n)) := by symm; simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using moveCut (([false,true,false,false,true,false,false])) ([]) [false,false,true,false,false] true n

theorem finalR (n : Nat) : ([] : List Bool) = [] := by
  rfl

theorem growth (n : Nat) : run0 table (21+16*n) (family n) = some (family (n+1)) := by
  have H := (join0 (join0 (join0 (join0 (phase0 n) (phase1 n)) (phase2 n)) (phase3 n)) (phase4 n))
  rw [finalL n] at H
  rw [show 7+10*n+8+6*n+6=21+16*n by omega] at H
  simpa only [family,rep,List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using H

theorem never (m : Machine) (hm : compatible table m) : NeverHalts m :=
  never_of_growth table family 1 (fun n => 21+16*n) entry (by intro n; omega) growth m hm

#print axioms never

end M331

namespace M339

-- 1RB1RC_1RC---_0RD0LF_1LD0RA_0RD0LA_1LE1LF

def table : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 0,true => some (some ⟨true,true,2⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 2,false => some (some ⟨false,true,3⟩)
  | 2,true => some (some ⟨false,false,5⟩)
  | 3,false => some (some ⟨true,false,3⟩)
  | 3,true => some (some ⟨false,true,0⟩)
  | 4,false => some (some ⟨false,true,3⟩)
  | 4,true => some (some ⟨false,false,0⟩)
  | 5,false => some (some ⟨true,false,4⟩)
  | 5,true => some (some ⟨true,false,5⟩)
  | _,_ => none

def family (n : Nat) : Z0 := ⟨1,([false,true,false,false,true,false,false]) ++ (rep [true,false,false] (n)) ++ ([false]),[]⟩

theorem entry : run0 table 40 ⟨0,[],[]⟩ = some (family 0) := by rfl

theorem phase0 (n : Nat) : run0 table 7 ⟨1,([false,true,false,false,true,false,false]) ++ (rep [true,false,false] (n)) ++ ([false]),[]⟩ = some ⟨5,([true,false,true,false,false,true,false,false]) ++ (rep [true,false,false] (n)) ++ ([false]),([false])⟩ := by rfl

theorem local1 (L R : List Bool) : run0 table 7 ⟨5,([true,false,true,false,false,true,false,false]) ++ ([true,false,false]) ++ (L),(R)⟩ = some ⟨5,([true,false,true,false,false,true,false,false]) ++ (L),([true,false,true]) ++ (R)⟩ := by rfl

theorem phase1 (n : Nat) : run0 table (7*n) ⟨5,([true,false,true,false,false,true,false,false]) ++ (rep [true,false,false] (n)) ++ ([false]),([false])⟩ = some ⟨5,([true,false,true,false,false,true,false,false,false]),(rep [true,false,true] (n)) ++ ([false])⟩ := by
  simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using sweepL table 5 [true,false,true,false,false,true,false,false] [] [true,false,false] [true,false,true] 7 local1 n (([false])) (([false]))

theorem phase2 (n : Nat) : run0 table 34 ⟨5,([true,false,true,false,false,true,false,false,false]),(rep [true,false,true] (n)) ++ ([false])⟩ = some ⟨3,([true,false,false]),([true,false,true,true,false,true]) ++ (rep [true,false,true] (n)) ++ ([false])⟩ := by rfl

theorem local3 (L R : List Bool) : run0 table 3 ⟨3,([true]) ++ (L),([true,false,true,true,false,true]) ++ ([true,false,true]) ++ (R)⟩ = some ⟨3,([true]) ++ ([false,true,false]) ++ (L),([true,false,true,true,false,true]) ++ (R)⟩ := by rfl

theorem phase3 (n : Nat) : run0 table (3*n) ⟨3,([true,false,false]),([true,false,true,true,false,true]) ++ (rep [true,false,true] (n)) ++ ([false])⟩ = some ⟨3,([true]) ++ (rep [false,true,false] (n)) ++ ([false,false]),([true,false,true,true,false,true,false])⟩ := by
  simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using sweepR table 3 [true] [true,false,true,true,false,true] [true,false,true] [false,true,false] 3 local3 n (([false,false])) (([false]))

theorem phase4 (n : Nat) : run0 table 8 ⟨3,([true]) ++ (rep [false,true,false] (n)) ++ ([false,false]),([true,false,true,true,false,true,false])⟩ = some ⟨1,([false,true,false,false,true,false,false,true,false]) ++ (rep [false,true,false] (n)) ++ ([false,false]),[]⟩ := by rfl

theorem finalL (n : Nat) : ([false,true,false,false,true,false,false,true,false]) ++ (rep [false,true,false] (n)) ++ ([false,false]) = ([false,true,false,false,true,false,false,true,false,false]) ++ (rep [true,false,false] (n)) ++ ([false]) := by
  calc
    _ = ([false,true,false,false,true,false,false,true,false,false]) ++ (rep [true,false,false] (n)) ++ ([false]) := by symm; simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using moveCut (([false,true,false,false,true,false,false,true,false])) (([false])) [true,false] false n

theorem finalR (n : Nat) : ([] : List Bool) = [] := by
  rfl

theorem growth (n : Nat) : run0 table (49+10*n) (family n) = some (family (n+1)) := by
  have H := (join0 (join0 (join0 (join0 (phase0 n) (phase1 n)) (phase2 n)) (phase3 n)) (phase4 n))
  rw [finalL n] at H
  rw [show 7+7*n+34+3*n+8=49+10*n by omega] at H
  simpa only [family,rep,List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using H

theorem never (m : Machine) (hm : compatible table m) : NeverHalts m :=
  never_of_growth table family 40 (fun n => 49+10*n) entry (by intro n; omega) growth m hm

#print axioms never

end M339

namespace M340

-- 1RB1RC_1RC---_0RD0LF_1LD0RA_1RE0LA_1LE1LF

def table : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 0,true => some (some ⟨true,true,2⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 2,false => some (some ⟨false,true,3⟩)
  | 2,true => some (some ⟨false,false,5⟩)
  | 3,false => some (some ⟨true,false,3⟩)
  | 3,true => some (some ⟨false,true,0⟩)
  | 4,false => some (some ⟨true,true,4⟩)
  | 4,true => some (some ⟨false,false,0⟩)
  | 5,false => some (some ⟨true,false,4⟩)
  | 5,true => some (some ⟨true,false,5⟩)
  | _,_ => none

def family (n : Nat) : Z0 := ⟨1,([false,true]) ++ (rep [false,false,true,false,false,true] (n)),[]⟩

theorem entry : run0 table 1 ⟨0,[],[]⟩ = some (family 0) := by rfl

theorem phase0 (n : Nat) : run0 table 7 ⟨1,([false,true]) ++ (rep [false,false,true,false,false,true] (n)),[]⟩ = some ⟨5,([true,false,true]) ++ (rep [false,false,true,false,false,true] (n)),([false])⟩ := by rfl

theorem local1 (L R : List Bool) : run0 table 14 ⟨5,([true,false,true]) ++ ([false,false,true,false,false,true]) ++ (L),(R)⟩ = some ⟨5,([true,false,true]) ++ (L),([true,false,true,true,false,true]) ++ (R)⟩ := by rfl

theorem phase1 (n : Nat) : run0 table (14*n) ⟨5,([true,false,true]) ++ (rep [false,false,true,false,false,true] (n)),([false])⟩ = some ⟨5,([true,false,true]),(rep [true,false,true,true,false,true] (n)) ++ ([false])⟩ := by
  simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using sweepL table 5 [true,false,true] [] [false,false,true,false,false,true] [true,false,true,true,false,true] 14 local1 n ([]) (([false]))

theorem phase2 (n : Nat) : run0 table 11 ⟨5,([true,false,true]),(rep [true,false,true,true,false,true] (n)) ++ ([false])⟩ = some ⟨0,([true]),([false,true,true,false,true]) ++ (rep [true,false,true,true,false,true] (n)) ++ ([false])⟩ := by rfl

theorem local3 (L R : List Bool) : run0 table 6 ⟨0,([true]) ++ (L),([false,true,true,false,true]) ++ ([true,false,true,true,false,true]) ++ (R)⟩ = some ⟨0,([true]) ++ ([false,false,true,false,false,true]) ++ (L),([false,true,true,false,true]) ++ (R)⟩ := by rfl

theorem phase3 (n : Nat) : run0 table (6*n) ⟨0,([true]),([false,true,true,false,true]) ++ (rep [true,false,true,true,false,true] (n)) ++ ([false])⟩ = some ⟨0,([true]) ++ (rep [false,false,true,false,false,true] (n)),([false,true,true,false,true,false])⟩ := by
  simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using sweepR table 0 [true] [false,true,true,false,true] [true,false,true,true,false,true] [false,false,true,false,false,true] 6 local3 n ([]) (([false]))

theorem phase4 (n : Nat) : run0 table 7 ⟨0,([true]) ++ (rep [false,false,true,false,false,true] (n)),([false,true,true,false,true,false])⟩ = some ⟨1,([false,true,false,false,true,false,false,true]) ++ (rep [false,false,true,false,false,true] (n)),[]⟩ := by rfl

theorem finalL (n : Nat) : ([false,true,false,false,true,false,false,true]) ++ (rep [false,false,true,false,false,true] (n)) = ([false,true,false,false,true,false,false,true]) ++ (rep [false,false,true,false,false,true] (n)) := by
  rfl

theorem finalR (n : Nat) : ([] : List Bool) = [] := by
  rfl

theorem growth (n : Nat) : run0 table (25+20*n) (family n) = some (family (n+1)) := by
  have H := (join0 (join0 (join0 (join0 (phase0 n) (phase1 n)) (phase2 n)) (phase3 n)) (phase4 n))
  rw [show 7+14*n+11+6*n+7=25+20*n by omega] at H
  simpa only [family,rep,List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using H

theorem never (m : Machine) (hm : compatible table m) : NeverHalts m :=
  never_of_growth table family 1 (fun n => 25+20*n) entry (by intro n; omega) growth m hm

#print axioms never

end M340

namespace M356

-- 1RB1RC_1RC---_0RD0LF_1LD0RA_1LC0LA_1LE1RE

def table : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 0,true => some (some ⟨true,true,2⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 2,false => some (some ⟨false,true,3⟩)
  | 2,true => some (some ⟨false,false,5⟩)
  | 3,false => some (some ⟨true,false,3⟩)
  | 3,true => some (some ⟨false,true,0⟩)
  | 4,false => some (some ⟨true,false,2⟩)
  | 4,true => some (some ⟨false,false,0⟩)
  | 5,false => some (some ⟨true,false,4⟩)
  | 5,true => some (some ⟨true,true,4⟩)
  | _,_ => none

def family (n : Nat) : Z0 := ⟨4,[],([true,false,true,true,false,true]) ++ (rep [true,false,true,true,false,true] (n))⟩

theorem entry : run0 table 23 ⟨0,[],[]⟩ = some (family 0) := by rfl

theorem phase0 (n : Nat) : run0 table 2 ⟨4,[],([true,false,true,true,false,true]) ++ (rep [true,false,true,true,false,true] (n))⟩ = some ⟨3,([true,false]),([true,false,true,true,false,true]) ++ (rep [true,false,true,true,false,true] (n))⟩ := by rfl

theorem local1 (L R : List Bool) : run0 table 6 ⟨3,([true]) ++ (L),([true,false,true,true,false,true]) ++ ([true,false,true,true,false,true]) ++ (R)⟩ = some ⟨3,([true]) ++ ([false,true,false,false,true,false]) ++ (L),([true,false,true,true,false,true]) ++ (R)⟩ := by rfl

theorem phase1 (n : Nat) : run0 table (6*n) ⟨3,([true,false]),([true,false,true,true,false,true]) ++ (rep [true,false,true,true,false,true] (n))⟩ = some ⟨3,([true]) ++ (rep [false,true,false,false,true,false] (n)) ++ ([false]),([true,false,true,true,false,true])⟩ := by
  simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using sweepR table 3 [true] [true,false,true,true,false,true] [true,false,true,true,false,true] [false,true,false,false,true,false] 6 local1 n (([false])) ([])

theorem phase2 (n : Nat) : run0 table 14 ⟨3,([true]) ++ (rep [false,true,false,false,true,false] (n)) ++ ([false]),([true,false,true,true,false,true])⟩ = some ⟨2,([true,true,false,true,false,false,true,false,false,true,false]) ++ (rep [false,true,false,false,true,false] (n)) ++ ([false]),[]⟩ := by rfl

theorem local3 (L R : List Bool) : run0 table 22 ⟨2,([true,true,false,true,false,false,true,false,false,true,false]) ++ ([false,true,false,false,true,false]) ++ (L),(R)⟩ = some ⟨2,([true,true,false,true,false,false,true,false,false,true,false]) ++ (L),([true,false,true,true,false,true]) ++ (R)⟩ := by rfl

theorem phase3 (n : Nat) : run0 table (22*n) ⟨2,([true,true,false,true,false,false,true,false,false,true,false]) ++ (rep [false,true,false,false,true,false] (n)) ++ ([false]),[]⟩ = some ⟨2,([true,true,false,true,false,false,true,false,false,true,false,false]),(rep [true,false,true,true,false,true] (n))⟩ := by
  simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using sweepL table 2 [true,true,false,true,false,false,true,false,false,true,false] [] [false,true,false,false,true,false] [true,false,true,true,false,true] 22 local3 n (([false])) ([])

theorem phase4 (n : Nat) : run0 table 38 ⟨2,([true,true,false,true,false,false,true,false,false,true,false,false]),(rep [true,false,true,true,false,true] (n))⟩ = some ⟨4,[],([true,false,true,true,false,true,true,false,true,true,false,true]) ++ (rep [true,false,true,true,false,true] (n))⟩ := by rfl

theorem finalL (n : Nat) : ([] : List Bool) = [] := by
  rfl

theorem finalR (n : Nat) : ([true,false,true,true,false,true,true,false,true,true,false,true]) ++ (rep [true,false,true,true,false,true] (n)) = ([true,false,true,true,false,true,true,false,true,true,false,true]) ++ (rep [true,false,true,true,false,true] (n)) := by
  rfl

theorem growth (n : Nat) : run0 table (54+28*n) (family n) = some (family (n+1)) := by
  have H := (join0 (join0 (join0 (join0 (phase0 n) (phase1 n)) (phase2 n)) (phase3 n)) (phase4 n))
  rw [show 2+6*n+14+22*n+38=54+28*n by omega] at H
  simpa only [family,rep,List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using H

theorem never (m : Machine) (hm : compatible table m) : NeverHalts m :=
  never_of_growth table family 23 (fun n => 54+28*n) entry (by intro n; omega) growth m hm

#print axioms never

end M356

namespace M357

-- 1RB1RC_1RC---_0RD0LF_1LD0RA_1LC1LB_1LE1RE

def table : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 0,true => some (some ⟨true,true,2⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 2,false => some (some ⟨false,true,3⟩)
  | 2,true => some (some ⟨false,false,5⟩)
  | 3,false => some (some ⟨true,false,3⟩)
  | 3,true => some (some ⟨false,true,0⟩)
  | 4,false => some (some ⟨true,false,2⟩)
  | 4,true => some (some ⟨true,false,1⟩)
  | 5,false => some (some ⟨true,false,4⟩)
  | 5,true => some (some ⟨true,true,4⟩)
  | _,_ => none

def family (n : Nat) : Z0 := ⟨4,[],([true,false,true,true,false,true]) ++ (rep [true,false,true,true,false,true] (n))⟩

theorem entry : run0 table 19 ⟨0,[],[]⟩ = some (family 0) := by rfl

theorem phase0 (n : Nat) : run0 table 2 ⟨4,[],([true,false,true,true,false,true]) ++ (rep [true,false,true,true,false,true] (n))⟩ = some ⟨3,([true,false]),([true,false,true,true,false,true]) ++ (rep [true,false,true,true,false,true] (n))⟩ := by rfl

theorem local1 (L R : List Bool) : run0 table 6 ⟨3,([true]) ++ (L),([true,false,true,true,false,true]) ++ ([true,false,true,true,false,true]) ++ (R)⟩ = some ⟨3,([true]) ++ ([false,true,false,false,true,false]) ++ (L),([true,false,true,true,false,true]) ++ (R)⟩ := by rfl

theorem phase1 (n : Nat) : run0 table (6*n) ⟨3,([true,false]),([true,false,true,true,false,true]) ++ (rep [true,false,true,true,false,true] (n))⟩ = some ⟨3,([true]) ++ (rep [false,true,false,false,true,false] (n)) ++ ([false]),([true,false,true,true,false,true])⟩ := by
  simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using sweepR table 3 [true] [true,false,true,true,false,true] [true,false,true,true,false,true] [false,true,false,false,true,false] 6 local1 n (([false])) ([])

theorem phase2 (n : Nat) : run0 table 14 ⟨3,([true]) ++ (rep [false,true,false,false,true,false] (n)) ++ ([false]),([true,false,true,true,false,true])⟩ = some ⟨2,([true,true,false,true,false,false,true,false,false,true,false]) ++ (rep [false,true,false,false,true,false] (n)) ++ ([false]),[]⟩ := by rfl

theorem local3 (L R : List Bool) : run0 table 14 ⟨2,([true,true,false,true,false,false,true,false,false,true,false]) ++ ([false,true,false,false,true,false]) ++ (L),(R)⟩ = some ⟨2,([true,true,false,true,false,false,true,false,false,true,false]) ++ (L),([true,false,true,true,false,true]) ++ (R)⟩ := by rfl

theorem phase3 (n : Nat) : run0 table (14*n) ⟨2,([true,true,false,true,false,false,true,false,false,true,false]) ++ (rep [false,true,false,false,true,false] (n)) ++ ([false]),[]⟩ = some ⟨2,([true,true,false,true,false,false,true,false,false,true,false,false]),(rep [true,false,true,true,false,true] (n))⟩ := by
  simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using sweepL table 2 [true,true,false,true,false,false,true,false,false,true,false] [] [false,true,false,false,true,false] [true,false,true,true,false,true] 14 local3 n (([false])) ([])

theorem phase4 (n : Nat) : run0 table 26 ⟨2,([true,true,false,true,false,false,true,false,false,true,false,false]),(rep [true,false,true,true,false,true] (n))⟩ = some ⟨4,[],([true,false,true,true,false,true,true,false,true,true,false,true]) ++ (rep [true,false,true,true,false,true] (n))⟩ := by rfl

theorem finalL (n : Nat) : ([] : List Bool) = [] := by
  rfl

theorem finalR (n : Nat) : ([true,false,true,true,false,true,true,false,true,true,false,true]) ++ (rep [true,false,true,true,false,true] (n)) = ([true,false,true,true,false,true,true,false,true,true,false,true]) ++ (rep [true,false,true,true,false,true] (n)) := by
  rfl

theorem growth (n : Nat) : run0 table (42+20*n) (family n) = some (family (n+1)) := by
  have H := (join0 (join0 (join0 (join0 (phase0 n) (phase1 n)) (phase2 n)) (phase3 n)) (phase4 n))
  rw [show 2+6*n+14+14*n+26=42+20*n by omega] at H
  simpa only [family,rep,List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using H

theorem never (m : Machine) (hm : compatible table m) : NeverHalts m :=
  never_of_growth table family 19 (fun n => 42+20*n) entry (by intro n; omega) growth m hm

#print axioms never

end M357

namespace M381

-- 1RB1RC_1RC0RE_0RD0LF_1LD0RA_1RF---_1LC1RF

def table : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 0,true => some (some ⟨true,true,2⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 1,true => some (some ⟨false,true,4⟩)
  | 2,false => some (some ⟨false,true,3⟩)
  | 2,true => some (some ⟨false,false,5⟩)
  | 3,false => some (some ⟨true,false,3⟩)
  | 3,true => some (some ⟨false,true,0⟩)
  | 4,false => some (some ⟨true,true,5⟩)
  | 5,false => some (some ⟨true,false,2⟩)
  | 5,true => some (some ⟨true,true,5⟩)
  | _,_ => none

def family (n : Nat) : Z0 := ⟨5,([false,true,true]) ++ (rep [true] (n)) ++ ([false,true,false,false]),[]⟩

theorem entry : run0 table 20 ⟨0,[],[]⟩ = some (family 0) := by rfl

theorem local0 (L R : List Bool) : run0 table 3 ⟨5,([false,true,true]) ++ ([true]) ++ (L),(R)⟩ = some ⟨5,([false,true,true]) ++ (L),([true]) ++ (R)⟩ := by rfl

theorem phase0 (n : Nat) : run0 table (3*n) ⟨5,([false,true,true]) ++ (rep [true] (n)) ++ ([false,true,false,false]),[]⟩ = some ⟨5,([false,true,true,false,true,false,false]),(rep [true] (n))⟩ := by
  simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using sweepL table 5 [false,true,true] [] [true] [true] 3 local0 n (([false,true,false,false])) ([])

theorem phase1 (n : Nat) : run0 table 13 ⟨5,([false,true,true,false,true,false,false]),(rep [true] (n))⟩ = some ⟨5,([true,true,false,true,false,false]),([true]) ++ (rep [true] (n))⟩ := by rfl

theorem local2 (L R : List Bool) : run0 table 1 ⟨5,([true]) ++ (L),([true]) ++ ([true]) ++ (R)⟩ = some ⟨5,([true]) ++ ([true]) ++ (L),([true]) ++ (R)⟩ := by rfl

theorem phase2 (n : Nat) : run0 table (1*n) ⟨5,([true,true,false,true,false,false]),([true]) ++ (rep [true] (n))⟩ = some ⟨5,([true]) ++ (rep [true] (n)) ++ ([true,false,true,false,false]),([true])⟩ := by
  simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using sweepR table 5 [true] [true] [true] [true] 1 local2 n (([true,false,true,false,false])) ([])

theorem phase3 (n : Nat) : run0 table 2 ⟨5,([true]) ++ (rep [true] (n)) ++ ([true,false,true,false,false]),([true])⟩ = some ⟨5,([false,true,true]) ++ (rep [true] (n)) ++ ([true,false,true,false,false]),[]⟩ := by rfl

theorem finalL (n : Nat) : ([false,true,true]) ++ (rep [true] (n)) ++ ([true,false,true,false,false]) = ([false,true,true,true]) ++ (rep [true] (n)) ++ ([false,true,false,false]) := by
  calc
    _ = ([false,true,true,true]) ++ (rep [true] (n)) ++ ([false,true,false,false]) := by symm; simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using moveCut (([false,true,true])) (([false,true,false,false])) [] true n

theorem finalR (n : Nat) : ([] : List Bool) = [] := by
  rfl

theorem growth (n : Nat) : run0 table (15+4*n) (family n) = some (family (n+1)) := by
  have H := (join0 (join0 (join0 (phase0 n) (phase1 n)) (phase2 n)) (phase3 n))
  rw [finalL n] at H
  rw [show 3*n+13+1*n+2=15+4*n by omega] at H
  simpa only [family,rep,List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using H

theorem never (m : Machine) (hm : compatible table m) : NeverHalts m :=
  never_of_growth table family 20 (fun n => 15+4*n) entry (by intro n; omega) growth m hm

#print axioms never

end M381

end BB6.Agent11Raw39B1RCPumps
