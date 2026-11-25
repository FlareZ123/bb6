import SweepPumping
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedVariables false
namespace BB6.Agent11Raw39B1RCPumps
open BB6Coverage BB6Coverage.Agent31Pump


namespace M100

-- 1RB1RC_1RC1LF_0RD0LE_1LD0RA_0LB1LE_1LE---

def table : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 0,true => some (some ⟨true,true,2⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 1,true => some (some ⟨true,false,5⟩)
  | 2,false => some (some ⟨false,true,3⟩)
  | 2,true => some (some ⟨false,false,4⟩)
  | 3,false => some (some ⟨true,false,3⟩)
  | 3,true => some (some ⟨false,true,0⟩)
  | 4,false => some (some ⟨false,false,1⟩)
  | 4,true => some (some ⟨true,false,4⟩)
  | 5,false => some (some ⟨true,false,4⟩)
  | _,_ => none

def family (n : Nat) : Z0 := ⟨1,([false,true]) ++ (rep [false,false,true,false,false,true] (n)),[]⟩

theorem entry : run0 table 1 ⟨0,[],[]⟩ = some (family 0) := by rfl

theorem phase0 (n : Nat) : run0 table 8 ⟨1,([false,true]) ++ (rep [false,false,true,false,false,true] (n)),[]⟩ = some ⟨4,([false,true]) ++ (rep [false,false,true,false,false,true] (n)),([true,false])⟩ := by rfl

theorem local1 (L R : List Bool) : run0 table 6 ⟨4,([false,true]) ++ ([false,false,true,false,false,true]) ++ (L),(R)⟩ = some ⟨4,([false,true]) ++ (L),([true,true,false,true,true,false]) ++ (R)⟩ := by rfl

theorem phase1 (n : Nat) : run0 table (6*n) ⟨4,([false,true]) ++ (rep [false,false,true,false,false,true] (n)),([true,false])⟩ = some ⟨4,([false,true]),(rep [true,true,false,true,true,false] (n)) ++ ([true,false])⟩ := by
  simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using sweepL table 4 [false,true] [] [false,false,true,false,false,true] [true,true,false,true,true,false] 6 local1 n ([]) (([true,false]))

theorem phase2 (n : Nat) : run0 table 5 ⟨4,([false,true]),(rep [true,true,false,true,true,false] (n)) ++ ([true,false])⟩ = some ⟨2,([false,true]),([true,true,false]) ++ (rep [true,true,false,true,true,false] (n)) ++ ([true,false])⟩ := by rfl

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

end M100

namespace M101

-- 1RB1RC_1RC1LF_0RD0LE_1LD0RA_0LB1LE_1RE---

def table : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 0,true => some (some ⟨true,true,2⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 1,true => some (some ⟨true,false,5⟩)
  | 2,false => some (some ⟨false,true,3⟩)
  | 2,true => some (some ⟨false,false,4⟩)
  | 3,false => some (some ⟨true,false,3⟩)
  | 3,true => some (some ⟨false,true,0⟩)
  | 4,false => some (some ⟨false,false,1⟩)
  | 4,true => some (some ⟨true,false,4⟩)
  | 5,false => some (some ⟨true,true,4⟩)
  | _,_ => none

def family (n : Nat) : Z0 := ⟨1,([false,true]) ++ (rep [false,false,true,false,false,true] (n)),[]⟩

theorem entry : run0 table 1 ⟨0,[],[]⟩ = some (family 0) := by rfl

theorem phase0 (n : Nat) : run0 table 7 ⟨1,([false,true]) ++ (rep [false,false,true,false,false,true] (n)),[]⟩ = some ⟨4,([true,false,true]) ++ (rep [false,false,true,false,false,true] (n)),([false])⟩ := by rfl

theorem local1 (L R : List Bool) : run0 table 10 ⟨4,([true,false,true]) ++ ([false,false,true,false,false,true]) ++ (L),(R)⟩ = some ⟨4,([true,false,true]) ++ (L),([true,false,true,true,false,true]) ++ (R)⟩ := by rfl

theorem phase1 (n : Nat) : run0 table (10*n) ⟨4,([true,false,true]) ++ (rep [false,false,true,false,false,true] (n)),([false])⟩ = some ⟨4,([true,false,true]),(rep [true,false,true,true,false,true] (n)) ++ ([false])⟩ := by
  simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using sweepL table 4 [true,false,true] [] [false,false,true,false,false,true] [true,false,true,true,false,true] 10 local1 n ([]) (([false]))

theorem phase2 (n : Nat) : run0 table 8 ⟨4,([true,false,true]),(rep [true,false,true,true,false,true] (n)) ++ ([false])⟩ = some ⟨2,([false,true]),([true,true,false,true]) ++ (rep [true,false,true,true,false,true] (n)) ++ ([false])⟩ := by rfl

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

end M101

namespace M109

-- 1RB1RC_1RC---_0RD0LE_1LD0RA_1LF1LE_0RD0LA

def table : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 0,true => some (some ⟨true,true,2⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 2,false => some (some ⟨false,true,3⟩)
  | 2,true => some (some ⟨false,false,4⟩)
  | 3,false => some (some ⟨true,false,3⟩)
  | 3,true => some (some ⟨false,true,0⟩)
  | 4,false => some (some ⟨true,false,5⟩)
  | 4,true => some (some ⟨true,false,4⟩)
  | 5,false => some (some ⟨false,true,3⟩)
  | 5,true => some (some ⟨false,false,0⟩)
  | _,_ => none

def family (n : Nat) : Z0 := ⟨1,([false,true,false,false,true,false,false]) ++ (rep [true,false,false] (n)) ++ ([false]),[]⟩

theorem entry : run0 table 40 ⟨0,[],[]⟩ = some (family 0) := by rfl

theorem phase0 (n : Nat) : run0 table 7 ⟨1,([false,true,false,false,true,false,false]) ++ (rep [true,false,false] (n)) ++ ([false]),[]⟩ = some ⟨4,([true,false,true,false,false,true,false,false]) ++ (rep [true,false,false] (n)) ++ ([false]),([false])⟩ := by rfl

theorem local1 (L R : List Bool) : run0 table 7 ⟨4,([true,false,true,false,false,true,false,false]) ++ ([true,false,false]) ++ (L),(R)⟩ = some ⟨4,([true,false,true,false,false,true,false,false]) ++ (L),([true,false,true]) ++ (R)⟩ := by rfl

theorem phase1 (n : Nat) : run0 table (7*n) ⟨4,([true,false,true,false,false,true,false,false]) ++ (rep [true,false,false] (n)) ++ ([false]),([false])⟩ = some ⟨4,([true,false,true,false,false,true,false,false,false]),(rep [true,false,true] (n)) ++ ([false])⟩ := by
  simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using sweepL table 4 [true,false,true,false,false,true,false,false] [] [true,false,false] [true,false,true] 7 local1 n (([false])) (([false]))

theorem phase2 (n : Nat) : run0 table 34 ⟨4,([true,false,true,false,false,true,false,false,false]),(rep [true,false,true] (n)) ++ ([false])⟩ = some ⟨3,([true,false,false]),([true,false,true,true,false,true]) ++ (rep [true,false,true] (n)) ++ ([false])⟩ := by rfl

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

end M109

namespace M110

-- 1RB1RC_1RC---_0RD0LE_1LD0RA_1LF1LE_1RF0LA

def table : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 0,true => some (some ⟨true,true,2⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 2,false => some (some ⟨false,true,3⟩)
  | 2,true => some (some ⟨false,false,4⟩)
  | 3,false => some (some ⟨true,false,3⟩)
  | 3,true => some (some ⟨false,true,0⟩)
  | 4,false => some (some ⟨true,false,5⟩)
  | 4,true => some (some ⟨true,false,4⟩)
  | 5,false => some (some ⟨true,true,5⟩)
  | 5,true => some (some ⟨false,false,0⟩)
  | _,_ => none

def family (n : Nat) : Z0 := ⟨1,([false,true]) ++ (rep [false,false,true,false,false,true] (n)),[]⟩

theorem entry : run0 table 1 ⟨0,[],[]⟩ = some (family 0) := by rfl

theorem phase0 (n : Nat) : run0 table 7 ⟨1,([false,true]) ++ (rep [false,false,true,false,false,true] (n)),[]⟩ = some ⟨4,([true,false,true]) ++ (rep [false,false,true,false,false,true] (n)),([false])⟩ := by rfl

theorem local1 (L R : List Bool) : run0 table 14 ⟨4,([true,false,true]) ++ ([false,false,true,false,false,true]) ++ (L),(R)⟩ = some ⟨4,([true,false,true]) ++ (L),([true,false,true,true,false,true]) ++ (R)⟩ := by rfl

theorem phase1 (n : Nat) : run0 table (14*n) ⟨4,([true,false,true]) ++ (rep [false,false,true,false,false,true] (n)),([false])⟩ = some ⟨4,([true,false,true]),(rep [true,false,true,true,false,true] (n)) ++ ([false])⟩ := by
  simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using sweepL table 4 [true,false,true] [] [false,false,true,false,false,true] [true,false,true,true,false,true] 14 local1 n ([]) (([false]))

theorem phase2 (n : Nat) : run0 table 11 ⟨4,([true,false,true]),(rep [true,false,true,true,false,true] (n)) ++ ([false])⟩ = some ⟨0,([true]),([false,true,true,false,true]) ++ (rep [true,false,true,true,false,true] (n)) ++ ([false])⟩ := by rfl

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

end M110

namespace M120

-- 1RB1RC_1RC0LF_0RD0LE_1LD0RA_---1LF_0LB1LC

def table : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 0,true => some (some ⟨true,true,2⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 1,true => some (some ⟨false,false,5⟩)
  | 2,false => some (some ⟨false,true,3⟩)
  | 2,true => some (some ⟨false,false,4⟩)
  | 3,false => some (some ⟨true,false,3⟩)
  | 3,true => some (some ⟨false,true,0⟩)
  | 4,true => some (some ⟨true,false,5⟩)
  | 5,false => some (some ⟨false,false,1⟩)
  | 5,true => some (some ⟨true,false,2⟩)
  | _,_ => none

def family (n : Nat) : Z0 := ⟨1,([false,true]) ++ (rep [false,false,true,false,false,true] (n)),[]⟩

theorem entry : run0 table 1 ⟨0,[],[]⟩ = some (family 0) := by rfl

theorem phase0 (n : Nat) : run0 table 2 ⟨1,([false,true]) ++ (rep [false,false,true,false,false,true] (n)),[]⟩ = some ⟨3,([false,false,true,true]) ++ (rep [false,false,true,false,false,true] (n)),[]⟩ := by rfl

theorem local1 (L R : List Bool) : run0 table 22 ⟨3,([false,false,true,true]) ++ ([false,false,true,false,false,true]) ++ (L),(R)⟩ = some ⟨3,([false,false,true,true]) ++ (L),([false,true,false,false,true,false]) ++ (R)⟩ := by rfl

theorem phase1 (n : Nat) : run0 table (22*n) ⟨3,([false,false,true,true]) ++ (rep [false,false,true,false,false,true] (n)),[]⟩ = some ⟨3,([false,false,true,true]),(rep [false,true,false,false,true,false] (n))⟩ := by
  simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using sweepL table 3 [false,false,true,true] [] [false,false,true,false,false,true] [false,true,false,false,true,false] 22 local1 n ([]) ([])

theorem phase2 (n : Nat) : run0 table 19 ⟨3,([false,false,true,true]),(rep [false,true,false,false,true,false] (n))⟩ = some ⟨2,([false,true]),([true,false,false,true,false]) ++ (rep [false,true,false,false,true,false] (n))⟩ := by rfl

theorem local3 (L R : List Bool) : run0 table 38 ⟨2,([false]) ++ (L),([true,false,false,true,false]) ++ ([false,true,false,false,true,false]) ++ (R)⟩ = some ⟨2,([false]) ++ ([true,false,false,true,false,false]) ++ (L),([true,false,false,true,false]) ++ (R)⟩ := by rfl

theorem phase3 (n : Nat) : run0 table (38*n) ⟨2,([false,true]),([true,false,false,true,false]) ++ (rep [false,true,false,false,true,false] (n))⟩ = some ⟨2,([false]) ++ (rep [true,false,false,true,false,false] (n)) ++ ([true]),([true,false,false,true,false])⟩ := by
  simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using sweepR table 2 [false] [true,false,false,true,false] [false,true,false,false,true,false] [true,false,false,true,false,false] 38 local3 n (([true])) ([])

theorem phase4 (n : Nat) : run0 table 22 ⟨2,([false]) ++ (rep [true,false,false,true,false,false] (n)) ++ ([true]),([true,false,false,true,false])⟩ = some ⟨1,([false,true,false,false,true,false,false]) ++ (rep [true,false,false,true,false,false] (n)) ++ ([true]),[]⟩ := by rfl

theorem finalL (n : Nat) : ([false,true,false,false,true,false,false]) ++ (rep [true,false,false,true,false,false] (n)) ++ ([true]) = ([false,true,false,false,true,false,false,true]) ++ (rep [false,false,true,false,false,true] (n)) := by
  calc
    _ = ([false,true,false,false,true,false,false,true]) ++ (rep [false,false,true,false,false,true] (n)) := by symm; simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using moveCut (([false,true,false,false,true,false,false])) ([]) [false,false,true,false,false] true n

theorem finalR (n : Nat) : ([] : List Bool) = [] := by
  rfl

theorem growth (n : Nat) : run0 table (43+60*n) (family n) = some (family (n+1)) := by
  have H := (join0 (join0 (join0 (join0 (phase0 n) (phase1 n)) (phase2 n)) (phase3 n)) (phase4 n))
  rw [finalL n] at H
  rw [show 2+22*n+19+38*n+22=43+60*n by omega] at H
  simpa only [family,rep,List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using H

theorem never (m : Machine) (hm : compatible table m) : NeverHalts m :=
  never_of_growth table family 1 (fun n => 43+60*n) entry (by intro n; omega) growth m hm

#print axioms never

end M120

namespace M124

-- 1RB1RC_1RC1LA_0RD0LE_1LD0RA_---1LF_0LB1LC

def table : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 0,true => some (some ⟨true,true,2⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 1,true => some (some ⟨true,false,0⟩)
  | 2,false => some (some ⟨false,true,3⟩)
  | 2,true => some (some ⟨false,false,4⟩)
  | 3,false => some (some ⟨true,false,3⟩)
  | 3,true => some (some ⟨false,true,0⟩)
  | 4,true => some (some ⟨true,false,5⟩)
  | 5,false => some (some ⟨false,false,1⟩)
  | 5,true => some (some ⟨true,false,2⟩)
  | _,_ => none

def family (n : Nat) : Z0 := ⟨1,([false,true]) ++ (rep [false,false,true,false,false,true] (n)),[]⟩

theorem entry : run0 table 1 ⟨0,[],[]⟩ = some (family 0) := by rfl

theorem phase0 (n : Nat) : run0 table 5 ⟨1,([false,true]) ++ (rep [false,false,true,false,false,true] (n)),[]⟩ = some ⟨0,([true,false,true]) ++ (rep [false,false,true,false,false,true] (n)),([true])⟩ := by rfl

theorem local1 (L R : List Bool) : run0 table 14 ⟨0,([true,false,true]) ++ ([false,false,true,false,false,true]) ++ (L),([true]) ++ (R)⟩ = some ⟨0,([true,false,true]) ++ (L),([true]) ++ ([false,true,false,false,true,false]) ++ (R)⟩ := by rfl

theorem phase1 (n : Nat) : run0 table (14*n) ⟨0,([true,false,true]) ++ (rep [false,false,true,false,false,true] (n)),([true])⟩ = some ⟨0,([true,false,true]),([true]) ++ (rep [false,true,false,false,true,false] (n))⟩ := by
  simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using sweepL table 0 [true,false,true] [true] [false,false,true,false,false,true] [false,true,false,false,true,false] 14 local1 n ([]) ([])

theorem phase2 (n : Nat) : run0 table 12 ⟨0,([true,false,true]),([true]) ++ (rep [false,true,false,false,true,false] (n))⟩ = some ⟨2,([false,true]),([true,false,false,true,false]) ++ (rep [false,true,false,false,true,false] (n))⟩ := by rfl

theorem local3 (L R : List Bool) : run0 table 38 ⟨2,([false]) ++ (L),([true,false,false,true,false]) ++ ([false,true,false,false,true,false]) ++ (R)⟩ = some ⟨2,([false]) ++ ([true,false,false,true,false,false]) ++ (L),([true,false,false,true,false]) ++ (R)⟩ := by rfl

theorem phase3 (n : Nat) : run0 table (38*n) ⟨2,([false,true]),([true,false,false,true,false]) ++ (rep [false,true,false,false,true,false] (n))⟩ = some ⟨2,([false]) ++ (rep [true,false,false,true,false,false] (n)) ++ ([true]),([true,false,false,true,false])⟩ := by
  simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using sweepR table 2 [false] [true,false,false,true,false] [false,true,false,false,true,false] [true,false,false,true,false,false] 38 local3 n (([true])) ([])

theorem phase4 (n : Nat) : run0 table 22 ⟨2,([false]) ++ (rep [true,false,false,true,false,false] (n)) ++ ([true]),([true,false,false,true,false])⟩ = some ⟨1,([false,true,false,false,true,false,false]) ++ (rep [true,false,false,true,false,false] (n)) ++ ([true]),[]⟩ := by rfl

theorem finalL (n : Nat) : ([false,true,false,false,true,false,false]) ++ (rep [true,false,false,true,false,false] (n)) ++ ([true]) = ([false,true,false,false,true,false,false,true]) ++ (rep [false,false,true,false,false,true] (n)) := by
  calc
    _ = ([false,true,false,false,true,false,false,true]) ++ (rep [false,false,true,false,false,true] (n)) := by symm; simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using moveCut (([false,true,false,false,true,false,false])) ([]) [false,false,true,false,false] true n

theorem finalR (n : Nat) : ([] : List Bool) = [] := by
  rfl

theorem growth (n : Nat) : run0 table (39+52*n) (family n) = some (family (n+1)) := by
  have H := (join0 (join0 (join0 (join0 (phase0 n) (phase1 n)) (phase2 n)) (phase3 n)) (phase4 n))
  rw [finalL n] at H
  rw [show 5+14*n+12+38*n+22=39+52*n by omega] at H
  simpa only [family,rep,List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using H

theorem never (m : Machine) (hm : compatible table m) : NeverHalts m :=
  never_of_growth table family 1 (fun n => 39+52*n) entry (by intro n; omega) growth m hm

#print axioms never

end M124

namespace M127

-- 1RB1RC_1RC1LB_0RD0LE_1LD0RA_---1LF_0LB1LC

def table : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 0,true => some (some ⟨true,true,2⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 1,true => some (some ⟨true,false,1⟩)
  | 2,false => some (some ⟨false,true,3⟩)
  | 2,true => some (some ⟨false,false,4⟩)
  | 3,false => some (some ⟨true,false,3⟩)
  | 3,true => some (some ⟨false,true,0⟩)
  | 4,true => some (some ⟨true,false,5⟩)
  | 5,false => some (some ⟨false,false,1⟩)
  | 5,true => some (some ⟨true,false,2⟩)
  | _,_ => none

def family (n : Nat) : Z0 := ⟨1,([false,true]) ++ (rep [false,false,true,false,false,true] (n)),[]⟩

theorem entry : run0 table 1 ⟨0,[],[]⟩ = some (family 0) := by rfl

theorem phase0 (n : Nat) : run0 table 6 ⟨1,([false,true]) ++ (rep [false,false,true,false,false,true] (n)),[]⟩ = some ⟨2,([true,true,false,true]) ++ (rep [false,false,true,false,false,true] (n)),[]⟩ := by rfl

theorem local1 (L R : List Bool) : run0 table 10 ⟨2,([true,true,false,true]) ++ ([false,false,true,false,false,true]) ++ (L),(R)⟩ = some ⟨2,([true,true,false,true]) ++ (L),([false,true,false,false,true,false]) ++ (R)⟩ := by rfl

theorem phase1 (n : Nat) : run0 table (10*n) ⟨2,([true,true,false,true]) ++ (rep [false,false,true,false,false,true] (n)),[]⟩ = some ⟨2,([true,true,false,true]),(rep [false,true,false,false,true,false] (n))⟩ := by
  simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using sweepL table 2 [true,true,false,true] [] [false,false,true,false,false,true] [false,true,false,false,true,false] 10 local1 n ([]) ([])

theorem phase2 (n : Nat) : run0 table 9 ⟨2,([true,true,false,true]),(rep [false,true,false,false,true,false] (n))⟩ = some ⟨2,([false,true]),([true,false,false,true,false]) ++ (rep [false,true,false,false,true,false] (n))⟩ := by rfl

theorem local3 (L R : List Bool) : run0 table 38 ⟨2,([false]) ++ (L),([true,false,false,true,false]) ++ ([false,true,false,false,true,false]) ++ (R)⟩ = some ⟨2,([false]) ++ ([true,false,false,true,false,false]) ++ (L),([true,false,false,true,false]) ++ (R)⟩ := by rfl

theorem phase3 (n : Nat) : run0 table (38*n) ⟨2,([false,true]),([true,false,false,true,false]) ++ (rep [false,true,false,false,true,false] (n))⟩ = some ⟨2,([false]) ++ (rep [true,false,false,true,false,false] (n)) ++ ([true]),([true,false,false,true,false])⟩ := by
  simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using sweepR table 2 [false] [true,false,false,true,false] [false,true,false,false,true,false] [true,false,false,true,false,false] 38 local3 n (([true])) ([])

theorem phase4 (n : Nat) : run0 table 22 ⟨2,([false]) ++ (rep [true,false,false,true,false,false] (n)) ++ ([true]),([true,false,false,true,false])⟩ = some ⟨1,([false,true,false,false,true,false,false]) ++ (rep [true,false,false,true,false,false] (n)) ++ ([true]),[]⟩ := by rfl

theorem finalL (n : Nat) : ([false,true,false,false,true,false,false]) ++ (rep [true,false,false,true,false,false] (n)) ++ ([true]) = ([false,true,false,false,true,false,false,true]) ++ (rep [false,false,true,false,false,true] (n)) := by
  calc
    _ = ([false,true,false,false,true,false,false,true]) ++ (rep [false,false,true,false,false,true] (n)) := by symm; simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using moveCut (([false,true,false,false,true,false,false])) ([]) [false,false,true,false,false] true n

theorem finalR (n : Nat) : ([] : List Bool) = [] := by
  rfl

theorem growth (n : Nat) : run0 table (37+48*n) (family n) = some (family (n+1)) := by
  have H := (join0 (join0 (join0 (join0 (phase0 n) (phase1 n)) (phase2 n)) (phase3 n)) (phase4 n))
  rw [finalL n] at H
  rw [show 6+10*n+9+38*n+22=37+48*n by omega] at H
  simpa only [family,rep,List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using H

theorem never (m : Machine) (hm : compatible table m) : NeverHalts m :=
  never_of_growth table family 1 (fun n => 37+48*n) entry (by intro n; omega) growth m hm

#print axioms never

end M127

namespace M128

-- 1RB1RC_1RC1LE_0RD0LE_1LD0RA_0LF1LF_0LB---

def table : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 0,true => some (some ⟨true,true,2⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 1,true => some (some ⟨true,false,4⟩)
  | 2,false => some (some ⟨false,true,3⟩)
  | 2,true => some (some ⟨false,false,4⟩)
  | 3,false => some (some ⟨true,false,3⟩)
  | 3,true => some (some ⟨false,true,0⟩)
  | 4,false => some (some ⟨false,false,5⟩)
  | 4,true => some (some ⟨true,false,5⟩)
  | 5,false => some (some ⟨false,false,1⟩)
  | _,_ => none

def family (n : Nat) : Z0 := ⟨4,[],([true,false,true]) ++ (rep [true,false,true,true,false,false,true,false,false,true,false,true] (n)) ++ ([false])⟩

theorem entry : run0 table 11 ⟨0,[],[]⟩ = some (family 0) := by rfl

theorem phase0 (n : Nat) : run0 table 12 ⟨4,[],([true,false,true]) ++ (rep [true,false,true,true,false,false,true,false,false,true,false,true] (n)) ++ ([false])⟩ = some ⟨2,([false,true]),([true,false,true,false,true]) ++ (rep [true,false,true,true,false,false,true,false,false,true,false,true] (n)) ++ ([false])⟩ := by rfl

theorem local1 (L R : List Bool) : run0 table 44 ⟨2,([false]) ++ (L),([true,false,true,false,true]) ++ ([true,false,true,true,false,false,true,false,false,true,false,true]) ++ (R)⟩ = some ⟨2,([false]) ++ ([true,false,true,true,false,true,false,false,true,false,false,true]) ++ (L),([true,false,true,false,true]) ++ (R)⟩ := by rfl

theorem phase1 (n : Nat) : run0 table (44*n) ⟨2,([false,true]),([true,false,true,false,true]) ++ (rep [true,false,true,true,false,false,true,false,false,true,false,true] (n)) ++ ([false])⟩ = some ⟨2,([false]) ++ (rep [true,false,true,true,false,true,false,false,true,false,false,true] (n)) ++ ([true]),([true,false,true,false,true,false])⟩ := by
  simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using sweepR table 2 [false] [true,false,true,false,true] [true,false,true,true,false,false,true,false,false,true,false,true] [true,false,true,true,false,true,false,false,true,false,false,true] 44 local1 n (([true])) (([false]))

theorem phase2 (n : Nat) : run0 table 20 ⟨2,([false]) ++ (rep [true,false,true,true,false,true,false,false,true,false,false,true] (n)) ++ ([true]),([true,false,true,false,true,false])⟩ = some ⟨4,([true,false,true,false,false,true,false,false,true]) ++ (rep [true,false,true,true,false,true,false,false,true,false,false,true] (n)) ++ ([true]),([false])⟩ := by rfl

theorem local3 (L R : List Bool) : run0 table 12 ⟨4,([true,false,true,false,false,true,false,false,true]) ++ ([true,false,true,true,false,true,false,false,true,false,false,true]) ++ (L),(R)⟩ = some ⟨4,([true,false,true,false,false,true,false,false,true]) ++ (L),([true,false,true,true,false,false,true,false,false,true,false,true]) ++ (R)⟩ := by rfl

theorem phase3 (n : Nat) : run0 table (12*n) ⟨4,([true,false,true,false,false,true,false,false,true]) ++ (rep [true,false,true,true,false,true,false,false,true,false,false,true] (n)) ++ ([true]),([false])⟩ = some ⟨4,([true,false,true,false,false,true,false,false,true,true]),(rep [true,false,true,true,false,false,true,false,false,true,false,true] (n)) ++ ([false])⟩ := by
  simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using sweepL table 4 [true,false,true,false,false,true,false,false,true] [] [true,false,true,true,false,true,false,false,true,false,false,true] [true,false,true,true,false,false,true,false,false,true,false,true] 12 local3 n (([true])) (([false]))

theorem phase4 (n : Nat) : run0 table 12 ⟨4,([true,false,true,false,false,true,false,false,true,true]),(rep [true,false,true,true,false,false,true,false,false,true,false,true] (n)) ++ ([false])⟩ = some ⟨2,([false,true]),([true,true,false,false,true,false,false,true,false,true]) ++ (rep [true,false,true,true,false,false,true,false,false,true,false,true] (n)) ++ ([false])⟩ := by rfl

theorem local5 (L R : List Bool) : run0 table 44 ⟨2,([false]) ++ (L),([true,true,false,false,true,false,false,true,false,true]) ++ ([true,false,true,true,false,false,true,false,false,true,false,true]) ++ (R)⟩ = some ⟨2,([false]) ++ ([true,false,false,true,false,false,true,true,false,true,true,false]) ++ (L),([true,true,false,false,true,false,false,true,false,true]) ++ (R)⟩ := by rfl

theorem phase5 (n : Nat) : run0 table (44*n) ⟨2,([false,true]),([true,true,false,false,true,false,false,true,false,true]) ++ (rep [true,false,true,true,false,false,true,false,false,true,false,true] (n)) ++ ([false])⟩ = some ⟨2,([false]) ++ (rep [true,false,false,true,false,false,true,true,false,true,true,false] (n)) ++ ([true]),([true,true,false,false,true,false,false,true,false,true,false])⟩ := by
  simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using sweepR table 2 [false] [true,true,false,false,true,false,false,true,false,true] [true,false,true,true,false,false,true,false,false,true,false,true] [true,false,false,true,false,false,true,true,false,true,true,false] 44 local5 n (([true])) (([false]))

theorem phase6 (n : Nat) : run0 table 51 ⟨2,([false]) ++ (rep [true,false,false,true,false,false,true,true,false,true,true,false] (n)) ++ ([true]),([true,true,false,false,true,false,false,true,false,true,false])⟩ = some ⟨4,([true,false,true,false,false,true,false,false,true,true,false,true,true,false]) ++ (rep [true,false,false,true,false,false,true,true,false,true,true,false] (n)) ++ ([true]),([false])⟩ := by rfl

theorem local7 (L R : List Bool) : run0 table 12 ⟨4,([true,false,true,false,false,true,false,false,true,true,false,true,true,false]) ++ ([true,false,false,true,false,false,true,true,false,true,true,false]) ++ (L),(R)⟩ = some ⟨4,([true,false,true,false,false,true,false,false,true,true,false,true,true,false]) ++ (L),([true,false,true,true,false,false,true,false,false,true,false,true]) ++ (R)⟩ := by rfl

theorem phase7 (n : Nat) : run0 table (12*n) ⟨4,([true,false,true,false,false,true,false,false,true,true,false,true,true,false]) ++ (rep [true,false,false,true,false,false,true,true,false,true,true,false] (n)) ++ ([true]),([false])⟩ = some ⟨4,([true,false,true,false,false,true,false,false,true,true,false,true,true,false,true]),(rep [true,false,true,true,false,false,true,false,false,true,false,true] (n)) ++ ([false])⟩ := by
  simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using sweepL table 4 [true,false,true,false,false,true,false,false,true,true,false,true,true,false] [] [true,false,false,true,false,false,true,true,false,true,true,false] [true,false,true,true,false,false,true,false,false,true,false,true] 12 local7 n (([true])) (([false]))

theorem phase8 (n : Nat) : run0 table 15 ⟨4,([true,false,true,false,false,true,false,false,true,true,false,true,true,false,true]),(rep [true,false,true,true,false,false,true,false,false,true,false,true] (n)) ++ ([false])⟩ = some ⟨4,[],([true,false,true,true,false,true,true,false,false,true,false,false,true,false,true]) ++ (rep [true,false,true,true,false,false,true,false,false,true,false,true] (n)) ++ ([false])⟩ := by rfl

theorem finalL (n : Nat) : ([] : List Bool) = [] := by
  rfl

theorem finalR (n : Nat) : ([true,false,true,true,false,true,true,false,false,true,false,false,true,false,true]) ++ (rep [true,false,true,true,false,false,true,false,false,true,false,true] (n)) ++ ([false]) = ([true,false,true,true,false,true,true,false,false,true,false,false,true,false,true]) ++ (rep [true,false,true,true,false,false,true,false,false,true,false,true] (n)) ++ ([false]) := by
  rfl

theorem growth (n : Nat) : run0 table (110+112*n) (family n) = some (family (n+1)) := by
  have H := (join0 (join0 (join0 (join0 (join0 (join0 (join0 (join0 (phase0 n) (phase1 n)) (phase2 n)) (phase3 n)) (phase4 n)) (phase5 n)) (phase6 n)) (phase7 n)) (phase8 n))
  rw [show 12+44*n+20+12*n+12+44*n+51+12*n+15=110+112*n by omega] at H
  simpa only [family,rep,List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using H

theorem never (m : Machine) (hm : compatible table m) : NeverHalts m :=
  never_of_growth table family 11 (fun n => 110+112*n) entry (by intro n; omega) growth m hm

#print axioms never

end M128

namespace M130

-- 1RB1RC_1RC1LE_0RD0LE_1LD0RA_1RB1LF_0LB---

def table : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 0,true => some (some ⟨true,true,2⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 1,true => some (some ⟨true,false,4⟩)
  | 2,false => some (some ⟨false,true,3⟩)
  | 2,true => some (some ⟨false,false,4⟩)
  | 3,false => some (some ⟨true,false,3⟩)
  | 3,true => some (some ⟨false,true,0⟩)
  | 4,false => some (some ⟨true,true,1⟩)
  | 4,true => some (some ⟨true,false,5⟩)
  | 5,false => some (some ⟨false,false,1⟩)
  | _,_ => none

def family (n : Nat) : Z0 := ⟨1,([false,true]) ++ (rep [false,false,true,false,false,true] (n)),[]⟩

theorem entry : run0 table 1 ⟨0,[],[]⟩ = some (family 0) := by rfl

theorem phase0 (n : Nat) : run0 table 7 ⟨1,([false,true]) ++ (rep [false,false,true,false,false,true] (n)),[]⟩ = some ⟨4,([true,false,true]) ++ (rep [false,false,true,false,false,true] (n)),([false])⟩ := by rfl

theorem local1 (L R : List Bool) : run0 table 10 ⟨4,([true,false,true]) ++ ([false,false,true,false,false,true]) ++ (L),(R)⟩ = some ⟨4,([true,false,true]) ++ (L),([true,false,true,true,false,true]) ++ (R)⟩ := by rfl

theorem phase1 (n : Nat) : run0 table (10*n) ⟨4,([true,false,true]) ++ (rep [false,false,true,false,false,true] (n)),([false])⟩ = some ⟨4,([true,false,true]),(rep [true,false,true,true,false,true] (n)) ++ ([false])⟩ := by
  simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using sweepL table 4 [true,false,true] [] [false,false,true,false,false,true] [true,false,true,true,false,true] 10 local1 n ([]) (([false]))

theorem phase2 (n : Nat) : run0 table 8 ⟨4,([true,false,true]),(rep [true,false,true,true,false,true] (n)) ++ ([false])⟩ = some ⟨2,([false,true]),([true,true,false,true]) ++ (rep [true,false,true,true,false,true] (n)) ++ ([false])⟩ := by rfl

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

end M130

namespace M132

-- 1RB1RC_1RC0RA_0RD0LE_1LD0RA_0LA1LF_0LE---

def table : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 0,true => some (some ⟨true,true,2⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 1,true => some (some ⟨false,true,0⟩)
  | 2,false => some (some ⟨false,true,3⟩)
  | 2,true => some (some ⟨false,false,4⟩)
  | 3,false => some (some ⟨true,false,3⟩)
  | 3,true => some (some ⟨false,true,0⟩)
  | 4,false => some (some ⟨false,false,0⟩)
  | 4,true => some (some ⟨true,false,5⟩)
  | 5,false => some (some ⟨false,false,4⟩)
  | _,_ => none

def family (n : Nat) : Z0 := ⟨5,[],([true,false,true,false]) ++ (rep [true,false,true,false,true,false] (n))⟩

theorem entry : run0 table 11 ⟨0,[],[]⟩ = some (family 0) := by rfl

theorem phase0 (n : Nat) : run0 table 6 ⟨5,[],([true,false,true,false]) ++ (rep [true,false,true,false,true,false] (n))⟩ = some ⟨0,([false,false,false,true,true]),([true,false]) ++ (rep [true,false,true,false,true,false] (n))⟩ := by rfl

theorem local1 (L R : List Bool) : run0 table 6 ⟨0,([false]) ++ (L),([true,false]) ++ ([true,false,true,false,true,false]) ++ (R)⟩ = some ⟨0,([false]) ++ ([false,true,false,true,false,true]) ++ (L),([true,false]) ++ (R)⟩ := by rfl

theorem phase1 (n : Nat) : run0 table (6*n) ⟨0,([false,false,false,true,true]),([true,false]) ++ (rep [true,false,true,false,true,false] (n))⟩ = some ⟨0,([false]) ++ (rep [false,true,false,true,false,true] (n)) ++ ([false,false,true,true]),([true,false])⟩ := by
  simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using sweepR table 0 [false] [true,false] [true,false,true,false,true,false] [false,true,false,true,false,true] 6 local1 n (([false,false,true,true])) ([])

theorem phase2 (n : Nat) : run0 table 10 ⟨0,([false]) ++ (rep [false,true,false,true,false,true] (n)) ++ ([false,false,true,true]),([true,false])⟩ = some ⟨4,([true,false,true,false,true]) ++ (rep [false,true,false,true,false,true] (n)) ++ ([false,false,true,true]),([false])⟩ := by rfl

theorem local3 (L R : List Bool) : run0 table 6 ⟨4,([true,false,true,false,true]) ++ ([false,true,false,true,false,true]) ++ (L),(R)⟩ = some ⟨4,([true,false,true,false,true]) ++ (L),([false,true,false,true,false,true]) ++ (R)⟩ := by rfl

theorem phase3 (n : Nat) : run0 table (6*n) ⟨4,([true,false,true,false,true]) ++ (rep [false,true,false,true,false,true] (n)) ++ ([false,false,true,true]),([false])⟩ = some ⟨4,([true,false,true,false,true,false,false,true,true]),(rep [false,true,false,true,false,true] (n)) ++ ([false])⟩ := by
  simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using sweepL table 4 [true,false,true,false,true] [] [false,true,false,true,false,true] [false,true,false,true,false,true] 6 local3 n (([false,false,true,true])) (([false]))

theorem phase4 (n : Nat) : run0 table 17 ⟨4,([true,false,true,false,true,false,false,true,true]),(rep [false,true,false,true,false,true] (n)) ++ ([false])⟩ = some ⟨5,[],([true,false,true,false,true,false,true,false,true]) ++ (rep [false,true,false,true,false,true] (n)) ++ ([false])⟩ := by rfl

theorem finalL (n : Nat) : ([] : List Bool) = [] := by
  rfl

theorem finalR (n : Nat) : ([true,false,true,false,true,false,true,false,true]) ++ (rep [false,true,false,true,false,true] (n)) ++ ([false]) = ([true,false,true,false,true,false,true,false,true,false]) ++ (rep [true,false,true,false,true,false] (n)) := by
  calc
    _ = ([true,false,true,false,true,false,true,false,true,false]) ++ (rep [true,false,true,false,true,false] (n)) := by symm; simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using moveCut (([true,false,true,false,true,false,true,false,true])) ([]) [true,false,true,false,true] false n

theorem growth (n : Nat) : run0 table (33+12*n) (family n) = some (family (n+1)) := by
  have H := (join0 (join0 (join0 (join0 (phase0 n) (phase1 n)) (phase2 n)) (phase3 n)) (phase4 n))
  rw [finalR n] at H
  rw [show 6+6*n+10+6*n+17=33+12*n by omega] at H
  simpa only [family,rep,List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using H

theorem never (m : Machine) (hm : compatible table m) : NeverHalts m :=
  never_of_growth table family 11 (fun n => 33+12*n) entry (by intro n; omega) growth m hm

#print axioms never

end M132

end BB6.Agent11Raw39B1RCPumps
