import SweepPumping
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedVariables false
namespace BB6.Agent11Raw39B0REPumps
open BB6Coverage BB6Coverage.Agent31Pump


namespace M128

-- 1RB0RE_1RC1RD_0RD---_1LD0RA_1RA0LF_0LF1LE

def table : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 0,true => some (some ⟨false,true,4⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 1,true => some (some ⟨true,true,3⟩)
  | 2,false => some (some ⟨false,true,3⟩)
  | 3,false => some (some ⟨true,false,3⟩)
  | 3,true => some (some ⟨false,true,0⟩)
  | 4,false => some (some ⟨true,true,0⟩)
  | 4,true => some (some ⟨false,false,5⟩)
  | 5,false => some (some ⟨false,false,5⟩)
  | 5,true => some (some ⟨true,false,4⟩)
  | _,_ => none

def family (n : Nat) : Z0 := ⟨2,([false,true,true,true,false]) ++ (rep [false,true,true,false] (n)) ++ ([true]),[]⟩

theorem entry : run0 table 16 ⟨0,[],[]⟩ = some (family 0) := by rfl

theorem phase0 (n : Nat) : run0 table 5 ⟨2,([false,true,true,true,false]) ++ (rep [false,true,true,false] (n)) ++ ([true]),[]⟩ = some ⟨4,([true,false,false,true,true,false]) ++ (rep [false,true,true,false] (n)) ++ ([true]),[]⟩ := by rfl

theorem local1 (L R : List Bool) : run0 table 4 ⟨4,([true,false,false,true,true,false]) ++ ([false,true,true,false]) ++ (L),(R)⟩ = some ⟨4,([true,false,false,true,true,false]) ++ (L),([true,false,false,false]) ++ (R)⟩ := by rfl

theorem phase1 (n : Nat) : run0 table (4*n) ⟨4,([true,false,false,true,true,false]) ++ (rep [false,true,true,false] (n)) ++ ([true]),[]⟩ = some ⟨4,([true,false,false,true,true,false,true]),(rep [true,false,false,false] (n))⟩ := by
  simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using sweepL table 4 [true,false,false,true,true,false] [] [false,true,true,false] [true,false,false,false] 4 local1 n (([true])) ([])

theorem phase2 (n : Nat) : run0 table 8 ⟨4,([true,false,false,true,true,false,true]),(rep [true,false,false,false] (n))⟩ = some ⟨0,([true,true]),([false,false,true,false,false,false]) ++ (rep [true,false,false,false] (n))⟩ := by rfl

theorem local3 (L R : List Bool) : run0 table 6 ⟨0,([true]) ++ (L),([false,false,true,false,false,false]) ++ ([true,false,false,false]) ++ (R)⟩ = some ⟨0,([true]) ++ ([false,true,true,false]) ++ (L),([false,false,true,false,false,false]) ++ (R)⟩ := by rfl

theorem phase3 (n : Nat) : run0 table (6*n) ⟨0,([true,true]),([false,false,true,false,false,false]) ++ (rep [true,false,false,false] (n))⟩ = some ⟨0,([true]) ++ (rep [false,true,true,false] (n)) ++ ([true]),([false,false,true,false,false,false])⟩ := by
  simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using sweepR table 0 [true] [false,false,true,false,false,false] [true,false,false,false] [false,true,true,false] 6 local3 n (([true])) ([])

theorem phase4 (n : Nat) : run0 table 10 ⟨0,([true]) ++ (rep [false,true,true,false] (n)) ++ ([true]),([false,false,true,false,false,false])⟩ = some ⟨2,([false,true,true,true,false,false,true,true,false]) ++ (rep [false,true,true,false] (n)) ++ ([true]),[]⟩ := by rfl

theorem finalL (n : Nat) : ([false,true,true,true,false,false,true,true,false]) ++ (rep [false,true,true,false] (n)) ++ ([true]) = ([false,true,true,true,false,false,true,true,false]) ++ (rep [false,true,true,false] (n)) ++ ([true]) := by
  rfl

theorem finalR (n : Nat) : ([] : List Bool) = [] := by
  rfl

theorem growth (n : Nat) : run0 table (23+10*n) (family n) = some (family (n+1)) := by
  have H := (join0 (join0 (join0 (join0 (phase0 n) (phase1 n)) (phase2 n)) (phase3 n)) (phase4 n))
  rw [show 5+4*n+8+6*n+10=23+10*n by omega] at H
  simpa only [family,rep,List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using H

theorem never (m : Machine) (hm : compatible table m) : NeverHalts m :=
  never_of_growth table family 16 (fun n => 23+10*n) entry (by intro n; omega) growth m hm

#print axioms never

end M128

namespace M149

-- 1RB0RE_1RC1LF_0RD---_1LD0RA_0LB0LF_1LA0LB

def table : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 0,true => some (some ⟨false,true,4⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 1,true => some (some ⟨true,false,5⟩)
  | 2,false => some (some ⟨false,true,3⟩)
  | 3,false => some (some ⟨true,false,3⟩)
  | 3,true => some (some ⟨false,true,0⟩)
  | 4,false => some (some ⟨false,false,1⟩)
  | 4,true => some (some ⟨false,false,5⟩)
  | 5,false => some (some ⟨true,false,0⟩)
  | 5,true => some (some ⟨false,false,1⟩)
  | _,_ => none

def family (n : Nat) : Z0 := ⟨1,([false,true]) ++ (rep [false,false,true,false,false,true] (n)),[]⟩

theorem entry : run0 table 1 ⟨0,[],[]⟩ = some (family 0) := by rfl

theorem phase0 (n : Nat) : run0 table 7 ⟨1,([false,true]) ++ (rep [false,false,true,false,false,true] (n)),[]⟩ = some ⟨5,([false,false,true]) ++ (rep [false,false,true,false,false,true] (n)),([false])⟩ := by rfl

theorem local1 (L R : List Bool) : run0 table 10 ⟨5,([false,false,true]) ++ ([false,false,true,false,false,true]) ++ (L),(R)⟩ = some ⟨5,([false,false,true]) ++ (L),([true,false,true,true,false,true]) ++ (R)⟩ := by rfl

theorem phase1 (n : Nat) : run0 table (10*n) ⟨5,([false,false,true]) ++ (rep [false,false,true,false,false,true] (n)),([false])⟩ = some ⟨5,([false,false,true]),(rep [true,false,true,true,false,true] (n)) ++ ([false])⟩ := by
  simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using sweepL table 5 [false,false,true] [] [false,false,true,false,false,true] [true,false,true,true,false,true] 10 local1 n ([]) (([false]))

theorem phase2 (n : Nat) : run0 table 10 ⟨5,([false,false,true]),(rep [true,false,true,true,false,true] (n)) ++ ([false])⟩ = some ⟨2,([false,true]),([true,true,false,true]) ++ (rep [true,false,true,true,false,true] (n)) ++ ([false])⟩ := by rfl

theorem local3 (L R : List Bool) : run0 table 10 ⟨2,([false]) ++ (L),([true,true,false,true]) ++ ([true,false,true,true,false,true]) ++ (R)⟩ = some ⟨2,([false]) ++ ([true,false,false,true,false,false]) ++ (L),([true,true,false,true]) ++ (R)⟩ := by rfl

theorem phase3 (n : Nat) : run0 table (10*n) ⟨2,([false,true]),([true,true,false,true]) ++ (rep [true,false,true,true,false,true] (n)) ++ ([false])⟩ = some ⟨2,([false]) ++ (rep [true,false,false,true,false,false] (n)) ++ ([true]),([true,true,false,true,false])⟩ := by
  simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using sweepR table 2 [false] [true,true,false,true] [true,false,true,true,false,true] [true,false,false,true,false,false] 10 local3 n (([true])) (([false]))

theorem phase4 (n : Nat) : run0 table 8 ⟨2,([false]) ++ (rep [true,false,false,true,false,false] (n)) ++ ([true]),([true,true,false,true,false])⟩ = some ⟨1,([false,true,false,false,true,false,false]) ++ (rep [true,false,false,true,false,false] (n)) ++ ([true]),[]⟩ := by rfl

theorem finalL (n : Nat) : ([false,true,false,false,true,false,false]) ++ (rep [true,false,false,true,false,false] (n)) ++ ([true]) = ([false,true,false,false,true,false,false,true]) ++ (rep [false,false,true,false,false,true] (n)) := by
  calc
    _ = ([false,true,false,false,true,false,false,true]) ++ (rep [false,false,true,false,false,true] (n)) := by symm; simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using moveCut (([false,true,false,false,true,false,false])) ([]) [false,false,true,false,false] true n

theorem finalR (n : Nat) : ([] : List Bool) = [] := by
  rfl

theorem growth (n : Nat) : run0 table (25+20*n) (family n) = some (family (n+1)) := by
  have H := (join0 (join0 (join0 (join0 (phase0 n) (phase1 n)) (phase2 n)) (phase3 n)) (phase4 n))
  rw [finalL n] at H
  rw [show 7+10*n+10+10*n+8=25+20*n by omega] at H
  simpa only [family,rep,List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using H

theorem never (m : Machine) (hm : compatible table m) : NeverHalts m :=
  never_of_growth table family 1 (fun n => 25+20*n) entry (by intro n; omega) growth m hm

#print axioms never

end M149

namespace M150

-- 1RB0RE_1RC1LF_0RD---_1LD0RA_0RE0LF_1LA0LB

def table : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 0,true => some (some ⟨false,true,4⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 1,true => some (some ⟨true,false,5⟩)
  | 2,false => some (some ⟨false,true,3⟩)
  | 3,false => some (some ⟨true,false,3⟩)
  | 3,true => some (some ⟨false,true,0⟩)
  | 4,false => some (some ⟨false,true,4⟩)
  | 4,true => some (some ⟨false,false,5⟩)
  | 5,false => some (some ⟨true,false,0⟩)
  | 5,true => some (some ⟨false,false,1⟩)
  | _,_ => none

def family (n : Nat) : Z0 := ⟨0,[],([true]) ++ (rep [false,true,false,true] (n)) ++ ([true,false,true,false])⟩

theorem entry : run0 table 14 ⟨0,[],[]⟩ = some (family 0) := by rfl

theorem phase0 (n : Nat) : run0 table 4 ⟨0,[],([true]) ++ (rep [false,true,false,true] (n)) ++ ([true,false,true,false])⟩ = some ⟨2,([false,true]),([true]) ++ (rep [false,true,false,true] (n)) ++ ([true,false,true,false])⟩ := by rfl

theorem local1 (L R : List Bool) : run0 table 12 ⟨2,([false]) ++ (L),([true]) ++ ([false,true,false,true]) ++ (R)⟩ = some ⟨2,([false]) ++ ([true,false,true,false]) ++ (L),([true]) ++ (R)⟩ := by rfl

theorem phase1 (n : Nat) : run0 table (12*n) ⟨2,([false,true]),([true]) ++ (rep [false,true,false,true] (n)) ++ ([true,false,true,false])⟩ = some ⟨2,([false]) ++ (rep [true,false,true,false] (n)) ++ ([true]),([true,true,false,true,false])⟩ := by
  simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using sweepR table 2 [false] [true] [false,true,false,true] [true,false,true,false] 12 local1 n (([true])) (([true,false,true,false]))

theorem phase2 (n : Nat) : run0 table 25 ⟨2,([false]) ++ (rep [true,false,true,false] (n)) ++ ([true]),([true,true,false,true,false])⟩ = some ⟨5,([false,false,true,false]) ++ (rep [true,false,true,false] (n)) ++ ([true]),([true,false,true,false])⟩ := by rfl

theorem local3 (L R : List Bool) : run0 table 8 ⟨5,([false,false,true,false]) ++ ([true,false,true,false]) ++ (L),(R)⟩ = some ⟨5,([false,false,true,false]) ++ (L),([false,true,false,true]) ++ (R)⟩ := by rfl

theorem phase3 (n : Nat) : run0 table (8*n) ⟨5,([false,false,true,false]) ++ (rep [true,false,true,false] (n)) ++ ([true]),([true,false,true,false])⟩ = some ⟨5,([false,false,true,false,true]),(rep [false,true,false,true] (n)) ++ ([true,false,true,false])⟩ := by
  simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using sweepL table 5 [false,false,true,false] [] [true,false,true,false] [false,true,false,true] 8 local3 n (([true])) (([true,false,true,false]))

theorem phase4 (n : Nat) : run0 table 9 ⟨5,([false,false,true,false,true]),(rep [false,true,false,true] (n)) ++ ([true,false,true,false])⟩ = some ⟨0,[],([true,false,true,false,true]) ++ (rep [false,true,false,true] (n)) ++ ([true,false,true,false])⟩ := by rfl

theorem finalL (n : Nat) : ([] : List Bool) = [] := by
  rfl

theorem finalR (n : Nat) : ([true,false,true,false,true]) ++ (rep [false,true,false,true] (n)) ++ ([true,false,true,false]) = ([true,false,true,false,true]) ++ (rep [false,true,false,true] (n)) ++ ([true,false,true,false]) := by
  rfl

theorem growth (n : Nat) : run0 table (38+20*n) (family n) = some (family (n+1)) := by
  have H := (join0 (join0 (join0 (join0 (phase0 n) (phase1 n)) (phase2 n)) (phase3 n)) (phase4 n))
  rw [show 4+12*n+25+8*n+9=38+20*n by omega] at H
  simpa only [family,rep,List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using H

theorem never (m : Machine) (hm : compatible table m) : NeverHalts m :=
  never_of_growth table family 14 (fun n => 38+20*n) entry (by intro n; omega) growth m hm

#print axioms never

end M150

namespace M151

-- 1RB0RE_1RC1LF_0RD---_1LD0RA_1RB0LF_1LA0LB

def table : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 0,true => some (some ⟨false,true,4⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 1,true => some (some ⟨true,false,5⟩)
  | 2,false => some (some ⟨false,true,3⟩)
  | 3,false => some (some ⟨true,false,3⟩)
  | 3,true => some (some ⟨false,true,0⟩)
  | 4,false => some (some ⟨true,true,1⟩)
  | 4,true => some (some ⟨false,false,5⟩)
  | 5,false => some (some ⟨true,false,0⟩)
  | 5,true => some (some ⟨false,false,1⟩)
  | _,_ => none

def family (n : Nat) : Z0 := ⟨1,([false,true]) ++ (rep [false,false,true,false,false,true] (n)),[]⟩

theorem entry : run0 table 1 ⟨0,[],[]⟩ = some (family 0) := by rfl

theorem phase0 (n : Nat) : run0 table 7 ⟨1,([false,true]) ++ (rep [false,false,true,false,false,true] (n)),[]⟩ = some ⟨5,([false,false,true]) ++ (rep [false,false,true,false,false,true] (n)),([false])⟩ := by rfl

theorem local1 (L R : List Bool) : run0 table 10 ⟨5,([false,false,true]) ++ ([false,false,true,false,false,true]) ++ (L),(R)⟩ = some ⟨5,([false,false,true]) ++ (L),([true,false,true,true,false,true]) ++ (R)⟩ := by rfl

theorem phase1 (n : Nat) : run0 table (10*n) ⟨5,([false,false,true]) ++ (rep [false,false,true,false,false,true] (n)),([false])⟩ = some ⟨5,([false,false,true]),(rep [true,false,true,true,false,true] (n)) ++ ([false])⟩ := by
  simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using sweepL table 5 [false,false,true] [] [false,false,true,false,false,true] [true,false,true,true,false,true] 10 local1 n ([]) (([false]))

theorem phase2 (n : Nat) : run0 table 10 ⟨5,([false,false,true]),(rep [true,false,true,true,false,true] (n)) ++ ([false])⟩ = some ⟨2,([false,true]),([true,true,false,true]) ++ (rep [true,false,true,true,false,true] (n)) ++ ([false])⟩ := by rfl

theorem local3 (L R : List Bool) : run0 table 14 ⟨2,([false]) ++ (L),([true,true,false,true]) ++ ([true,false,true,true,false,true]) ++ (R)⟩ = some ⟨2,([false]) ++ ([true,false,false,true,false,false]) ++ (L),([true,true,false,true]) ++ (R)⟩ := by rfl

theorem phase3 (n : Nat) : run0 table (14*n) ⟨2,([false,true]),([true,true,false,true]) ++ (rep [true,false,true,true,false,true] (n)) ++ ([false])⟩ = some ⟨2,([false]) ++ (rep [true,false,false,true,false,false] (n)) ++ ([true]),([true,true,false,true,false])⟩ := by
  simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using sweepR table 2 [false] [true,true,false,true] [true,false,true,true,false,true] [true,false,false,true,false,false] 14 local3 n (([true])) (([false]))

theorem phase4 (n : Nat) : run0 table 10 ⟨2,([false]) ++ (rep [true,false,false,true,false,false] (n)) ++ ([true]),([true,true,false,true,false])⟩ = some ⟨1,([false,true,false,false,true,false,false]) ++ (rep [true,false,false,true,false,false] (n)) ++ ([true]),[]⟩ := by rfl

theorem finalL (n : Nat) : ([false,true,false,false,true,false,false]) ++ (rep [true,false,false,true,false,false] (n)) ++ ([true]) = ([false,true,false,false,true,false,false,true]) ++ (rep [false,false,true,false,false,true] (n)) := by
  calc
    _ = ([false,true,false,false,true,false,false,true]) ++ (rep [false,false,true,false,false,true] (n)) := by symm; simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using moveCut (([false,true,false,false,true,false,false])) ([]) [false,false,true,false,false] true n

theorem finalR (n : Nat) : ([] : List Bool) = [] := by
  rfl

theorem growth (n : Nat) : run0 table (27+24*n) (family n) = some (family (n+1)) := by
  have H := (join0 (join0 (join0 (join0 (phase0 n) (phase1 n)) (phase2 n)) (phase3 n)) (phase4 n))
  rw [finalL n] at H
  rw [show 7+10*n+10+14*n+10=27+24*n by omega] at H
  simpa only [family,rep,List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using H

theorem never (m : Machine) (hm : compatible table m) : NeverHalts m :=
  never_of_growth table family 1 (fun n => 27+24*n) entry (by intro n; omega) growth m hm

#print axioms never

end M151

namespace M152

-- 1RB0RE_1RC1LF_0RD---_1LD0RA_1RD0LF_1LA0LB

def table : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 0,true => some (some ⟨false,true,4⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 1,true => some (some ⟨true,false,5⟩)
  | 2,false => some (some ⟨false,true,3⟩)
  | 3,false => some (some ⟨true,false,3⟩)
  | 3,true => some (some ⟨false,true,0⟩)
  | 4,false => some (some ⟨true,true,3⟩)
  | 4,true => some (some ⟨false,false,5⟩)
  | 5,false => some (some ⟨true,false,0⟩)
  | 5,true => some (some ⟨false,false,1⟩)
  | _,_ => none

def family (n : Nat) : Z0 := ⟨0,[],([true]) ++ (rep [false,true,false,true,false,true,false,true] (n)) ++ ([true,false,true,false])⟩

theorem entry : run0 table 14 ⟨0,[],[]⟩ = some (family 0) := by rfl

theorem phase0 (n : Nat) : run0 table 4 ⟨0,[],([true]) ++ (rep [false,true,false,true,false,true,false,true] (n)) ++ ([true,false,true,false])⟩ = some ⟨2,([false,true]),([true]) ++ (rep [false,true,false,true,false,true,false,true] (n)) ++ ([true,false,true,false])⟩ := by rfl

theorem local1 (L R : List Bool) : run0 table 24 ⟨2,([false]) ++ (L),([true]) ++ ([false,true,false,true,false,true,false,true]) ++ (R)⟩ = some ⟨2,([false]) ++ ([true,false,true,false,true,false,true,false]) ++ (L),([true]) ++ (R)⟩ := by rfl

theorem phase1 (n : Nat) : run0 table (24*n) ⟨2,([false,true]),([true]) ++ (rep [false,true,false,true,false,true,false,true] (n)) ++ ([true,false,true,false])⟩ = some ⟨2,([false]) ++ (rep [true,false,true,false,true,false,true,false] (n)) ++ ([true]),([true,true,false,true,false])⟩ := by
  simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using sweepR table 2 [false] [true] [false,true,false,true,false,true,false,true] [true,false,true,false,true,false,true,false] 24 local1 n (([true])) (([true,false,true,false]))

theorem phase2 (n : Nat) : run0 table 53 ⟨2,([false]) ++ (rep [true,false,true,false,true,false,true,false] (n)) ++ ([true]),([true,true,false,true,false])⟩ = some ⟨5,([false,false,true,false,true,false,true,false]) ++ (rep [true,false,true,false,true,false,true,false] (n)) ++ ([true]),([true,false,true,false])⟩ := by rfl

theorem local3 (L R : List Bool) : run0 table 16 ⟨5,([false,false,true,false,true,false,true,false]) ++ ([true,false,true,false,true,false,true,false]) ++ (L),(R)⟩ = some ⟨5,([false,false,true,false,true,false,true,false]) ++ (L),([false,true,false,true,false,true,false,true]) ++ (R)⟩ := by rfl

theorem phase3 (n : Nat) : run0 table (16*n) ⟨5,([false,false,true,false,true,false,true,false]) ++ (rep [true,false,true,false,true,false,true,false] (n)) ++ ([true]),([true,false,true,false])⟩ = some ⟨5,([false,false,true,false,true,false,true,false,true]),(rep [false,true,false,true,false,true,false,true] (n)) ++ ([true,false,true,false])⟩ := by
  simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using sweepL table 5 [false,false,true,false,true,false,true,false] [] [true,false,true,false,true,false,true,false] [false,true,false,true,false,true,false,true] 16 local3 n (([true])) (([true,false,true,false]))

theorem phase4 (n : Nat) : run0 table 17 ⟨5,([false,false,true,false,true,false,true,false,true]),(rep [false,true,false,true,false,true,false,true] (n)) ++ ([true,false,true,false])⟩ = some ⟨0,[],([true,false,true,false,true,false,true,false,true]) ++ (rep [false,true,false,true,false,true,false,true] (n)) ++ ([true,false,true,false])⟩ := by rfl

theorem finalL (n : Nat) : ([] : List Bool) = [] := by
  rfl

theorem finalR (n : Nat) : ([true,false,true,false,true,false,true,false,true]) ++ (rep [false,true,false,true,false,true,false,true] (n)) ++ ([true,false,true,false]) = ([true,false,true,false,true,false,true,false,true]) ++ (rep [false,true,false,true,false,true,false,true] (n)) ++ ([true,false,true,false]) := by
  rfl

theorem growth (n : Nat) : run0 table (74+40*n) (family n) = some (family (n+1)) := by
  have H := (join0 (join0 (join0 (join0 (phase0 n) (phase1 n)) (phase2 n)) (phase3 n)) (phase4 n))
  rw [show 4+24*n+53+16*n+17=74+40*n by omega] at H
  simpa only [family,rep,List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using H

theorem never (m : Machine) (hm : compatible table m) : NeverHalts m :=
  never_of_growth table family 14 (fun n => 74+40*n) entry (by intro n; omega) growth m hm

#print axioms never

end M152

namespace M153

-- 1RB0RE_1RC1LF_0RD---_1LD0RA_1RE0LF_1LA0LB

def table : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 0,true => some (some ⟨false,true,4⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 1,true => some (some ⟨true,false,5⟩)
  | 2,false => some (some ⟨false,true,3⟩)
  | 3,false => some (some ⟨true,false,3⟩)
  | 3,true => some (some ⟨false,true,0⟩)
  | 4,false => some (some ⟨true,true,4⟩)
  | 4,true => some (some ⟨false,false,5⟩)
  | 5,false => some (some ⟨true,false,0⟩)
  | 5,true => some (some ⟨false,false,1⟩)
  | _,_ => none

def family (n : Nat) : Z0 := ⟨0,[],([true]) ++ (rep [false,true,false,true] (n)) ++ ([true,false,true,false])⟩

theorem entry : run0 table 14 ⟨0,[],[]⟩ = some (family 0) := by rfl

theorem phase0 (n : Nat) : run0 table 4 ⟨0,[],([true]) ++ (rep [false,true,false,true] (n)) ++ ([true,false,true,false])⟩ = some ⟨2,([false,true]),([true]) ++ (rep [false,true,false,true] (n)) ++ ([true,false,true,false])⟩ := by rfl

theorem local1 (L R : List Bool) : run0 table 12 ⟨2,([false]) ++ (L),([true]) ++ ([false,true,false,true]) ++ (R)⟩ = some ⟨2,([false]) ++ ([true,false,true,false]) ++ (L),([true]) ++ (R)⟩ := by rfl

theorem phase1 (n : Nat) : run0 table (12*n) ⟨2,([false,true]),([true]) ++ (rep [false,true,false,true] (n)) ++ ([true,false,true,false])⟩ = some ⟨2,([false]) ++ (rep [true,false,true,false] (n)) ++ ([true]),([true,true,false,true,false])⟩ := by
  simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using sweepR table 2 [false] [true] [false,true,false,true] [true,false,true,false] 12 local1 n (([true])) (([true,false,true,false]))

theorem phase2 (n : Nat) : run0 table 33 ⟨2,([false]) ++ (rep [true,false,true,false] (n)) ++ ([true]),([true,true,false,true,false])⟩ = some ⟨5,([false,false,true,false]) ++ (rep [true,false,true,false] (n)) ++ ([true]),([true,false,true,false])⟩ := by rfl

theorem local3 (L R : List Bool) : run0 table 8 ⟨5,([false,false,true,false]) ++ ([true,false,true,false]) ++ (L),(R)⟩ = some ⟨5,([false,false,true,false]) ++ (L),([false,true,false,true]) ++ (R)⟩ := by rfl

theorem phase3 (n : Nat) : run0 table (8*n) ⟨5,([false,false,true,false]) ++ (rep [true,false,true,false] (n)) ++ ([true]),([true,false,true,false])⟩ = some ⟨5,([false,false,true,false,true]),(rep [false,true,false,true] (n)) ++ ([true,false,true,false])⟩ := by
  simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using sweepL table 5 [false,false,true,false] [] [true,false,true,false] [false,true,false,true] 8 local3 n (([true])) (([true,false,true,false]))

theorem phase4 (n : Nat) : run0 table 9 ⟨5,([false,false,true,false,true]),(rep [false,true,false,true] (n)) ++ ([true,false,true,false])⟩ = some ⟨0,[],([true,false,true,false,true]) ++ (rep [false,true,false,true] (n)) ++ ([true,false,true,false])⟩ := by rfl

theorem finalL (n : Nat) : ([] : List Bool) = [] := by
  rfl

theorem finalR (n : Nat) : ([true,false,true,false,true]) ++ (rep [false,true,false,true] (n)) ++ ([true,false,true,false]) = ([true,false,true,false,true]) ++ (rep [false,true,false,true] (n)) ++ ([true,false,true,false]) := by
  rfl

theorem growth (n : Nat) : run0 table (46+20*n) (family n) = some (family (n+1)) := by
  have H := (join0 (join0 (join0 (join0 (phase0 n) (phase1 n)) (phase2 n)) (phase3 n)) (phase4 n))
  rw [show 4+12*n+33+8*n+9=46+20*n by omega] at H
  simpa only [family,rep,List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using H

theorem never (m : Machine) (hm : compatible table m) : NeverHalts m :=
  never_of_growth table family 14 (fun n => 46+20*n) entry (by intro n; omega) growth m hm

#print axioms never

end M153

namespace M169

-- 1RB0RE_1RC0LE_0RD1LD_1LD0RA_0LB0LF_1LE---

def table : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 0,true => some (some ⟨false,true,4⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 1,true => some (some ⟨false,false,4⟩)
  | 2,false => some (some ⟨false,true,3⟩)
  | 2,true => some (some ⟨true,false,3⟩)
  | 3,false => some (some ⟨true,false,3⟩)
  | 3,true => some (some ⟨false,true,0⟩)
  | 4,false => some (some ⟨false,false,1⟩)
  | 4,true => some (some ⟨false,false,5⟩)
  | 5,false => some (some ⟨true,false,4⟩)
  | _,_ => none

def family (n : Nat) : Z0 := ⟨2,([false,true,true,false,false,true,true,false,false,true]) ++ (rep [true,false,false,true,true,false,false,true] (n)),[]⟩

theorem entry : run0 table 44 ⟨0,[],[]⟩ = some (family 0) := by rfl

theorem phase0 (n : Nat) : run0 table 16 ⟨2,([false,true,true,false,false,true,true,false,false,true]) ++ (rep [true,false,false,true,true,false,false,true] (n)),[]⟩ = some ⟨4,([true,false,false,true,true,false,false,true]) ++ (rep [true,false,false,true,true,false,false,true] (n)),([false,true,false])⟩ := by rfl

theorem local1 (L R : List Bool) : run0 table 8 ⟨4,([true,false,false,true,true,false,false,true]) ++ ([true,false,false,true,true,false,false,true]) ++ (L),(R)⟩ = some ⟨4,([true,false,false,true,true,false,false,true]) ++ (L),([false,false,true,false,false,false,true,false]) ++ (R)⟩ := by rfl

theorem phase1 (n : Nat) : run0 table (8*n) ⟨4,([true,false,false,true,true,false,false,true]) ++ (rep [true,false,false,true,true,false,false,true] (n)),([false,true,false])⟩ = some ⟨4,([true,false,false,true,true,false,false,true]),(rep [false,false,true,false,false,false,true,false] (n)) ++ ([false,true,false])⟩ := by
  simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using sweepL table 4 [true,false,false,true,true,false,false,true] [] [true,false,false,true,true,false,false,true] [false,false,true,false,false,false,true,false] 8 local1 n ([]) (([false,true,false]))

theorem phase2 (n : Nat) : run0 table 19 ⟨4,([true,false,false,true,true,false,false,true]),(rep [false,false,true,false,false,false,true,false] (n)) ++ ([false,true,false])⟩ = some ⟨2,([false,true]),([true,false,false,true,false,false,false,true,false]) ++ (rep [false,false,true,false,false,false,true,false] (n)) ++ ([false,true,false])⟩ := by rfl

theorem local3 (L R : List Bool) : run0 table 36 ⟨2,([false]) ++ (L),([true,false,false,true,false,false,false,true,false]) ++ ([false,false,true,false,false,false,true,false]) ++ (R)⟩ = some ⟨2,([false]) ++ ([true,true,false,false,true,true,false,false]) ++ (L),([true,false,false,true,false,false,false,true,false]) ++ (R)⟩ := by rfl

theorem phase3 (n : Nat) : run0 table (36*n) ⟨2,([false,true]),([true,false,false,true,false,false,false,true,false]) ++ (rep [false,false,true,false,false,false,true,false] (n)) ++ ([false,true,false])⟩ = some ⟨2,([false]) ++ (rep [true,true,false,false,true,true,false,false] (n)) ++ ([true]),([true,false,false,true,false,false,false,true,false,false,true,false])⟩ := by
  simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using sweepR table 2 [false] [true,false,false,true,false,false,false,true,false] [false,false,true,false,false,false,true,false] [true,true,false,false,true,true,false,false] 36 local3 n (([true])) (([false,true,false]))

theorem phase4 (n : Nat) : run0 table 39 ⟨2,([false]) ++ (rep [true,true,false,false,true,true,false,false] (n)) ++ ([true]),([true,false,false,true,false,false,false,true,false,false,true,false])⟩ = some ⟨1,([true,true,false,false,true,true,false,false,true,true,false,false]) ++ (rep [true,true,false,false,true,true,false,false] (n)) ++ ([true]),([false])⟩ := by rfl

theorem local5 (L R : List Bool) : run0 table 8 ⟨1,([true,true,false,false,true,true,false,false,true,true,false,false]) ++ ([true,true,false,false,true,true,false,false]) ++ (L),(R)⟩ = some ⟨1,([true,true,false,false,true,true,false,false,true,true,false,false]) ++ (L),([false,true,false,false,false,true,false,false]) ++ (R)⟩ := by rfl

theorem phase5 (n : Nat) : run0 table (8*n) ⟨1,([true,true,false,false,true,true,false,false,true,true,false,false]) ++ (rep [true,true,false,false,true,true,false,false] (n)) ++ ([true]),([false])⟩ = some ⟨1,([true,true,false,false,true,true,false,false,true,true,false,false,true]),(rep [false,true,false,false,false,true,false,false] (n)) ++ ([false])⟩ := by
  simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using sweepL table 1 [true,true,false,false,true,true,false,false,true,true,false,false] [] [true,true,false,false,true,true,false,false] [false,true,false,false,false,true,false,false] 8 local5 n (([true])) (([false]))

theorem phase6 (n : Nat) : run0 table 24 ⟨1,([true,true,false,false,true,true,false,false,true,true,false,false,true]),(rep [false,true,false,false,false,true,false,false] (n)) ++ ([false])⟩ = some ⟨2,([false,true]),([true,false,false,true,false,false,false,true,false,false,false,true,false,false]) ++ (rep [false,true,false,false,false,true,false,false] (n)) ++ ([false])⟩ := by rfl

theorem local7 (L R : List Bool) : run0 table 36 ⟨2,([false]) ++ (L),([true,false,false,true,false,false,false,true,false,false,false,true,false,false]) ++ ([false,true,false,false,false,true,false,false]) ++ (R)⟩ = some ⟨2,([false]) ++ ([true,true,false,false,true,true,false,false]) ++ (L),([true,false,false,true,false,false,false,true,false,false,false,true,false,false]) ++ (R)⟩ := by rfl

theorem phase7 (n : Nat) : run0 table (36*n) ⟨2,([false,true]),([true,false,false,true,false,false,false,true,false,false,false,true,false,false]) ++ (rep [false,true,false,false,false,true,false,false] (n)) ++ ([false])⟩ = some ⟨2,([false]) ++ (rep [true,true,false,false,true,true,false,false] (n)) ++ ([true]),([true,false,false,true,false,false,false,true,false,false,false,true,false,false,false])⟩ := by
  simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using sweepR table 2 [false] [true,false,false,true,false,false,false,true,false,false,false,true,false,false] [false,true,false,false,false,true,false,false] [true,true,false,false,true,true,false,false] 36 local7 n (([true])) (([false]))

theorem phase8 (n : Nat) : run0 table 58 ⟨2,([false]) ++ (rep [true,true,false,false,true,true,false,false] (n)) ++ ([true]),([true,false,false,true,false,false,false,true,false,false,false,true,false,false,false])⟩ = some ⟨2,([false,true,true,false,false,true,true,false,false,true,true,false,false,true,true,false,false]) ++ (rep [true,true,false,false,true,true,false,false] (n)) ++ ([true]),[]⟩ := by rfl

theorem finalL (n : Nat) : ([false,true,true,false,false,true,true,false,false,true,true,false,false,true,true,false,false]) ++ (rep [true,true,false,false,true,true,false,false] (n)) ++ ([true]) = ([false,true,true,false,false,true,true,false,false,true,true,false,false,true,true,false,false,true]) ++ (rep [true,false,false,true,true,false,false,true] (n)) := by
  calc
    _ = ([false,true,true,false,false,true,true,false,false,true,true,false,false,true,true,false,false,true]) ++ (rep [true,false,false,true,true,false,false,true] (n)) := by symm; simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using moveCut (([false,true,true,false,false,true,true,false,false,true,true,false,false,true,true,false,false])) ([]) [true,false,false,true,true,false,false] true n

theorem finalR (n : Nat) : ([] : List Bool) = [] := by
  rfl

theorem growth (n : Nat) : run0 table (156+88*n) (family n) = some (family (n+1)) := by
  have H := (join0 (join0 (join0 (join0 (join0 (join0 (join0 (join0 (phase0 n) (phase1 n)) (phase2 n)) (phase3 n)) (phase4 n)) (phase5 n)) (phase6 n)) (phase7 n)) (phase8 n))
  rw [finalL n] at H
  rw [show 16+8*n+19+36*n+39+8*n+24+36*n+58=156+88*n by omega] at H
  simpa only [family,rep,List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using H

theorem never (m : Machine) (hm : compatible table m) : NeverHalts m :=
  never_of_growth table family 44 (fun n => 156+88*n) entry (by intro n; omega) growth m hm

#print axioms never

end M169

namespace M170

-- 1RB0RE_1RC1LA_0RD0LD_1LD0RA_0LB0LF_1LE---

def table : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 0,true => some (some ⟨false,true,4⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 1,true => some (some ⟨true,false,0⟩)
  | 2,false => some (some ⟨false,true,3⟩)
  | 2,true => some (some ⟨false,false,3⟩)
  | 3,false => some (some ⟨true,false,3⟩)
  | 3,true => some (some ⟨false,true,0⟩)
  | 4,false => some (some ⟨false,false,1⟩)
  | 4,true => some (some ⟨false,false,5⟩)
  | 5,false => some (some ⟨true,false,4⟩)
  | _,_ => none

def family (n : Nat) : Z0 := ⟨2,([false,true,true,false]) ++ (rep [false,true,true,false,true,false] (n)) ++ ([true,false,false,true]),[]⟩

theorem entry : run0 table 26 ⟨0,[],[]⟩ = some (family 0) := by rfl

theorem phase0 (n : Nat) : run0 table 4 ⟨2,([false,true,true,false]) ++ (rep [false,true,true,false,true,false] (n)) ++ ([true,false,false,true]),[]⟩ = some ⟨0,([true,false,true,false]) ++ (rep [false,true,true,false,true,false] (n)) ++ ([true,false,false,true]),([true])⟩ := by rfl

theorem local1 (L R : List Bool) : run0 table 12 ⟨0,([true,false,true,false]) ++ ([false,true,true,false,true,false]) ++ (L),([true]) ++ (R)⟩ = some ⟨0,([true,false,true,false]) ++ (L),([true]) ++ ([false,true,false,false,true,false]) ++ (R)⟩ := by rfl

theorem phase1 (n : Nat) : run0 table (12*n) ⟨0,([true,false,true,false]) ++ (rep [false,true,true,false,true,false] (n)) ++ ([true,false,false,true]),([true])⟩ = some ⟨0,([true,false,true,false,true,false,false,true]),([true]) ++ (rep [false,true,false,false,true,false] (n))⟩ := by
  simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using sweepL table 0 [true,false,true,false] [true] [false,true,true,false,true,false] [false,true,false,false,true,false] 12 local1 n (([true,false,false,true])) ([])

theorem phase2 (n : Nat) : run0 table 26 ⟨0,([true,false,true,false,true,false,false,true]),([true]) ++ (rep [false,true,false,false,true,false] (n))⟩ = some ⟨3,([true,true,false,false,true]),([false,false,true,false,false,true,false]) ++ (rep [false,true,false,false,true,false] (n))⟩ := by rfl

theorem local3 (L R : List Bool) : run0 table 8 ⟨3,([true]) ++ (L),([false,false,true,false,false,true,false]) ++ ([false,true,false,false,true,false]) ++ (R)⟩ = some ⟨3,([true]) ++ ([false,true,true,false,true,false]) ++ (L),([false,false,true,false,false,true,false]) ++ (R)⟩ := by rfl

theorem phase3 (n : Nat) : run0 table (8*n) ⟨3,([true,true,false,false,true]),([false,false,true,false,false,true,false]) ++ (rep [false,true,false,false,true,false] (n))⟩ = some ⟨3,([true]) ++ (rep [false,true,true,false,true,false] (n)) ++ ([true,false,false,true]),([false,false,true,false,false,true,false])⟩ := by
  simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using sweepR table 3 [true] [false,false,true,false,false,true,false] [false,true,false,false,true,false] [false,true,true,false,true,false] 8 local3 n (([true,false,false,true])) ([])

theorem phase4 (n : Nat) : run0 table 11 ⟨3,([true]) ++ (rep [false,true,true,false,true,false] (n)) ++ ([true,false,false,true]),([false,false,true,false,false,true,false])⟩ = some ⟨2,([false,true,true,false,false,true,true,false,true,false]) ++ (rep [false,true,true,false,true,false] (n)) ++ ([true,false,false,true]),[]⟩ := by rfl

theorem finalL (n : Nat) : ([false,true,true,false,false,true,true,false,true,false]) ++ (rep [false,true,true,false,true,false] (n)) ++ ([true,false,false,true]) = ([false,true,true,false,false,true,true,false,true,false]) ++ (rep [false,true,true,false,true,false] (n)) ++ ([true,false,false,true]) := by
  rfl

theorem finalR (n : Nat) : ([] : List Bool) = [] := by
  rfl

theorem growth (n : Nat) : run0 table (41+20*n) (family n) = some (family (n+1)) := by
  have H := (join0 (join0 (join0 (join0 (phase0 n) (phase1 n)) (phase2 n)) (phase3 n)) (phase4 n))
  rw [show 4+12*n+26+8*n+11=41+20*n by omega] at H
  simpa only [family,rep,List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using H

theorem never (m : Machine) (hm : compatible table m) : NeverHalts m :=
  never_of_growth table family 26 (fun n => 41+20*n) entry (by intro n; omega) growth m hm

#print axioms never

end M170

namespace M171

-- 1RB0RE_1RC1LA_0RD1LD_1LD0RA_0LB0LF_1LE---

def table : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 0,true => some (some ⟨false,true,4⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 1,true => some (some ⟨true,false,0⟩)
  | 2,false => some (some ⟨false,true,3⟩)
  | 2,true => some (some ⟨true,false,3⟩)
  | 3,false => some (some ⟨true,false,3⟩)
  | 3,true => some (some ⟨false,true,0⟩)
  | 4,false => some (some ⟨false,false,1⟩)
  | 4,true => some (some ⟨false,false,5⟩)
  | 5,false => some (some ⟨true,false,4⟩)
  | _,_ => none

def family (n : Nat) : Z0 := ⟨4,[],([true,false,false,true,false,true,false,false,true,false]) ++ (rep [true,false,false,true,false] (n)) ++ ([false,true,false])⟩

theorem entry : run0 table 118 ⟨0,[],[]⟩ = some (family 0) := by rfl

theorem phase0 (n : Nat) : run0 table 2 ⟨4,[],([true,false,false,true,false,true,false,false,true,false]) ++ (rep [true,false,false,true,false] (n)) ++ ([false,true,false])⟩ = some ⟨2,([false,true]),([true,false,false,true,false,true,false,false,true,false]) ++ (rep [true,false,false,true,false] (n)) ++ ([false,true,false])⟩ := by rfl

theorem local1 (L R : List Bool) : run0 table 9 ⟨2,([false]) ++ (L),([true,false,false,true,false,true,false,false,true,false]) ++ ([true,false,false,true,false]) ++ (R)⟩ = some ⟨2,([false]) ++ ([true,false,true,false,false]) ++ (L),([true,false,false,true,false,true,false,false,true,false]) ++ (R)⟩ := by rfl

theorem phase1 (n : Nat) : run0 table (9*n) ⟨2,([false,true]),([true,false,false,true,false,true,false,false,true,false]) ++ (rep [true,false,false,true,false] (n)) ++ ([false,true,false])⟩ = some ⟨2,([false]) ++ (rep [true,false,true,false,false] (n)) ++ ([true]),([true,false,false,true,false,true,false,false,true,false,false,true,false])⟩ := by
  simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using sweepR table 2 [false] [true,false,false,true,false,true,false,false,true,false] [true,false,false,true,false] [true,false,true,false,false] 9 local1 n (([true])) (([false,true,false]))

theorem phase2 (n : Nat) : run0 table 55 ⟨2,([false]) ++ (rep [true,false,true,false,false] (n)) ++ ([true]),([true,false,false,true,false,true,false,false,true,false,false,true,false])⟩ = some ⟨1,([true,true,true,false,false,true,false,true,false,false]) ++ (rep [true,false,true,false,false] (n)) ++ ([true]),([false,true,false,false,true,false])⟩ := by rfl

theorem local3 (L R : List Bool) : run0 table 9 ⟨1,([true,true,true,false,false,true,false,true,false,false]) ++ ([true,false,true,false,false]) ++ (L),(R)⟩ = some ⟨1,([true,true,true,false,false,true,false,true,false,false]) ++ (L),([false,true,false,true,false]) ++ (R)⟩ := by rfl

theorem phase3 (n : Nat) : run0 table (9*n) ⟨1,([true,true,true,false,false,true,false,true,false,false]) ++ (rep [true,false,true,false,false] (n)) ++ ([true]),([false,true,false,false,true,false])⟩ = some ⟨1,([true,true,true,false,false,true,false,true,false,false,true]),(rep [false,true,false,true,false] (n)) ++ ([false,true,false,false,true,false])⟩ := by
  simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using sweepL table 1 [true,true,true,false,false,true,false,true,false,false] [] [true,false,true,false,false] [false,true,false,true,false] 9 local3 n (([true])) (([false,true,false,false,true,false]))

theorem phase4 (n : Nat) : run0 table 22 ⟨1,([true,true,true,false,false,true,false,true,false,false,true]),(rep [false,true,false,true,false] (n)) ++ ([false,true,false,false,true,false])⟩ = some ⟨4,[],([true,false,false,true,false,true,false,false,true,false,true,false]) ++ (rep [false,true,false,true,false] (n)) ++ ([false,true,false,false,true,false])⟩ := by rfl

theorem finalL (n : Nat) : ([] : List Bool) = [] := by
  rfl

theorem finalR (n : Nat) : ([true,false,false,true,false,true,false,false,true,false,true,false]) ++ (rep [false,true,false,true,false] (n)) ++ ([false,true,false,false,true,false]) = ([true,false,false,true,false,true,false,false,true,false,true,false,false,true,false]) ++ (rep [true,false,false,true,false] (n)) ++ ([false,true,false]) := by
  calc
    _ = ([true,false,false,true,false,true,false,false,true,false,true,false,false]) ++ (rep [true,false,true,false,false] (n)) ++ ([true,false,false,true,false]) := by symm; simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using moveCut (([true,false,false,true,false,true,false,false,true,false,true,false])) (([true,false,false,true,false])) [true,false,true,false] false n
    _ = ([true,false,false,true,false,true,false,false,true,false,true,false,false,true]) ++ (rep [false,true,false,false,true] (n)) ++ ([false,false,true,false]) := by symm; simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using moveCut (([true,false,false,true,false,true,false,false,true,false,true,false,false])) (([false,false,true,false])) [false,true,false,false] true n
    _ = ([true,false,false,true,false,true,false,false,true,false,true,false,false,true,false]) ++ (rep [true,false,false,true,false] (n)) ++ ([false,true,false]) := by symm; simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using moveCut (([true,false,false,true,false,true,false,false,true,false,true,false,false,true])) (([false,true,false])) [true,false,false,true] false n

theorem growth (n : Nat) : run0 table (79+18*n) (family n) = some (family (n+1)) := by
  have H := (join0 (join0 (join0 (join0 (phase0 n) (phase1 n)) (phase2 n)) (phase3 n)) (phase4 n))
  rw [finalR n] at H
  rw [show 2+9*n+55+9*n+22=79+18*n by omega] at H
  simpa only [family,rep,List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using H

theorem never (m : Machine) (hm : compatible table m) : NeverHalts m :=
  never_of_growth table family 118 (fun n => 79+18*n) entry (by intro n; omega) growth m hm

#print axioms never

end M171

namespace M172

-- 1RB0RE_1RC1LF_0RD---_1LD0RA_0LB0LF_1LE---

def table : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 0,true => some (some ⟨false,true,4⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 1,true => some (some ⟨true,false,5⟩)
  | 2,false => some (some ⟨false,true,3⟩)
  | 3,false => some (some ⟨true,false,3⟩)
  | 3,true => some (some ⟨false,true,0⟩)
  | 4,false => some (some ⟨false,false,1⟩)
  | 4,true => some (some ⟨false,false,5⟩)
  | 5,false => some (some ⟨true,false,4⟩)
  | _,_ => none

def family (n : Nat) : Z0 := ⟨1,([false,true]) ++ (rep [false,false,true,false,false,true] (n)),[]⟩

theorem entry : run0 table 1 ⟨0,[],[]⟩ = some (family 0) := by rfl

theorem phase0 (n : Nat) : run0 table 7 ⟨1,([false,true]) ++ (rep [false,false,true,false,false,true] (n)),[]⟩ = some ⟨5,([false,false,true]) ++ (rep [false,false,true,false,false,true] (n)),([false])⟩ := by rfl

theorem local1 (L R : List Bool) : run0 table 6 ⟨5,([false,false,true]) ++ ([false,false,true,false,false,true]) ++ (L),(R)⟩ = some ⟨5,([false,false,true]) ++ (L),([true,false,true,true,false,true]) ++ (R)⟩ := by rfl

theorem phase1 (n : Nat) : run0 table (6*n) ⟨5,([false,false,true]) ++ (rep [false,false,true,false,false,true] (n)),([false])⟩ = some ⟨5,([false,false,true]),(rep [true,false,true,true,false,true] (n)) ++ ([false])⟩ := by
  simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using sweepL table 5 [false,false,true] [] [false,false,true,false,false,true] [true,false,true,true,false,true] 6 local1 n ([]) (([false]))

theorem phase2 (n : Nat) : run0 table 6 ⟨5,([false,false,true]),(rep [true,false,true,true,false,true] (n)) ++ ([false])⟩ = some ⟨2,([false,true]),([true,true,false,true]) ++ (rep [true,false,true,true,false,true] (n)) ++ ([false])⟩ := by rfl

theorem local3 (L R : List Bool) : run0 table 10 ⟨2,([false]) ++ (L),([true,true,false,true]) ++ ([true,false,true,true,false,true]) ++ (R)⟩ = some ⟨2,([false]) ++ ([true,false,false,true,false,false]) ++ (L),([true,true,false,true]) ++ (R)⟩ := by rfl

theorem phase3 (n : Nat) : run0 table (10*n) ⟨2,([false,true]),([true,true,false,true]) ++ (rep [true,false,true,true,false,true] (n)) ++ ([false])⟩ = some ⟨2,([false]) ++ (rep [true,false,false,true,false,false] (n)) ++ ([true]),([true,true,false,true,false])⟩ := by
  simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using sweepR table 2 [false] [true,true,false,true] [true,false,true,true,false,true] [true,false,false,true,false,false] 10 local3 n (([true])) (([false]))

theorem phase4 (n : Nat) : run0 table 8 ⟨2,([false]) ++ (rep [true,false,false,true,false,false] (n)) ++ ([true]),([true,true,false,true,false])⟩ = some ⟨1,([false,true,false,false,true,false,false]) ++ (rep [true,false,false,true,false,false] (n)) ++ ([true]),[]⟩ := by rfl

theorem finalL (n : Nat) : ([false,true,false,false,true,false,false]) ++ (rep [true,false,false,true,false,false] (n)) ++ ([true]) = ([false,true,false,false,true,false,false,true]) ++ (rep [false,false,true,false,false,true] (n)) := by
  calc
    _ = ([false,true,false,false,true,false,false,true]) ++ (rep [false,false,true,false,false,true] (n)) := by symm; simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using moveCut (([false,true,false,false,true,false,false])) ([]) [false,false,true,false,false] true n

theorem finalR (n : Nat) : ([] : List Bool) = [] := by
  rfl

theorem growth (n : Nat) : run0 table (21+16*n) (family n) = some (family (n+1)) := by
  have H := (join0 (join0 (join0 (join0 (phase0 n) (phase1 n)) (phase2 n)) (phase3 n)) (phase4 n))
  rw [finalL n] at H
  rw [show 7+6*n+6+10*n+8=21+16*n by omega] at H
  simpa only [family,rep,List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using H

theorem never (m : Machine) (hm : compatible table m) : NeverHalts m :=
  never_of_growth table family 1 (fun n => 21+16*n) entry (by intro n; omega) growth m hm

#print axioms never

end M172

end BB6.Agent11Raw39B0REPumps
