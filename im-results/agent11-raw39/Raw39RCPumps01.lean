import SweepPumping
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedVariables false
namespace BB6.Agent11Raw39RCPumps
open BB6Coverage BB6Coverage.Agent31Pump


namespace M118

-- 1RB0RC_1RC1LF_0RD0LF_1LD0RA_1LC---_0LE1RA

def table : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 0,true => some (some ⟨false,true,2⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 1,true => some (some ⟨true,false,5⟩)
  | 2,false => some (some ⟨false,true,3⟩)
  | 2,true => some (some ⟨false,false,5⟩)
  | 3,false => some (some ⟨true,false,3⟩)
  | 3,true => some (some ⟨false,true,0⟩)
  | 4,false => some (some ⟨true,false,2⟩)
  | 5,false => some (some ⟨false,false,4⟩)
  | 5,true => some (some ⟨true,true,0⟩)
  | _,_ => none

def family (n : Nat) : Z0 := ⟨2,[],([true,false,false,true,false,false,true,true]) ++ (rep [true,true,false,false,true,true] (n))⟩

theorem entry : run0 table 62 ⟨0,[],[]⟩ = some (family 0) := by rfl

theorem phase0 (n : Nat) : run0 table 1 ⟨2,[],([true,false,false,true,false,false,true,true]) ++ (rep [true,true,false,false,true,true] (n))⟩ = some ⟨3,([true,false]),([false,false,true,false,false,true,true]) ++ (rep [true,true,false,false,true,true] (n))⟩ := by rfl

theorem local1 (L R : List Bool) : run0 table 14 ⟨3,([true]) ++ (L),([false,false,true,false,false,true,true]) ++ ([true,true,false,false,true,true]) ++ (R)⟩ = some ⟨3,([true]) ++ ([false,true,true,true,true,false]) ++ (L),([false,false,true,false,false,true,true]) ++ (R)⟩ := by rfl

theorem phase1 (n : Nat) : run0 table (14*n) ⟨3,([true,false]),([false,false,true,false,false,true,true]) ++ (rep [true,true,false,false,true,true] (n))⟩ = some ⟨3,([true]) ++ (rep [false,true,true,true,true,false] (n)) ++ ([false]),([false,false,true,false,false,true,true])⟩ := by
  simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using sweepR table 3 [true] [false,false,true,false,false,true,true] [true,true,false,false,true,true] [false,true,true,true,true,false] 14 local1 n (([false])) ([])

theorem phase2 (n : Nat) : run0 table 13 ⟨3,([true]) ++ (rep [false,true,true,true,true,false] (n)) ++ ([false]),([false,false,true,false,false,true,true])⟩ = some ⟨3,([false,false,false,true,true,true,true,false]) ++ (rep [false,true,true,true,true,false] (n)) ++ ([false]),([true,true])⟩ := by rfl

theorem local3 (L R : List Bool) : run0 table 48 ⟨3,([false,false,false,true,true,true,true,false]) ++ ([false,true,true,true,true,false]) ++ (L),(R)⟩ = some ⟨3,([false,false,false,true,true,true,true,false]) ++ (L),([true,false,false,true,true,true]) ++ (R)⟩ := by rfl

theorem phase3 (n : Nat) : run0 table (48*n) ⟨3,([false,false,false,true,true,true,true,false]) ++ (rep [false,true,true,true,true,false] (n)) ++ ([false]),([true,true])⟩ = some ⟨3,([false,false,false,true,true,true,true,false,false]),(rep [true,false,false,true,true,true] (n)) ++ ([true,true])⟩ := by
  simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using sweepL table 3 [false,false,false,true,true,true,true,false] [] [false,true,true,true,true,false] [true,false,false,true,true,true] 48 local3 n (([false])) (([true,true]))

theorem phase4 (n : Nat) : run0 table 42 ⟨3,([false,false,false,true,true,true,true,false,false]),(rep [true,false,false,true,true,true] (n)) ++ ([true,true])⟩ = some ⟨3,([true,false]),([false,false,true,false,false,true,true,true]) ++ (rep [true,false,false,true,true,true] (n)) ++ ([true,true])⟩ := by rfl

theorem local5 (L R : List Bool) : run0 table 14 ⟨3,([true]) ++ (L),([false,false,true,false,false,true,true,true]) ++ ([true,false,false,true,true,true]) ++ (R)⟩ = some ⟨3,([true]) ++ ([false,true,true,true,true,false]) ++ (L),([false,false,true,false,false,true,true,true]) ++ (R)⟩ := by rfl

theorem phase5 (n : Nat) : run0 table (14*n) ⟨3,([true,false]),([false,false,true,false,false,true,true,true]) ++ (rep [true,false,false,true,true,true] (n)) ++ ([true,true])⟩ = some ⟨3,([true]) ++ (rep [false,true,true,true,true,false] (n)) ++ ([false]),([false,false,true,false,false,true,true,true,true,true])⟩ := by
  simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using sweepR table 3 [true] [false,false,true,false,false,true,true,true] [true,false,false,true,true,true] [false,true,true,true,true,false] 14 local5 n (([false])) (([true,true]))

theorem phase6 (n : Nat) : run0 table 24 ⟨3,([true]) ++ (rep [false,true,true,true,true,false] (n)) ++ ([false]),([false,false,true,false,false,true,true,true,true,true])⟩ = some ⟨3,([false,false,false,true,true,true,false,false,true,true,true,true,false]) ++ (rep [false,true,true,true,true,false] (n)) ++ ([false]),[]⟩ := by rfl

theorem local7 (L R : List Bool) : run0 table 48 ⟨3,([false,false,false,true,true,true,false,false,true,true,true,true,false]) ++ ([false,true,true,true,true,false]) ++ (L),(R)⟩ = some ⟨3,([false,false,false,true,true,true,false,false,true,true,true,true,false]) ++ (L),([true,true,false,false,true,true]) ++ (R)⟩ := by rfl

theorem phase7 (n : Nat) : run0 table (48*n) ⟨3,([false,false,false,true,true,true,false,false,true,true,true,true,false]) ++ (rep [false,true,true,true,true,false] (n)) ++ ([false]),[]⟩ = some ⟨3,([false,false,false,true,true,true,false,false,true,true,true,true,false,false]),(rep [true,true,false,false,true,true] (n))⟩ := by
  simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using sweepL table 3 [false,false,false,true,true,true,false,false,true,true,true,true,false] [] [false,true,true,true,true,false] [true,true,false,false,true,true] 48 local7 n (([false])) ([])

theorem phase8 (n : Nat) : run0 table 74 ⟨3,([false,false,false,true,true,true,false,false,true,true,true,true,false,false]),(rep [true,true,false,false,true,true] (n))⟩ = some ⟨2,[],([true,false,false,true,false,false,true,true,true,true,false,false,true,true]) ++ (rep [true,true,false,false,true,true] (n))⟩ := by rfl

theorem finalL (n : Nat) : ([] : List Bool) = [] := by
  rfl

theorem finalR (n : Nat) : ([true,false,false,true,false,false,true,true,true,true,false,false,true,true]) ++ (rep [true,true,false,false,true,true] (n)) = ([true,false,false,true,false,false,true,true,true,true,false,false,true,true]) ++ (rep [true,true,false,false,true,true] (n)) := by
  rfl

theorem growth (n : Nat) : run0 table (154+124*n) (family n) = some (family (n+1)) := by
  have H := (join0 (join0 (join0 (join0 (join0 (join0 (join0 (join0 (phase0 n) (phase1 n)) (phase2 n)) (phase3 n)) (phase4 n)) (phase5 n)) (phase6 n)) (phase7 n)) (phase8 n))
  rw [show 1+14*n+13+48*n+42+14*n+24+48*n+74=154+124*n by omega] at H
  simpa only [family,rep,List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using H

theorem never (m : Machine) (hm : compatible table m) : NeverHalts m :=
  never_of_growth table family 62 (fun n => 154+124*n) entry (by intro n; omega) growth m hm

#print axioms never

end M118

namespace M144

-- 1RB0RC_1RC---_0RD0LF_1LD0RA_1LC1RE_1LB0LE

def table : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 0,true => some (some ⟨false,true,2⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 2,false => some (some ⟨false,true,3⟩)
  | 2,true => some (some ⟨false,false,5⟩)
  | 3,false => some (some ⟨true,false,3⟩)
  | 3,true => some (some ⟨false,true,0⟩)
  | 4,false => some (some ⟨true,false,2⟩)
  | 4,true => some (some ⟨true,true,4⟩)
  | 5,false => some (some ⟨true,false,1⟩)
  | 5,true => some (some ⟨false,false,4⟩)
  | _,_ => none

def family (n : Nat) : Z0 := ⟨4,[],([false,false,false,true,false,false]) ++ (rep [false,true,false,false] (n))⟩

theorem entry : run0 table 19 ⟨0,[],[]⟩ = some (family 0) := by rfl

theorem phase0 (n : Nat) : run0 table 2 ⟨4,[],([false,false,false,true,false,false]) ++ (rep [false,true,false,false] (n))⟩ = some ⟨3,([true,false]),([false,false,false,true,false,false]) ++ (rep [false,true,false,false] (n))⟩ := by rfl

theorem local1 (L R : List Bool) : run0 table 4 ⟨3,([true]) ++ (L),([false,false,false,true,false,false]) ++ ([false,true,false,false]) ++ (R)⟩ = some ⟨3,([true]) ++ ([false,true,true,false]) ++ (L),([false,false,false,true,false,false]) ++ (R)⟩ := by rfl

theorem phase1 (n : Nat) : run0 table (4*n) ⟨3,([true,false]),([false,false,false,true,false,false]) ++ (rep [false,true,false,false] (n))⟩ = some ⟨3,([true]) ++ (rep [false,true,true,false] (n)) ++ ([false]),([false,false,false,true,false,false])⟩ := by
  simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using sweepR table 3 [true] [false,false,false,true,false,false] [false,true,false,false] [false,true,true,false] 4 local1 n (([false])) ([])

theorem phase2 (n : Nat) : run0 table 14 ⟨3,([true]) ++ (rep [false,true,true,false] (n)) ++ ([false]),([false,false,false,true,false,false])⟩ = some ⟨1,([false,true,false,false,true,true,false]) ++ (rep [false,true,true,false] (n)) ++ ([false]),([true,false])⟩ := by rfl

theorem local3 (L R : List Bool) : run0 table 18 ⟨1,([false,true,false,false,true,true,false]) ++ ([false,true,true,false]) ++ (L),([true]) ++ (R)⟩ = some ⟨1,([false,true,false,false,true,true,false]) ++ (L),([true]) ++ ([false,false,true,false]) ++ (R)⟩ := by rfl

theorem phase3 (n : Nat) : run0 table (18*n) ⟨1,([false,true,false,false,true,true,false]) ++ (rep [false,true,true,false] (n)) ++ ([false]),([true,false])⟩ = some ⟨1,([false,true,false,false,true,true,false,false]),([true]) ++ (rep [false,false,true,false] (n)) ++ ([false])⟩ := by
  simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using sweepL table 1 [false,true,false,false,true,true,false] [true] [false,true,true,false] [false,false,true,false] 18 local3 n (([false])) (([false]))

theorem phase4 (n : Nat) : run0 table 28 ⟨1,([false,true,false,false,true,true,false,false]),([true]) ++ (rep [false,false,true,false] (n)) ++ ([false])⟩ = some ⟨4,[],([false,false,false,true,false,false,false,true,false]) ++ (rep [false,false,true,false] (n)) ++ ([false])⟩ := by rfl

theorem finalL (n : Nat) : ([] : List Bool) = [] := by
  rfl

theorem finalR (n : Nat) : ([false,false,false,true,false,false,false,true,false]) ++ (rep [false,false,true,false] (n)) ++ ([false]) = ([false,false,false,true,false,false,false,true,false,false]) ++ (rep [false,true,false,false] (n)) := by
  calc
    _ = ([false,false,false,true,false,false,false,true,false,false]) ++ (rep [false,true,false,false] (n)) := by symm; simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using moveCut (([false,false,false,true,false,false,false,true,false])) ([]) [false,true,false] false n

theorem growth (n : Nat) : run0 table (44+22*n) (family n) = some (family (n+1)) := by
  have H := (join0 (join0 (join0 (join0 (phase0 n) (phase1 n)) (phase2 n)) (phase3 n)) (phase4 n))
  rw [finalR n] at H
  rw [show 2+4*n+14+18*n+28=44+22*n by omega] at H
  simpa only [family,rep,List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using H

theorem never (m : Machine) (hm : compatible table m) : NeverHalts m :=
  never_of_growth table family 19 (fun n => 44+22*n) entry (by intro n; omega) growth m hm

#print axioms never

end M144

namespace M145

-- 1RB0RC_1RC1LA_0RD0LF_1LD0RA_0LB---_1LE0RC

def table : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 0,true => some (some ⟨false,true,2⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 1,true => some (some ⟨true,false,0⟩)
  | 2,false => some (some ⟨false,true,3⟩)
  | 2,true => some (some ⟨false,false,5⟩)
  | 3,false => some (some ⟨true,false,3⟩)
  | 3,true => some (some ⟨false,true,0⟩)
  | 4,false => some (some ⟨false,false,1⟩)
  | 5,false => some (some ⟨true,false,4⟩)
  | 5,true => some (some ⟨false,true,2⟩)
  | _,_ => none

def family (n : Nat) : Z0 := ⟨0,[],([true,false,true,false]) ++ (rep [false,true,false,false,true,false] (n))⟩

theorem entry : run0 table 11 ⟨0,[],[]⟩ = some (family 0) := by rfl

theorem phase0 (n : Nat) : run0 table 7 ⟨0,[],([true,false,true,false]) ++ (rep [false,true,false,false,true,false] (n))⟩ = some ⟨2,([false,true]),([true,false,false,true,false]) ++ (rep [false,true,false,false,true,false] (n))⟩ := by rfl

theorem local1 (L R : List Bool) : run0 table 50 ⟨2,([false]) ++ (L),([true,false,false,true,false]) ++ ([false,true,false,false,true,false]) ++ (R)⟩ = some ⟨2,([false]) ++ ([true,true,false,true,true,false]) ++ (L),([true,false,false,true,false]) ++ (R)⟩ := by rfl

theorem phase1 (n : Nat) : run0 table (50*n) ⟨2,([false,true]),([true,false,false,true,false]) ++ (rep [false,true,false,false,true,false] (n))⟩ = some ⟨2,([false]) ++ (rep [true,true,false,true,true,false] (n)) ++ ([true]),([true,false,false,true,false])⟩ := by
  simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using sweepR table 2 [false] [true,false,false,true,false] [false,true,false,false,true,false] [true,true,false,true,true,false] 50 local1 n (([true])) ([])

theorem phase2 (n : Nat) : run0 table 39 ⟨2,([false]) ++ (rep [true,true,false,true,true,false] (n)) ++ ([true]),([true,false,false,true,false])⟩ = some ⟨1,([true,true,false,true,true,false]) ++ (rep [true,true,false,true,true,false] (n)) ++ ([true]),([false,true,false])⟩ := by rfl

theorem local3 (L R : List Bool) : run0 table 10 ⟨1,([true,true,false,true,true,false]) ++ ([true,true,false,true,true,false]) ++ (L),(R)⟩ = some ⟨1,([true,true,false,true,true,false]) ++ (L),([false,true,false,false,true,false]) ++ (R)⟩ := by rfl

theorem phase3 (n : Nat) : run0 table (10*n) ⟨1,([true,true,false,true,true,false]) ++ (rep [true,true,false,true,true,false] (n)) ++ ([true]),([false,true,false])⟩ = some ⟨1,([true,true,false,true,true,false,true]),(rep [false,true,false,false,true,false] (n)) ++ ([false,true,false])⟩ := by
  simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using sweepL table 1 [true,true,false,true,true,false] [] [true,true,false,true,true,false] [false,true,false,false,true,false] 10 local3 n (([true])) (([false,true,false]))

theorem phase4 (n : Nat) : run0 table 11 ⟨1,([true,true,false,true,true,false,true]),(rep [false,true,false,false,true,false] (n)) ++ ([false,true,false])⟩ = some ⟨0,[],([true,false,true,false,false,true,false]) ++ (rep [false,true,false,false,true,false] (n)) ++ ([false,true,false])⟩ := by rfl

theorem finalL (n : Nat) : ([] : List Bool) = [] := by
  rfl

theorem finalR (n : Nat) : ([true,false,true,false,false,true,false]) ++ (rep [false,true,false,false,true,false] (n)) ++ ([false,true,false]) = ([true,false,true,false,false,true,false,false,true,false]) ++ (rep [false,true,false,false,true,false] (n)) := by
  calc
    _ = ([true,false,true,false,false,true,false,false]) ++ (rep [true,false,false,true,false,false] (n)) ++ ([true,false]) := by symm; simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using moveCut (([true,false,true,false,false,true,false])) (([true,false])) [true,false,false,true,false] false n
    _ = ([true,false,true,false,false,true,false,false,true]) ++ (rep [false,false,true,false,false,true] (n)) ++ ([false]) := by symm; simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using moveCut (([true,false,true,false,false,true,false,false])) (([false])) [false,false,true,false,false] true n
    _ = ([true,false,true,false,false,true,false,false,true,false]) ++ (rep [false,true,false,false,true,false] (n)) := by symm; simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using moveCut (([true,false,true,false,false,true,false,false,true])) ([]) [false,true,false,false,true] false n

theorem growth (n : Nat) : run0 table (57+60*n) (family n) = some (family (n+1)) := by
  have H := (join0 (join0 (join0 (join0 (phase0 n) (phase1 n)) (phase2 n)) (phase3 n)) (phase4 n))
  rw [finalR n] at H
  rw [show 7+50*n+39+10*n+11=57+60*n by omega] at H
  simpa only [family,rep,List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using H

theorem never (m : Machine) (hm : compatible table m) : NeverHalts m :=
  never_of_growth table family 11 (fun n => 57+60*n) entry (by intro n; omega) growth m hm

#print axioms never

end M145

namespace M156

-- 1RB0RC_1RC1LB_0RD0LF_1LD0RA_1LA---_1LE1RB

def table : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 0,true => some (some ⟨false,true,2⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 1,true => some (some ⟨true,false,1⟩)
  | 2,false => some (some ⟨false,true,3⟩)
  | 2,true => some (some ⟨false,false,5⟩)
  | 3,false => some (some ⟨true,false,3⟩)
  | 3,true => some (some ⟨false,true,0⟩)
  | 4,false => some (some ⟨true,false,0⟩)
  | 5,false => some (some ⟨true,false,4⟩)
  | 5,true => some (some ⟨true,true,1⟩)
  | _,_ => none

def family (n : Nat) : Z0 := ⟨1,[],([true,true,true]) ++ (rep [true,true,true,true] (n)) ++ ([false,true,false])⟩

theorem entry : run0 table 17 ⟨0,[],[]⟩ = some (family 0) := by rfl

theorem phase0 (n : Nat) : run0 table 1 ⟨1,[],([true,true,true]) ++ (rep [true,true,true,true] (n)) ++ ([false,true,false])⟩ = some ⟨2,([true,true]),([true,true]) ++ (rep [true,true,true,true] (n)) ++ ([false,true,false])⟩ := by rfl

theorem local1 (L R : List Bool) : run0 table 12 ⟨2,([true,true]) ++ (L),([true,true]) ++ ([true,true,true,true]) ++ (R)⟩ = some ⟨2,([true,true]) ++ ([true,true,true,true]) ++ (L),([true,true]) ++ (R)⟩ := by rfl

theorem phase1 (n : Nat) : run0 table (12*n) ⟨2,([true,true]),([true,true]) ++ (rep [true,true,true,true] (n)) ++ ([false,true,false])⟩ = some ⟨2,([true,true]) ++ (rep [true,true,true,true] (n)),([true,true,false,true,false])⟩ := by
  simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using sweepR table 2 [true,true] [true,true] [true,true,true,true] [true,true,true,true] 12 local1 n ([]) (([false,true,false]))

theorem phase2 (n : Nat) : run0 table 26 ⟨2,([true,true]) ++ (rep [true,true,true,true] (n)),([true,true,false,true,false])⟩ = some ⟨1,([true,true,true,true,true,true]) ++ (rep [true,true,true,true] (n)),([true,false,true,false])⟩ := by rfl

theorem local3 (L R : List Bool) : run0 table 4 ⟨1,([true,true,true,true,true,true]) ++ ([true,true,true,true]) ++ (L),(R)⟩ = some ⟨1,([true,true,true,true,true,true]) ++ (L),([true,true,true,true]) ++ (R)⟩ := by rfl

theorem phase3 (n : Nat) : run0 table (4*n) ⟨1,([true,true,true,true,true,true]) ++ (rep [true,true,true,true] (n)),([true,false,true,false])⟩ = some ⟨1,([true,true,true,true,true,true]),(rep [true,true,true,true] (n)) ++ ([true,false,true,false])⟩ := by
  simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using sweepL table 1 [true,true,true,true,true,true] [] [true,true,true,true] [true,true,true,true] 4 local3 n ([]) (([true,false,true,false]))

theorem phase4 (n : Nat) : run0 table 6 ⟨1,([true,true,true,true,true,true]),(rep [true,true,true,true] (n)) ++ ([true,false,true,false])⟩ = some ⟨1,[],([true,true,true,true,true,true]) ++ (rep [true,true,true,true] (n)) ++ ([true,false,true,false])⟩ := by rfl

theorem finalL (n : Nat) : ([] : List Bool) = [] := by
  rfl

theorem finalR (n : Nat) : ([true,true,true,true,true,true]) ++ (rep [true,true,true,true] (n)) ++ ([true,false,true,false]) = ([true,true,true,true,true,true,true]) ++ (rep [true,true,true,true] (n)) ++ ([false,true,false]) := by
  calc
    _ = ([true,true,true,true,true,true,true]) ++ (rep [true,true,true,true] (n)) ++ ([false,true,false]) := by symm; simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using moveCut (([true,true,true,true,true,true])) (([false,true,false])) [true,true,true] true n

theorem growth (n : Nat) : run0 table (33+16*n) (family n) = some (family (n+1)) := by
  have H := (join0 (join0 (join0 (join0 (phase0 n) (phase1 n)) (phase2 n)) (phase3 n)) (phase4 n))
  rw [finalR n] at H
  rw [show 1+12*n+26+4*n+6=33+16*n by omega] at H
  simpa only [family,rep,List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using H

theorem never (m : Machine) (hm : compatible table m) : NeverHalts m :=
  never_of_growth table family 17 (fun n => 33+16*n) entry (by intro n; omega) growth m hm

#print axioms never

end M156

namespace M159

-- 1RB0RC_1RC0LF_0RD0LF_1LD0RA_1LB---_1LE0RA

def table : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 0,true => some (some ⟨false,true,2⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 1,true => some (some ⟨false,false,5⟩)
  | 2,false => some (some ⟨false,true,3⟩)
  | 2,true => some (some ⟨false,false,5⟩)
  | 3,false => some (some ⟨true,false,3⟩)
  | 3,true => some (some ⟨false,true,0⟩)
  | 4,false => some (some ⟨true,false,1⟩)
  | 5,false => some (some ⟨true,false,4⟩)
  | 5,true => some (some ⟨false,true,0⟩)
  | _,_ => none

def family (n : Nat) : Z0 := ⟨1,[],([true,true,false,true,true,false]) ++ (rep [true,true,false] (n))⟩

theorem entry : run0 table 13 ⟨0,[],[]⟩ = some (family 0) := by rfl

theorem phase0 (n : Nat) : run0 table 1 ⟨1,[],([true,true,false,true,true,false]) ++ (rep [true,true,false] (n))⟩ = some ⟨2,([true,true]),([true,false,true,true,false]) ++ (rep [true,true,false] (n))⟩ := by rfl

theorem local1 (L R : List Bool) : run0 table 7 ⟨2,([true,true]) ++ (L),([true,false,true,true,false]) ++ ([true,true,false]) ++ (R)⟩ = some ⟨2,([true,true]) ++ ([true,false,false]) ++ (L),([true,false,true,true,false]) ++ (R)⟩ := by rfl

theorem phase1 (n : Nat) : run0 table (7*n) ⟨2,([true,true]),([true,false,true,true,false]) ++ (rep [true,true,false] (n))⟩ = some ⟨2,([true,true]) ++ (rep [true,false,false] (n)),([true,false,true,true,false])⟩ := by
  simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using sweepR table 2 [true,true] [true,false,true,true,false] [true,true,false] [true,false,false] 7 local1 n ([]) ([])

theorem phase2 (n : Nat) : run0 table 20 ⟨2,([true,true]) ++ (rep [true,false,false] (n)),([true,false,true,true,false])⟩ = some ⟨5,([false,false,true,false,false,true,false,false]) ++ (rep [true,false,false] (n)),([false])⟩ := by rfl

theorem local3 (L R : List Bool) : run0 table 3 ⟨5,([false,false,true,false,false,true,false,false]) ++ ([true,false,false]) ++ (L),(R)⟩ = some ⟨5,([false,false,true,false,false,true,false,false]) ++ (L),([false,true,true]) ++ (R)⟩ := by rfl

theorem phase3 (n : Nat) : run0 table (3*n) ⟨5,([false,false,true,false,false,true,false,false]) ++ (rep [true,false,false] (n)),([false])⟩ = some ⟨5,([false,false,true,false,false,true,false,false]),(rep [false,true,true] (n)) ++ ([false])⟩ := by
  simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using sweepL table 5 [false,false,true,false,false,true,false,false] [] [true,false,false] [false,true,true] 3 local3 n ([]) (([false]))

theorem phase4 (n : Nat) : run0 table 8 ⟨5,([false,false,true,false,false,true,false,false]),(rep [false,true,true] (n)) ++ ([false])⟩ = some ⟨1,[],([true,true,false,true,true,false,true,true]) ++ (rep [false,true,true] (n)) ++ ([false])⟩ := by rfl

theorem finalL (n : Nat) : ([] : List Bool) = [] := by
  rfl

theorem finalR (n : Nat) : ([true,true,false,true,true,false,true,true]) ++ (rep [false,true,true] (n)) ++ ([false]) = ([true,true,false,true,true,false,true,true,false]) ++ (rep [true,true,false] (n)) := by
  calc
    _ = ([true,true,false,true,true,false,true,true,false]) ++ (rep [true,true,false] (n)) := by symm; simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using moveCut (([true,true,false,true,true,false,true,true])) ([]) [true,true] false n

theorem growth (n : Nat) : run0 table (29+10*n) (family n) = some (family (n+1)) := by
  have H := (join0 (join0 (join0 (join0 (phase0 n) (phase1 n)) (phase2 n)) (phase3 n)) (phase4 n))
  rw [finalR n] at H
  rw [show 1+7*n+20+3*n+8=29+10*n by omega] at H
  simpa only [family,rep,List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using H

theorem never (m : Machine) (hm : compatible table m) : NeverHalts m :=
  never_of_growth table family 13 (fun n => 29+10*n) entry (by intro n; omega) growth m hm

#print axioms never

end M159

namespace M161

-- 1RB0RC_1RC0RA_0RD0LF_1LD0RA_1LB---_1LE1LA

def table : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 0,true => some (some ⟨false,true,2⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 1,true => some (some ⟨false,true,0⟩)
  | 2,false => some (some ⟨false,true,3⟩)
  | 2,true => some (some ⟨false,false,5⟩)
  | 3,false => some (some ⟨true,false,3⟩)
  | 3,true => some (some ⟨false,true,0⟩)
  | 4,false => some (some ⟨true,false,1⟩)
  | 5,false => some (some ⟨true,false,4⟩)
  | 5,true => some (some ⟨true,false,0⟩)
  | _,_ => none

def family (n : Nat) : Z0 := ⟨1,[],([true,true,false,false,false,true,false,false]) ++ (rep [false,false,false,true,false,false] (n))⟩

theorem entry : run0 table 49 ⟨0,[],[]⟩ = some (family 0) := by rfl

theorem phase0 (n : Nat) : run0 table 4 ⟨1,[],([true,true,false,false,false,true,false,false]) ++ (rep [false,false,false,true,false,false] (n))⟩ = some ⟨1,([true,true]),([false,true,false,false,false,true,false,false]) ++ (rep [false,false,false,true,false,false] (n))⟩ := by rfl

theorem local1 (L R : List Bool) : run0 table 26 ⟨1,([true]) ++ (L),([false,true,false,false,false,true,false,false]) ++ ([false,false,false,true,false,false]) ++ (R)⟩ = some ⟨1,([true]) ++ ([true,true,true,false,true,false]) ++ (L),([false,true,false,false,false,true,false,false]) ++ (R)⟩ := by rfl

theorem phase1 (n : Nat) : run0 table (26*n) ⟨1,([true,true]),([false,true,false,false,false,true,false,false]) ++ (rep [false,false,false,true,false,false] (n))⟩ = some ⟨1,([true]) ++ (rep [true,true,true,false,true,false] (n)) ++ ([true]),([false,true,false,false,false,true,false,false])⟩ := by
  simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using sweepR table 1 [true] [false,true,false,false,false,true,false,false] [false,false,false,true,false,false] [true,true,true,false,true,false] 26 local1 n (([true])) ([])

theorem phase2 (n : Nat) : run0 table 35 ⟨1,([true]) ++ (rep [true,true,true,false,true,false] (n)) ++ ([true]),([false,true,false,false,false,true,false,false])⟩ = some ⟨0,([true,false,true,false,true,false,true,true,true,false,true,false]) ++ (rep [true,true,true,false,true,false] (n)) ++ ([true]),([true])⟩ := by rfl

theorem local3 (L R : List Bool) : run0 table 22 ⟨0,([true,false,true,false,true,false,true,true,true,false,true,false]) ++ ([true,true,true,false,true,false]) ++ (L),([true]) ++ (R)⟩ = some ⟨0,([true,false,true,false,true,false,true,true,true,false,true,false]) ++ (L),([true]) ++ ([false,false,false,true,false,false]) ++ (R)⟩ := by rfl

theorem phase3 (n : Nat) : run0 table (22*n) ⟨0,([true,false,true,false,true,false,true,true,true,false,true,false]) ++ (rep [true,true,true,false,true,false] (n)) ++ ([true]),([true])⟩ = some ⟨0,([true,false,true,false,true,false,true,true,true,false,true,false,true]),([true]) ++ (rep [false,false,false,true,false,false] (n))⟩ := by
  simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using sweepL table 0 [true,false,true,false,true,false,true,true,true,false,true,false] [true] [true,true,true,false,true,false] [false,false,false,true,false,false] 22 local3 n (([true])) ([])

theorem phase4 (n : Nat) : run0 table 43 ⟨0,([true,false,true,false,true,false,true,true,true,false,true,false,true]),([true]) ++ (rep [false,false,false,true,false,false] (n))⟩ = some ⟨1,[],([true,true,false,false,false,true,false,false,false,false,false,true,false,false]) ++ (rep [false,false,false,true,false,false] (n))⟩ := by rfl

theorem finalL (n : Nat) : ([] : List Bool) = [] := by
  rfl

theorem finalR (n : Nat) : ([true,true,false,false,false,true,false,false,false,false,false,true,false,false]) ++ (rep [false,false,false,true,false,false] (n)) = ([true,true,false,false,false,true,false,false,false,false,false,true,false,false]) ++ (rep [false,false,false,true,false,false] (n)) := by
  rfl

theorem growth (n : Nat) : run0 table (82+48*n) (family n) = some (family (n+1)) := by
  have H := (join0 (join0 (join0 (join0 (phase0 n) (phase1 n)) (phase2 n)) (phase3 n)) (phase4 n))
  rw [show 4+26*n+35+22*n+43=82+48*n by omega] at H
  simpa only [family,rep,List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using H

theorem never (m : Machine) (hm : compatible table m) : NeverHalts m :=
  never_of_growth table family 49 (fun n => 82+48*n) entry (by intro n; omega) growth m hm

#print axioms never

end M161

namespace M247

-- 1RB0RC_1RC0RD_0RD0RE_1LD0RA_0LF0LB_1LE---

def table : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 0,true => some (some ⟨false,true,2⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 1,true => some (some ⟨false,true,3⟩)
  | 2,false => some (some ⟨false,true,3⟩)
  | 2,true => some (some ⟨false,true,4⟩)
  | 3,false => some (some ⟨true,false,3⟩)
  | 3,true => some (some ⟨false,true,0⟩)
  | 4,false => some (some ⟨false,false,5⟩)
  | 4,true => some (some ⟨false,false,1⟩)
  | 5,false => some (some ⟨true,false,4⟩)
  | _,_ => none

def family (n : Nat) : Z0 := ⟨4,([false,false,false,false]) ++ (rep [false,false] (n)) ++ ([true]),[]⟩

theorem entry : run0 table 8 ⟨0,[],[]⟩ = some (family 0) := by rfl

theorem local0 (L R : List Bool) : run0 table 2 ⟨4,([false,false,false,false]) ++ ([false,false]) ++ (L),(R)⟩ = some ⟨4,([false,false,false,false]) ++ (L),([true,false]) ++ (R)⟩ := by rfl

theorem phase0 (n : Nat) : run0 table (2*n) ⟨4,([false,false,false,false]) ++ (rep [false,false] (n)) ++ ([true]),[]⟩ = some ⟨4,([false,false,false,false,true]),(rep [true,false] (n))⟩ := by
  simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using sweepL table 4 [false,false,false,false] [] [false,false] [true,false] 2 local0 n (([true])) ([])

theorem phase1 (n : Nat) : run0 table 10 ⟨4,([false,false,false,false,true]),(rep [true,false] (n))⟩ = some ⟨3,([false,false,true,false,false,true]),(rep [true,false] (n))⟩ := by rfl

theorem local2 (L R : List Bool) : run0 table 8 ⟨3,([false,false,true]) ++ (L),([true,false]) ++ (R)⟩ = some ⟨3,([false,false,true]) ++ ([false,false]) ++ (L),(R)⟩ := by rfl

theorem phase2 (n : Nat) : run0 table (8*n) ⟨3,([false,false,true,false,false,true]),(rep [true,false] (n))⟩ = some ⟨3,([false,false,true]) ++ (rep [false,false] (n)) ++ ([false,false,true]),[]⟩ := by
  simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using sweepR table 3 [false,false,true] [] [true,false] [false,false] 8 local2 n (([false,false,true])) ([])

theorem phase3 (n : Nat) : run0 table 5 ⟨3,([false,false,true]) ++ (rep [false,false] (n)) ++ ([false,false,true]),[]⟩ = some ⟨4,([false,false,false,false]) ++ (rep [false,false] (n)) ++ ([false,false,true]),[]⟩ := by rfl

theorem finalL (n : Nat) : ([false,false,false,false]) ++ (rep [false,false] (n)) ++ ([false,false,true]) = ([false,false,false,false,false,false]) ++ (rep [false,false] (n)) ++ ([true]) := by
  calc
    _ = ([false,false,false,false,false]) ++ (rep [false,false] (n)) ++ ([false,true]) := by symm; simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using moveCut (([false,false,false,false])) (([false,true])) [false] false n
    _ = ([false,false,false,false,false,false]) ++ (rep [false,false] (n)) ++ ([true]) := by symm; simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using moveCut (([false,false,false,false,false])) (([true])) [false] false n

theorem finalR (n : Nat) : ([] : List Bool) = [] := by
  rfl

theorem growth (n : Nat) : run0 table (15+10*n) (family n) = some (family (n+1)) := by
  have H := (join0 (join0 (join0 (phase0 n) (phase1 n)) (phase2 n)) (phase3 n))
  rw [finalL n] at H
  rw [show 2*n+10+8*n+5=15+10*n by omega] at H
  simpa only [family,rep,List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using H

theorem never (m : Machine) (hm : compatible table m) : NeverHalts m :=
  never_of_growth table family 8 (fun n => 15+10*n) entry (by intro n; omega) growth m hm

#print axioms never

end M247

namespace M248

-- 1RB0RC_1RC1LC_0RD0RE_1LD0RA_0LF0LB_1LE---

def table : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 0,true => some (some ⟨false,true,2⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 1,true => some (some ⟨true,false,2⟩)
  | 2,false => some (some ⟨false,true,3⟩)
  | 2,true => some (some ⟨false,true,4⟩)
  | 3,false => some (some ⟨true,false,3⟩)
  | 3,true => some (some ⟨false,true,0⟩)
  | 4,false => some (some ⟨false,false,5⟩)
  | 4,true => some (some ⟨false,false,1⟩)
  | 5,false => some (some ⟨true,false,4⟩)
  | _,_ => none

def family (n : Nat) : Z0 := ⟨4,([false,false,false,false]) ++ (rep [false,false] (n)) ++ ([true]),[]⟩

theorem entry : run0 table 8 ⟨0,[],[]⟩ = some (family 0) := by rfl

theorem local0 (L R : List Bool) : run0 table 2 ⟨4,([false,false,false,false]) ++ ([false,false]) ++ (L),(R)⟩ = some ⟨4,([false,false,false,false]) ++ (L),([true,false]) ++ (R)⟩ := by rfl

theorem phase0 (n : Nat) : run0 table (2*n) ⟨4,([false,false,false,false]) ++ (rep [false,false] (n)) ++ ([true]),[]⟩ = some ⟨4,([false,false,false,false,true]),(rep [true,false] (n))⟩ := by
  simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using sweepL table 4 [false,false,false,false] [] [false,false] [true,false] 2 local0 n (([true])) ([])

theorem phase1 (n : Nat) : run0 table 10 ⟨4,([false,false,false,false,true]),(rep [true,false] (n))⟩ = some ⟨2,([true,false,false,true]),([true,false]) ++ (rep [true,false] (n))⟩ := by rfl

theorem local2 (L R : List Bool) : run0 table 8 ⟨2,([true]) ++ (L),([true,false]) ++ ([true,false]) ++ (R)⟩ = some ⟨2,([true]) ++ ([false,false]) ++ (L),([true,false]) ++ (R)⟩ := by rfl

theorem phase2 (n : Nat) : run0 table (8*n) ⟨2,([true,false,false,true]),([true,false]) ++ (rep [true,false] (n))⟩ = some ⟨2,([true]) ++ (rep [false,false] (n)) ++ ([false,false,true]),([true,false])⟩ := by
  simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using sweepR table 2 [true] [true,false] [true,false] [false,false] 8 local2 n (([false,false,true])) ([])

theorem phase3 (n : Nat) : run0 table 9 ⟨2,([true]) ++ (rep [false,false] (n)) ++ ([false,false,true]),([true,false])⟩ = some ⟨4,([false,false,false,false]) ++ (rep [false,false] (n)) ++ ([false,false,true]),[]⟩ := by rfl

theorem finalL (n : Nat) : ([false,false,false,false]) ++ (rep [false,false] (n)) ++ ([false,false,true]) = ([false,false,false,false,false,false]) ++ (rep [false,false] (n)) ++ ([true]) := by
  calc
    _ = ([false,false,false,false,false]) ++ (rep [false,false] (n)) ++ ([false,true]) := by symm; simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using moveCut (([false,false,false,false])) (([false,true])) [false] false n
    _ = ([false,false,false,false,false,false]) ++ (rep [false,false] (n)) ++ ([true]) := by symm; simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using moveCut (([false,false,false,false,false])) (([true])) [false] false n

theorem finalR (n : Nat) : ([] : List Bool) = [] := by
  rfl

theorem growth (n : Nat) : run0 table (19+10*n) (family n) = some (family (n+1)) := by
  have H := (join0 (join0 (join0 (phase0 n) (phase1 n)) (phase2 n)) (phase3 n))
  rw [finalL n] at H
  rw [show 2*n+10+8*n+9=19+10*n by omega] at H
  simpa only [family,rep,List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using H

theorem never (m : Machine) (hm : compatible table m) : NeverHalts m :=
  never_of_growth table family 8 (fun n => 19+10*n) entry (by intro n; omega) growth m hm

#print axioms never

end M248

namespace M249

-- 1RB0RC_1RC0RD_0RD0RE_1LD0RA_0LF1LA_1LE---

def table : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 0,true => some (some ⟨false,true,2⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 1,true => some (some ⟨false,true,3⟩)
  | 2,false => some (some ⟨false,true,3⟩)
  | 2,true => some (some ⟨false,true,4⟩)
  | 3,false => some (some ⟨true,false,3⟩)
  | 3,true => some (some ⟨false,true,0⟩)
  | 4,false => some (some ⟨false,false,5⟩)
  | 4,true => some (some ⟨true,false,0⟩)
  | 5,false => some (some ⟨true,false,4⟩)
  | _,_ => none

def family (n : Nat) : Z0 := ⟨4,([false,false,false,false]) ++ (rep [false,false] (n)) ++ ([true]),[]⟩

theorem entry : run0 table 8 ⟨0,[],[]⟩ = some (family 0) := by rfl

theorem local0 (L R : List Bool) : run0 table 2 ⟨4,([false,false,false,false]) ++ ([false,false]) ++ (L),(R)⟩ = some ⟨4,([false,false,false,false]) ++ (L),([true,false]) ++ (R)⟩ := by rfl

theorem phase0 (n : Nat) : run0 table (2*n) ⟨4,([false,false,false,false]) ++ (rep [false,false] (n)) ++ ([true]),[]⟩ = some ⟨4,([false,false,false,false,true]),(rep [true,false] (n))⟩ := by
  simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using sweepL table 4 [false,false,false,false] [] [false,false] [true,false] 2 local0 n (([true])) ([])

theorem phase1 (n : Nat) : run0 table 8 ⟨4,([false,false,false,false,true]),(rep [true,false] (n))⟩ = some ⟨0,([false,false,false,true]),([true,false]) ++ (rep [true,false] (n))⟩ := by rfl

theorem local2 (L R : List Bool) : run0 table 8 ⟨0,([false]) ++ (L),([true,false]) ++ ([true,false]) ++ (R)⟩ = some ⟨0,([false]) ++ ([false,false]) ++ (L),([true,false]) ++ (R)⟩ := by rfl

theorem phase2 (n : Nat) : run0 table (8*n) ⟨0,([false,false,false,true]),([true,false]) ++ (rep [true,false] (n))⟩ = some ⟨0,([false]) ++ (rep [false,false] (n)) ++ ([false,false,true]),([true,false])⟩ := by
  simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using sweepR table 0 [false] [true,false] [true,false] [false,false] 8 local2 n (([false,false,true])) ([])

theorem phase3 (n : Nat) : run0 table 7 ⟨0,([false]) ++ (rep [false,false] (n)) ++ ([false,false,true]),([true,false])⟩ = some ⟨4,([false,false,false,false]) ++ (rep [false,false] (n)) ++ ([false,false,true]),[]⟩ := by rfl

theorem finalL (n : Nat) : ([false,false,false,false]) ++ (rep [false,false] (n)) ++ ([false,false,true]) = ([false,false,false,false,false,false]) ++ (rep [false,false] (n)) ++ ([true]) := by
  calc
    _ = ([false,false,false,false,false]) ++ (rep [false,false] (n)) ++ ([false,true]) := by symm; simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using moveCut (([false,false,false,false])) (([false,true])) [false] false n
    _ = ([false,false,false,false,false,false]) ++ (rep [false,false] (n)) ++ ([true]) := by symm; simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using moveCut (([false,false,false,false,false])) (([true])) [false] false n

theorem finalR (n : Nat) : ([] : List Bool) = [] := by
  rfl

theorem growth (n : Nat) : run0 table (15+10*n) (family n) = some (family (n+1)) := by
  have H := (join0 (join0 (join0 (phase0 n) (phase1 n)) (phase2 n)) (phase3 n))
  rw [finalL n] at H
  rw [show 2*n+8+8*n+7=15+10*n by omega] at H
  simpa only [family,rep,List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using H

theorem never (m : Machine) (hm : compatible table m) : NeverHalts m :=
  never_of_growth table family 8 (fun n => 15+10*n) entry (by intro n; omega) growth m hm

#print axioms never

end M249

namespace M353

-- 1RB0RC_1RC0LF_0RD0RE_1LD0RA_1LE1LB_---1RE

def table : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 0,true => some (some ⟨false,true,2⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 1,true => some (some ⟨false,false,5⟩)
  | 2,false => some (some ⟨false,true,3⟩)
  | 2,true => some (some ⟨false,true,4⟩)
  | 3,false => some (some ⟨true,false,3⟩)
  | 3,true => some (some ⟨false,true,0⟩)
  | 4,false => some (some ⟨true,false,4⟩)
  | 4,true => some (some ⟨true,false,1⟩)
  | 5,true => some (some ⟨true,true,4⟩)
  | _,_ => none

def family (n : Nat) : Z0 := ⟨1,[],([true,true,true,true,true]) ++ (rep [true,true] (n))⟩

theorem entry : run0 table 13 ⟨0,[],[]⟩ = some (family 0) := by rfl

theorem phase0 (n : Nat) : run0 table 1 ⟨1,[],([true,true,true,true,true]) ++ (rep [true,true] (n))⟩ = some ⟨2,([true,true]),([true,true,true,true]) ++ (rep [true,true] (n))⟩ := by rfl

theorem local1 (L R : List Bool) : run0 table 6 ⟨2,([true]) ++ (L),([true,true,true,true]) ++ ([true,true]) ++ (R)⟩ = some ⟨2,([true]) ++ ([true,true]) ++ (L),([true,true,true,true]) ++ (R)⟩ := by rfl

theorem phase1 (n : Nat) : run0 table (6*n) ⟨2,([true,true]),([true,true,true,true]) ++ (rep [true,true] (n))⟩ = some ⟨2,([true]) ++ (rep [true,true] (n)) ++ ([true]),([true,true,true,true])⟩ := by
  simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using sweepR table 2 [true] [true,true,true,true] [true,true] [true,true] 6 local1 n (([true])) ([])

theorem phase2 (n : Nat) : run0 table 14 ⟨2,([true]) ++ (rep [true,true] (n)) ++ ([true]),([true,true,true,true])⟩ = some ⟨4,([false,true,true,true,true]) ++ (rep [true,true] (n)) ++ ([true]),([true])⟩ := by rfl

theorem local3 (L R : List Bool) : run0 table 4 ⟨4,([false,true,true,true,true]) ++ ([true,true]) ++ (L),(R)⟩ = some ⟨4,([false,true,true,true,true]) ++ (L),([true,true]) ++ (R)⟩ := by rfl

theorem phase3 (n : Nat) : run0 table (4*n) ⟨4,([false,true,true,true,true]) ++ (rep [true,true] (n)) ++ ([true]),([true])⟩ = some ⟨4,([false,true,true,true,true,true]),(rep [true,true] (n)) ++ ([true])⟩ := by
  simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using sweepL table 4 [false,true,true,true,true] [] [true,true] [true,true] 4 local3 n (([true])) (([true]))

theorem phase4 (n : Nat) : run0 table 10 ⟨4,([false,true,true,true,true,true]),(rep [true,true] (n)) ++ ([true])⟩ = some ⟨1,[],([true,true,true,true,true,true]) ++ (rep [true,true] (n)) ++ ([true])⟩ := by rfl

theorem finalL (n : Nat) : ([] : List Bool) = [] := by
  rfl

theorem finalR (n : Nat) : ([true,true,true,true,true,true]) ++ (rep [true,true] (n)) ++ ([true]) = ([true,true,true,true,true,true,true]) ++ (rep [true,true] (n)) := by
  calc
    _ = ([true,true,true,true,true,true,true]) ++ (rep [true,true] (n)) := by symm; simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using moveCut (([true,true,true,true,true,true])) ([]) [true] true n

theorem growth (n : Nat) : run0 table (25+10*n) (family n) = some (family (n+1)) := by
  have H := (join0 (join0 (join0 (join0 (phase0 n) (phase1 n)) (phase2 n)) (phase3 n)) (phase4 n))
  rw [finalR n] at H
  rw [show 1+6*n+14+4*n+10=25+10*n by omega] at H
  simpa only [family,rep,List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using H

theorem never (m : Machine) (hm : compatible table m) : NeverHalts m :=
  never_of_growth table family 13 (fun n => 25+10*n) entry (by intro n; omega) growth m hm

#print axioms never

end M353

end BB6.Agent11Raw39RCPumps
