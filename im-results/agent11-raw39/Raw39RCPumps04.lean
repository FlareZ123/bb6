import SweepPumping
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedVariables false
namespace BB6.Agent11Raw39RCPumps
open BB6Coverage BB6Coverage.Agent31Pump


namespace M1650

-- 1RB0RC_1RC---_0RD1RE_1LD0RA_0LF0LE_0RB1LE

def table : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 0,true => some (some ⟨false,true,2⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 2,false => some (some ⟨false,true,3⟩)
  | 2,true => some (some ⟨true,true,4⟩)
  | 3,false => some (some ⟨true,false,3⟩)
  | 3,true => some (some ⟨false,true,0⟩)
  | 4,false => some (some ⟨false,false,5⟩)
  | 4,true => some (some ⟨false,false,4⟩)
  | 5,false => some (some ⟨false,true,1⟩)
  | 5,true => some (some ⟨true,false,4⟩)
  | _,_ => none

def family (n : Nat) : Z0 := ⟨1,([false,true,false,false,true,false,false,true,false]) ++ (rep [false,true,false,false,true,false] (n)),[]⟩

theorem entry : run0 table 73 ⟨0,[],[]⟩ = some (family 0) := by rfl

theorem phase0 (n : Nat) : run0 table 7 ⟨1,([false,true,false,false,true,false,false,true,false]) ++ (rep [false,true,false,false,true,false] (n)),[]⟩ = some ⟨4,([false,true,false,false,true,false,false,true,false,false,true,false]) ++ (rep [false,true,false,false,true,false] (n)),[]⟩ := by rfl

theorem local1 (L R : List Bool) : run0 table 18 ⟨4,([false,true,false,false,true,false,false,true,false,false,true,false]) ++ ([false,true,false,false,true,false]) ++ (L),(R)⟩ = some ⟨4,([false,true,false,false,true,false,false,true,false,false,true,false]) ++ (L),([false,true,false,false,true,false]) ++ (R)⟩ := by rfl

theorem phase1 (n : Nat) : run0 table (18*n) ⟨4,([false,true,false,false,true,false,false,true,false,false,true,false]) ++ (rep [false,true,false,false,true,false] (n)),[]⟩ = some ⟨4,([false,true,false,false,true,false,false,true,false,false,true,false]),(rep [false,true,false,false,true,false] (n))⟩ := by
  simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using sweepL table 4 [false,true,false,false,true,false,false,true,false,false,true,false] [] [false,true,false,false,true,false] [false,true,false,false,true,false] 18 local1 n ([]) ([])

theorem phase2 (n : Nat) : run0 table 38 ⟨4,([false,true,false,false,true,false,false,true,false,false,true,false]),(rep [false,true,false,false,true,false] (n))⟩ = some ⟨1,([false,false]),([false,true,false,false,true,false,false,true,false,false,true,false]) ++ (rep [false,true,false,false,true,false] (n))⟩ := by rfl

theorem local3 (L R : List Bool) : run0 table 82 ⟨1,([false]) ++ (L),([false,true,false,false,true,false,false,true,false,false,true,false]) ++ ([false,true,false,false,true,false]) ++ (R)⟩ = some ⟨1,([false]) ++ ([false,false,true,false,false,true]) ++ (L),([false,true,false,false,true,false,false,true,false,false,true,false]) ++ (R)⟩ := by rfl

theorem phase3 (n : Nat) : run0 table (82*n) ⟨1,([false,false]),([false,true,false,false,true,false,false,true,false,false,true,false]) ++ (rep [false,true,false,false,true,false] (n))⟩ = some ⟨1,([false]) ++ (rep [false,false,true,false,false,true] (n)) ++ ([false]),([false,true,false,false,true,false,false,true,false,false,true,false])⟩ := by
  simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using sweepR table 1 [false] [false,true,false,false,true,false,false,true,false,false,true,false] [false,true,false,false,true,false] [false,false,true,false,false,true] 82 local3 n (([false])) ([])

theorem phase4 (n : Nat) : run0 table 127 ⟨1,([false]) ++ (rep [false,false,true,false,false,true] (n)) ++ ([false]),([false,true,false,false,true,false,false,true,false,false,true,false])⟩ = some ⟨1,([false,true,false,false,true,false,false,true,false,false,true,false,false,true]) ++ (rep [false,false,true,false,false,true] (n)) ++ ([false]),[]⟩ := by rfl

theorem finalL (n : Nat) : ([false,true,false,false,true,false,false,true,false,false,true,false,false,true]) ++ (rep [false,false,true,false,false,true] (n)) ++ ([false]) = ([false,true,false,false,true,false,false,true,false,false,true,false,false,true,false]) ++ (rep [false,true,false,false,true,false] (n)) := by
  calc
    _ = ([false,true,false,false,true,false,false,true,false,false,true,false,false,true,false]) ++ (rep [false,true,false,false,true,false] (n)) := by symm; simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using moveCut (([false,true,false,false,true,false,false,true,false,false,true,false,false,true])) ([]) [false,true,false,false,true] false n

theorem finalR (n : Nat) : ([] : List Bool) = [] := by
  rfl

theorem growth (n : Nat) : run0 table (172+100*n) (family n) = some (family (n+1)) := by
  have H := (join0 (join0 (join0 (join0 (phase0 n) (phase1 n)) (phase2 n)) (phase3 n)) (phase4 n))
  rw [finalL n] at H
  rw [show 7+18*n+38+82*n+127=172+100*n by omega] at H
  simpa only [family,rep,List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using H

theorem never (m : Machine) (hm : compatible table m) : NeverHalts m :=
  never_of_growth table family 73 (fun n => 172+100*n) entry (by intro n; omega) growth m hm

#print axioms never

end M1650

namespace M1708

-- 1RB0RC_1RC0LF_0RD1RE_1LD0RA_1LB---_0LE0RA

def table : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 0,true => some (some ⟨false,true,2⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 1,true => some (some ⟨false,false,5⟩)
  | 2,false => some (some ⟨false,true,3⟩)
  | 2,true => some (some ⟨true,true,4⟩)
  | 3,false => some (some ⟨true,false,3⟩)
  | 3,true => some (some ⟨false,true,0⟩)
  | 4,false => some (some ⟨true,false,1⟩)
  | 5,false => some (some ⟨false,false,4⟩)
  | 5,true => some (some ⟨false,true,0⟩)
  | _,_ => none

def family (n : Nat) : Z0 := ⟨1,[],([true,false,false,true,false,false,true]) ++ (rep [false,false,true,false,false,true] (n))⟩

theorem entry : run0 table 15 ⟨0,[],[]⟩ = some (family 0) := by rfl

theorem phase0 (n : Nat) : run0 table 1 ⟨1,[],([true,false,false,true,false,false,true]) ++ (rep [false,false,true,false,false,true] (n))⟩ = some ⟨2,([true,true]),([false,false,true,false,false,true]) ++ (rep [false,false,true,false,false,true] (n))⟩ := by rfl

theorem local1 (L R : List Bool) : run0 table 18 ⟨2,([true,true]) ++ (L),([false,false,true,false,false,true]) ++ ([false,false,true,false,false,true]) ++ (R)⟩ = some ⟨2,([true,true]) ++ ([true,false,false,true,false,false]) ++ (L),([false,false,true,false,false,true]) ++ (R)⟩ := by rfl

theorem phase1 (n : Nat) : run0 table (18*n) ⟨2,([true,true]),([false,false,true,false,false,true]) ++ (rep [false,false,true,false,false,true] (n))⟩ = some ⟨2,([true,true]) ++ (rep [true,false,false,true,false,false] (n)),([false,false,true,false,false,true])⟩ := by
  simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using sweepR table 2 [true,true] [false,false,true,false,false,true] [false,false,true,false,false,true] [true,false,false,true,false,false] 18 local1 n ([]) ([])

theorem phase2 (n : Nat) : run0 table 33 ⟨2,([true,true]) ++ (rep [true,false,false,true,false,false] (n)),([false,false,true,false,false,true])⟩ = some ⟨4,([false,true,false,false,true,false,false,true,false,false,true,false,false]) ++ (rep [true,false,false,true,false,false] (n)),[]⟩ := by rfl

theorem local3 (L R : List Bool) : run0 table 6 ⟨4,([false,true,false,false,true,false,false,true,false,false,true,false,false]) ++ ([true,false,false,true,false,false]) ++ (L),(R)⟩ = some ⟨4,([false,true,false,false,true,false,false,true,false,false,true,false,false]) ++ (L),([false,false,true,false,false,true]) ++ (R)⟩ := by rfl

theorem phase3 (n : Nat) : run0 table (6*n) ⟨4,([false,true,false,false,true,false,false,true,false,false,true,false,false]) ++ (rep [true,false,false,true,false,false] (n)),[]⟩ = some ⟨4,([false,true,false,false,true,false,false,true,false,false,true,false,false]),(rep [false,false,true,false,false,true] (n))⟩ := by
  simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using sweepL table 4 [false,true,false,false,true,false,false,true,false,false,true,false,false] [] [true,false,false,true,false,false] [false,false,true,false,false,true] 6 local3 n ([]) ([])

theorem phase4 (n : Nat) : run0 table 13 ⟨4,([false,true,false,false,true,false,false,true,false,false,true,false,false]),(rep [false,false,true,false,false,true] (n))⟩ = some ⟨1,[],([true,false,false,true,false,false,true,false,false,true,false,false,true]) ++ (rep [false,false,true,false,false,true] (n))⟩ := by rfl

theorem finalL (n : Nat) : ([] : List Bool) = [] := by
  rfl

theorem finalR (n : Nat) : ([true,false,false,true,false,false,true,false,false,true,false,false,true]) ++ (rep [false,false,true,false,false,true] (n)) = ([true,false,false,true,false,false,true,false,false,true,false,false,true]) ++ (rep [false,false,true,false,false,true] (n)) := by
  rfl

theorem growth (n : Nat) : run0 table (47+24*n) (family n) = some (family (n+1)) := by
  have H := (join0 (join0 (join0 (join0 (phase0 n) (phase1 n)) (phase2 n)) (phase3 n)) (phase4 n))
  rw [show 1+18*n+33+6*n+13=47+24*n by omega] at H
  simpa only [family,rep,List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using H

theorem never (m : Machine) (hm : compatible table m) : NeverHalts m :=
  never_of_growth table family 15 (fun n => 47+24*n) entry (by intro n; omega) growth m hm

#print axioms never

end M1708

namespace M1956

-- 1RB0RC_1RC---_0RD1RF_1LD0RA_0RB1LF_0LE0LF

def table : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 0,true => some (some ⟨false,true,2⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 2,false => some (some ⟨false,true,3⟩)
  | 2,true => some (some ⟨true,true,5⟩)
  | 3,false => some (some ⟨true,false,3⟩)
  | 3,true => some (some ⟨false,true,0⟩)
  | 4,false => some (some ⟨false,true,1⟩)
  | 4,true => some (some ⟨true,false,5⟩)
  | 5,false => some (some ⟨false,false,4⟩)
  | 5,true => some (some ⟨false,false,5⟩)
  | _,_ => none

def family (n : Nat) : Z0 := ⟨1,([false,true,false,false,true,false,false,true,false]) ++ (rep [false,true,false,false,true,false] (n)),[]⟩

theorem entry : run0 table 73 ⟨0,[],[]⟩ = some (family 0) := by rfl

theorem phase0 (n : Nat) : run0 table 7 ⟨1,([false,true,false,false,true,false,false,true,false]) ++ (rep [false,true,false,false,true,false] (n)),[]⟩ = some ⟨5,([false,true,false,false,true,false,false,true,false,false,true,false]) ++ (rep [false,true,false,false,true,false] (n)),[]⟩ := by rfl

theorem local1 (L R : List Bool) : run0 table 18 ⟨5,([false,true,false,false,true,false,false,true,false,false,true,false]) ++ ([false,true,false,false,true,false]) ++ (L),(R)⟩ = some ⟨5,([false,true,false,false,true,false,false,true,false,false,true,false]) ++ (L),([false,true,false,false,true,false]) ++ (R)⟩ := by rfl

theorem phase1 (n : Nat) : run0 table (18*n) ⟨5,([false,true,false,false,true,false,false,true,false,false,true,false]) ++ (rep [false,true,false,false,true,false] (n)),[]⟩ = some ⟨5,([false,true,false,false,true,false,false,true,false,false,true,false]),(rep [false,true,false,false,true,false] (n))⟩ := by
  simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using sweepL table 5 [false,true,false,false,true,false,false,true,false,false,true,false] [] [false,true,false,false,true,false] [false,true,false,false,true,false] 18 local1 n ([]) ([])

theorem phase2 (n : Nat) : run0 table 38 ⟨5,([false,true,false,false,true,false,false,true,false,false,true,false]),(rep [false,true,false,false,true,false] (n))⟩ = some ⟨1,([false,false]),([false,true,false,false,true,false,false,true,false,false,true,false]) ++ (rep [false,true,false,false,true,false] (n))⟩ := by rfl

theorem local3 (L R : List Bool) : run0 table 82 ⟨1,([false]) ++ (L),([false,true,false,false,true,false,false,true,false,false,true,false]) ++ ([false,true,false,false,true,false]) ++ (R)⟩ = some ⟨1,([false]) ++ ([false,false,true,false,false,true]) ++ (L),([false,true,false,false,true,false,false,true,false,false,true,false]) ++ (R)⟩ := by rfl

theorem phase3 (n : Nat) : run0 table (82*n) ⟨1,([false,false]),([false,true,false,false,true,false,false,true,false,false,true,false]) ++ (rep [false,true,false,false,true,false] (n))⟩ = some ⟨1,([false]) ++ (rep [false,false,true,false,false,true] (n)) ++ ([false]),([false,true,false,false,true,false,false,true,false,false,true,false])⟩ := by
  simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using sweepR table 1 [false] [false,true,false,false,true,false,false,true,false,false,true,false] [false,true,false,false,true,false] [false,false,true,false,false,true] 82 local3 n (([false])) ([])

theorem phase4 (n : Nat) : run0 table 127 ⟨1,([false]) ++ (rep [false,false,true,false,false,true] (n)) ++ ([false]),([false,true,false,false,true,false,false,true,false,false,true,false])⟩ = some ⟨1,([false,true,false,false,true,false,false,true,false,false,true,false,false,true]) ++ (rep [false,false,true,false,false,true] (n)) ++ ([false]),[]⟩ := by rfl

theorem finalL (n : Nat) : ([false,true,false,false,true,false,false,true,false,false,true,false,false,true]) ++ (rep [false,false,true,false,false,true] (n)) ++ ([false]) = ([false,true,false,false,true,false,false,true,false,false,true,false,false,true,false]) ++ (rep [false,true,false,false,true,false] (n)) := by
  calc
    _ = ([false,true,false,false,true,false,false,true,false,false,true,false,false,true,false]) ++ (rep [false,true,false,false,true,false] (n)) := by symm; simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using moveCut (([false,true,false,false,true,false,false,true,false,false,true,false,false,true])) ([]) [false,true,false,false,true] false n

theorem finalR (n : Nat) : ([] : List Bool) = [] := by
  rfl

theorem growth (n : Nat) : run0 table (172+100*n) (family n) = some (family (n+1)) := by
  have H := (join0 (join0 (join0 (join0 (phase0 n) (phase1 n)) (phase2 n)) (phase3 n)) (phase4 n))
  rw [finalL n] at H
  rw [show 7+18*n+38+82*n+127=172+100*n by omega] at H
  simpa only [family,rep,List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using H

theorem never (m : Machine) (hm : compatible table m) : NeverHalts m :=
  never_of_growth table family 73 (fun n => 172+100*n) entry (by intro n; omega) growth m hm

#print axioms never

end M1956

namespace M2011

-- 1RB0RC_1RC0LE_0RD1RF_1LD0RA_0LF0RA_1LB---

def table : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 0,true => some (some ⟨false,true,2⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 1,true => some (some ⟨false,false,4⟩)
  | 2,false => some (some ⟨false,true,3⟩)
  | 2,true => some (some ⟨true,true,5⟩)
  | 3,false => some (some ⟨true,false,3⟩)
  | 3,true => some (some ⟨false,true,0⟩)
  | 4,false => some (some ⟨false,false,5⟩)
  | 4,true => some (some ⟨false,true,0⟩)
  | 5,false => some (some ⟨true,false,1⟩)
  | _,_ => none

def family (n : Nat) : Z0 := ⟨1,[],([true,false,false,true,false,false,true]) ++ (rep [false,false,true,false,false,true] (n))⟩

theorem entry : run0 table 15 ⟨0,[],[]⟩ = some (family 0) := by rfl

theorem phase0 (n : Nat) : run0 table 1 ⟨1,[],([true,false,false,true,false,false,true]) ++ (rep [false,false,true,false,false,true] (n))⟩ = some ⟨2,([true,true]),([false,false,true,false,false,true]) ++ (rep [false,false,true,false,false,true] (n))⟩ := by rfl

theorem local1 (L R : List Bool) : run0 table 18 ⟨2,([true,true]) ++ (L),([false,false,true,false,false,true]) ++ ([false,false,true,false,false,true]) ++ (R)⟩ = some ⟨2,([true,true]) ++ ([true,false,false,true,false,false]) ++ (L),([false,false,true,false,false,true]) ++ (R)⟩ := by rfl

theorem phase1 (n : Nat) : run0 table (18*n) ⟨2,([true,true]),([false,false,true,false,false,true]) ++ (rep [false,false,true,false,false,true] (n))⟩ = some ⟨2,([true,true]) ++ (rep [true,false,false,true,false,false] (n)),([false,false,true,false,false,true])⟩ := by
  simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using sweepR table 2 [true,true] [false,false,true,false,false,true] [false,false,true,false,false,true] [true,false,false,true,false,false] 18 local1 n ([]) ([])

theorem phase2 (n : Nat) : run0 table 33 ⟨2,([true,true]) ++ (rep [true,false,false,true,false,false] (n)),([false,false,true,false,false,true])⟩ = some ⟨5,([false,true,false,false,true,false,false,true,false,false,true,false,false]) ++ (rep [true,false,false,true,false,false] (n)),[]⟩ := by rfl

theorem local3 (L R : List Bool) : run0 table 6 ⟨5,([false,true,false,false,true,false,false,true,false,false,true,false,false]) ++ ([true,false,false,true,false,false]) ++ (L),(R)⟩ = some ⟨5,([false,true,false,false,true,false,false,true,false,false,true,false,false]) ++ (L),([false,false,true,false,false,true]) ++ (R)⟩ := by rfl

theorem phase3 (n : Nat) : run0 table (6*n) ⟨5,([false,true,false,false,true,false,false,true,false,false,true,false,false]) ++ (rep [true,false,false,true,false,false] (n)),[]⟩ = some ⟨5,([false,true,false,false,true,false,false,true,false,false,true,false,false]),(rep [false,false,true,false,false,true] (n))⟩ := by
  simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using sweepL table 5 [false,true,false,false,true,false,false,true,false,false,true,false,false] [] [true,false,false,true,false,false] [false,false,true,false,false,true] 6 local3 n ([]) ([])

theorem phase4 (n : Nat) : run0 table 13 ⟨5,([false,true,false,false,true,false,false,true,false,false,true,false,false]),(rep [false,false,true,false,false,true] (n))⟩ = some ⟨1,[],([true,false,false,true,false,false,true,false,false,true,false,false,true]) ++ (rep [false,false,true,false,false,true] (n))⟩ := by rfl

theorem finalL (n : Nat) : ([] : List Bool) = [] := by
  rfl

theorem finalR (n : Nat) : ([true,false,false,true,false,false,true,false,false,true,false,false,true]) ++ (rep [false,false,true,false,false,true] (n)) = ([true,false,false,true,false,false,true,false,false,true,false,false,true]) ++ (rep [false,false,true,false,false,true] (n)) := by
  rfl

theorem growth (n : Nat) : run0 table (47+24*n) (family n) = some (family (n+1)) := by
  have H := (join0 (join0 (join0 (join0 (phase0 n) (phase1 n)) (phase2 n)) (phase3 n)) (phase4 n))
  rw [show 1+18*n+33+6*n+13=47+24*n by omega] at H
  simpa only [family,rep,List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using H

theorem never (m : Machine) (hm : compatible table m) : NeverHalts m :=
  never_of_growth table family 15 (fun n => 47+24*n) entry (by intro n; omega) growth m hm

#print axioms never

end M2011

end BB6.Agent11Raw39RCPumps
