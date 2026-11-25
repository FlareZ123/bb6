import SweepPumping
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedVariables false
namespace BB6.Agent11Raw39B1RCPumps
open BB6Coverage BB6Coverage.Agent31Pump


namespace M0

-- 1RB1RC_1RC0LE_0RD0LB_1LD0RA_0LF---_0LA1LE

def table : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 0,true => some (some ⟨true,true,2⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 1,true => some (some ⟨false,false,4⟩)
  | 2,false => some (some ⟨false,true,3⟩)
  | 2,true => some (some ⟨false,false,1⟩)
  | 3,false => some (some ⟨true,false,3⟩)
  | 3,true => some (some ⟨false,true,0⟩)
  | 4,false => some (some ⟨false,false,5⟩)
  | 5,false => some (some ⟨false,false,0⟩)
  | 5,true => some (some ⟨true,false,4⟩)
  | _,_ => none

def family (n : Nat) : Z0 := ⟨3,([false,false,true,true]) ++ (rep [false,false,true,true] (n)),[]⟩

theorem entry : run0 table 3 ⟨0,[],[]⟩ = some (family 0) := by rfl

theorem local0 (L R : List Bool) : run0 table 12 ⟨3,([false,false,true,true]) ++ ([false,false,true,true]) ++ (L),(R)⟩ = some ⟨3,([false,false,true,true]) ++ (L),([true,false,false,false]) ++ (R)⟩ := by rfl

theorem phase0 (n : Nat) : run0 table (12*n) ⟨3,([false,false,true,true]) ++ (rep [false,false,true,true] (n)),[]⟩ = some ⟨3,([false,false,true,true]),(rep [true,false,false,false] (n))⟩ := by
  simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using sweepL table 3 [false,false,true,true] [] [false,false,true,true] [true,false,false,false] 12 local0 n ([]) ([])

theorem phase1 (n : Nat) : run0 table 11 ⟨3,([false,false,true,true]),(rep [true,false,false,false] (n))⟩ = some ⟨1,([false,true]),([false,true,false,false,false]) ++ (rep [true,false,false,false] (n))⟩ := by rfl

theorem local2 (L R : List Bool) : run0 table 4 ⟨1,([false]) ++ (L),([false,true,false,false,false]) ++ ([true,false,false,false]) ++ (R)⟩ = some ⟨1,([false]) ++ ([true,false,false,true]) ++ (L),([false,true,false,false,false]) ++ (R)⟩ := by rfl

theorem phase2 (n : Nat) : run0 table (4*n) ⟨1,([false,true]),([false,true,false,false,false]) ++ (rep [true,false,false,false] (n))⟩ = some ⟨1,([false]) ++ (rep [true,false,false,true] (n)) ++ ([true]),([false,true,false,false,false])⟩ := by
  simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using sweepR table 1 [false] [false,true,false,false,false] [true,false,false,false] [true,false,false,true] 4 local2 n (([true])) ([])

theorem phase3 (n : Nat) : run0 table 6 ⟨1,([false]) ++ (rep [true,false,false,true] (n)) ++ ([true]),([false,true,false,false,false])⟩ = some ⟨3,([false,false,true,true,false,false,true]) ++ (rep [true,false,false,true] (n)) ++ ([true]),[]⟩ := by rfl

theorem finalL (n : Nat) : ([false,false,true,true,false,false,true]) ++ (rep [true,false,false,true] (n)) ++ ([true]) = ([false,false,true,true,false,false,true,true]) ++ (rep [false,false,true,true] (n)) := by
  calc
    _ = ([false,false,true,true,false,false,true,true]) ++ (rep [false,false,true,true] (n)) := by symm; simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using moveCut (([false,false,true,true,false,false,true])) ([]) [false,false,true] true n

theorem finalR (n : Nat) : ([] : List Bool) = [] := by
  rfl

theorem growth (n : Nat) : run0 table (17+16*n) (family n) = some (family (n+1)) := by
  have H := (join0 (join0 (join0 (phase0 n) (phase1 n)) (phase2 n)) (phase3 n))
  rw [finalL n] at H
  rw [show 12*n+11+4*n+6=17+16*n by omega] at H
  simpa only [family,rep,List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using H

theorem never (m : Machine) (hm : compatible table m) : NeverHalts m :=
  never_of_growth table family 3 (fun n => 17+16*n) entry (by intro n; omega) growth m hm

#print axioms never

end M0

namespace M1

-- 1RB1RC_1RC0LF_0RD0LB_1LD0RA_0LA1LF_0LE---

def table : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 0,true => some (some ⟨true,true,2⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 1,true => some (some ⟨false,false,5⟩)
  | 2,false => some (some ⟨false,true,3⟩)
  | 2,true => some (some ⟨false,false,1⟩)
  | 3,false => some (some ⟨true,false,3⟩)
  | 3,true => some (some ⟨false,true,0⟩)
  | 4,false => some (some ⟨false,false,0⟩)
  | 4,true => some (some ⟨true,false,5⟩)
  | 5,false => some (some ⟨false,false,4⟩)
  | _,_ => none

def family (n : Nat) : Z0 := ⟨3,([false,false,true,true]) ++ (rep [false,false,true,true] (n)),[]⟩

theorem entry : run0 table 3 ⟨0,[],[]⟩ = some (family 0) := by rfl

theorem local0 (L R : List Bool) : run0 table 12 ⟨3,([false,false,true,true]) ++ ([false,false,true,true]) ++ (L),(R)⟩ = some ⟨3,([false,false,true,true]) ++ (L),([true,false,false,false]) ++ (R)⟩ := by rfl

theorem phase0 (n : Nat) : run0 table (12*n) ⟨3,([false,false,true,true]) ++ (rep [false,false,true,true] (n)),[]⟩ = some ⟨3,([false,false,true,true]),(rep [true,false,false,false] (n))⟩ := by
  simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using sweepL table 3 [false,false,true,true] [] [false,false,true,true] [true,false,false,false] 12 local0 n ([]) ([])

theorem phase1 (n : Nat) : run0 table 11 ⟨3,([false,false,true,true]),(rep [true,false,false,false] (n))⟩ = some ⟨1,([false,true]),([false,true,false,false,false]) ++ (rep [true,false,false,false] (n))⟩ := by rfl

theorem local2 (L R : List Bool) : run0 table 4 ⟨1,([false]) ++ (L),([false,true,false,false,false]) ++ ([true,false,false,false]) ++ (R)⟩ = some ⟨1,([false]) ++ ([true,false,false,true]) ++ (L),([false,true,false,false,false]) ++ (R)⟩ := by rfl

theorem phase2 (n : Nat) : run0 table (4*n) ⟨1,([false,true]),([false,true,false,false,false]) ++ (rep [true,false,false,false] (n))⟩ = some ⟨1,([false]) ++ (rep [true,false,false,true] (n)) ++ ([true]),([false,true,false,false,false])⟩ := by
  simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using sweepR table 1 [false] [false,true,false,false,false] [true,false,false,false] [true,false,false,true] 4 local2 n (([true])) ([])

theorem phase3 (n : Nat) : run0 table 6 ⟨1,([false]) ++ (rep [true,false,false,true] (n)) ++ ([true]),([false,true,false,false,false])⟩ = some ⟨3,([false,false,true,true,false,false,true]) ++ (rep [true,false,false,true] (n)) ++ ([true]),[]⟩ := by rfl

theorem finalL (n : Nat) : ([false,false,true,true,false,false,true]) ++ (rep [true,false,false,true] (n)) ++ ([true]) = ([false,false,true,true,false,false,true,true]) ++ (rep [false,false,true,true] (n)) := by
  calc
    _ = ([false,false,true,true,false,false,true,true]) ++ (rep [false,false,true,true] (n)) := by symm; simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using moveCut (([false,false,true,true,false,false,true])) ([]) [false,false,true] true n

theorem finalR (n : Nat) : ([] : List Bool) = [] := by
  rfl

theorem growth (n : Nat) : run0 table (17+16*n) (family n) = some (family (n+1)) := by
  have H := (join0 (join0 (join0 (phase0 n) (phase1 n)) (phase2 n)) (phase3 n))
  rw [finalL n] at H
  rw [show 12*n+11+4*n+6=17+16*n by omega] at H
  simpa only [family,rep,List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using H

theorem never (m : Machine) (hm : compatible table m) : NeverHalts m :=
  never_of_growth table family 3 (fun n => 17+16*n) entry (by intro n; omega) growth m hm

#print axioms never

end M1

namespace M11

-- 1RB1RC_1RC1LE_0RD0LB_1LD0RA_1LF---_0LB1LE

def table : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 0,true => some (some ⟨true,true,2⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 1,true => some (some ⟨true,false,4⟩)
  | 2,false => some (some ⟨false,true,3⟩)
  | 2,true => some (some ⟨false,false,1⟩)
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

theorem phase4 (n : Nat) : run0 table 4 ⟨2,([false]) ++ (rep [true,false,false,true,false,false,true,false,false] (n)) ++ ([true]),([true,true,true,true,false])⟩ = some ⟨1,([true,false,false]) ++ (rep [true,false,false,true,false,false,true,false,false] (n)) ++ ([true]),([false,true,false])⟩ := by rfl

theorem local5 (L R : List Bool) : run0 table 9 ⟨1,([true,false,false]) ++ ([true,false,false,true,false,false,true,false,false]) ++ (L),(R)⟩ = some ⟨1,([true,false,false]) ++ (L),([false,true,true,false,true,true,false,true,true]) ++ (R)⟩ := by rfl

theorem phase5 (n : Nat) : run0 table (9*n) ⟨1,([true,false,false]) ++ (rep [true,false,false,true,false,false,true,false,false] (n)) ++ ([true]),([false,true,false])⟩ = some ⟨1,([true,false,false,true]),(rep [false,true,true,false,true,true,false,true,true] (n)) ++ ([false,true,false])⟩ := by
  simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using sweepL table 1 [true,false,false] [] [true,false,false,true,false,false,true,false,false] [false,true,true,false,true,true,false,true,true] 9 local5 n (([true])) (([false,true,false]))

theorem phase6 (n : Nat) : run0 table 7 ⟨1,([true,false,false,true]),(rep [false,true,true,false,true,true,false,true,true] (n)) ++ ([false,true,false])⟩ = some ⟨2,([false,true]),([true,true,false,true,true]) ++ (rep [false,true,true,false,true,true,false,true,true] (n)) ++ ([false,true,false])⟩ := by rfl

theorem local7 (L R : List Bool) : run0 table 9 ⟨2,([false]) ++ (L),([true,true,false,true,true]) ++ ([false,true,true,false,true,true,false,true,true]) ++ (R)⟩ = some ⟨2,([false]) ++ ([true,false,false,true,false,false,true,false,false]) ++ (L),([true,true,false,true,true]) ++ (R)⟩ := by rfl

theorem phase7 (n : Nat) : run0 table (9*n) ⟨2,([false,true]),([true,true,false,true,true]) ++ (rep [false,true,true,false,true,true,false,true,true] (n)) ++ ([false,true,false])⟩ = some ⟨2,([false]) ++ (rep [true,false,false,true,false,false,true,false,false] (n)) ++ ([true]),([true,true,false,true,true,false,true,false])⟩ := by
  simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using sweepR table 2 [false] [true,true,false,true,true] [false,true,true,false,true,true,false,true,true] [true,false,false,true,false,false,true,false,false] 9 local7 n (([true])) (([false,true,false]))

theorem phase8 (n : Nat) : run0 table 9 ⟨2,([false]) ++ (rep [true,false,false,true,false,false,true,false,false] (n)) ++ ([true]),([true,true,false,true,true,false,true,false])⟩ = some ⟨1,([false,true,false,false,true,false,false,true,false,false]) ++ (rep [true,false,false,true,false,false,true,false,false] (n)) ++ ([true]),[]⟩ := by rfl

theorem finalL (n : Nat) : ([false,true,false,false,true,false,false,true,false,false]) ++ (rep [true,false,false,true,false,false,true,false,false] (n)) ++ ([true]) = ([false,true,false,false,true,false,false,true,false,false,true]) ++ (rep [false,false,true,false,false,true,false,false,true] (n)) := by
  calc
    _ = ([false,true,false,false,true,false,false,true,false,false,true]) ++ (rep [false,false,true,false,false,true,false,false,true] (n)) := by symm; simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using moveCut (([false,true,false,false,true,false,false,true,false,false])) ([]) [false,false,true,false,false,true,false,false] true n

theorem finalR (n : Nat) : ([] : List Bool) = [] := by
  rfl

theorem growth (n : Nat) : run0 table (33+36*n) (family n) = some (family (n+1)) := by
  have H := (join0 (join0 (join0 (join0 (join0 (join0 (join0 (join0 (phase0 n) (phase1 n)) (phase2 n)) (phase3 n)) (phase4 n)) (phase5 n)) (phase6 n)) (phase7 n)) (phase8 n))
  rw [finalL n] at H
  rw [show 10+9*n+3+9*n+4+9*n+7+9*n+9=33+36*n by omega] at H
  simpa only [family,rep,List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using H

theorem never (m : Machine) (hm : compatible table m) : NeverHalts m :=
  never_of_growth table family 1 (fun n => 33+36*n) entry (by intro n; omega) growth m hm

#print axioms never

end M11

namespace M12

-- 1RB1RC_1RC1LE_0RD0LB_1LD0RA_1LF---_0LB1RC

def table : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 0,true => some (some ⟨true,true,2⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 1,true => some (some ⟨true,false,4⟩)
  | 2,false => some (some ⟨false,true,3⟩)
  | 2,true => some (some ⟨false,false,1⟩)
  | 3,false => some (some ⟨true,false,3⟩)
  | 3,true => some (some ⟨false,true,0⟩)
  | 4,false => some (some ⟨true,false,5⟩)
  | 5,false => some (some ⟨false,false,1⟩)
  | 5,true => some (some ⟨true,true,2⟩)
  | _,_ => none

def family (n : Nat) : Z0 := ⟨1,([false,true]) ++ (rep [false,false,true,false,false,true] (n)),[]⟩

theorem entry : run0 table 1 ⟨0,[],[]⟩ = some (family 0) := by rfl

theorem phase0 (n : Nat) : run0 table 11 ⟨1,([false,true]) ++ (rep [false,false,true,false,false,true] (n)),[]⟩ = some ⟨1,([true]) ++ (rep [false,false,true,false,false,true] (n)),([false,true,false])⟩ := by rfl

theorem local1 (L R : List Bool) : run0 table 6 ⟨1,([true]) ++ ([false,false,true,false,false,true]) ++ (L),(R)⟩ = some ⟨1,([true]) ++ (L),([false,true,true,false,true,true]) ++ (R)⟩ := by rfl

theorem phase1 (n : Nat) : run0 table (6*n) ⟨1,([true]) ++ (rep [false,false,true,false,false,true] (n)),([false,true,false])⟩ = some ⟨1,([true]),(rep [false,true,true,false,true,true] (n)) ++ ([false,true,false])⟩ := by
  simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using sweepL table 1 [true] [] [false,false,true,false,false,true] [false,true,true,false,true,true] 6 local1 n ([]) (([false,true,false]))

theorem phase2 (n : Nat) : run0 table 4 ⟨1,([true]),(rep [false,true,true,false,true,true] (n)) ++ ([false,true,false])⟩ = some ⟨2,([false,true]),([true,true]) ++ (rep [false,true,true,false,true,true] (n)) ++ ([false,true,false])⟩ := by rfl

theorem local3 (L R : List Bool) : run0 table 6 ⟨2,([false]) ++ (L),([true,true]) ++ ([false,true,true,false,true,true]) ++ (R)⟩ = some ⟨2,([false]) ++ ([true,false,false,true,false,false]) ++ (L),([true,true]) ++ (R)⟩ := by rfl

theorem phase3 (n : Nat) : run0 table (6*n) ⟨2,([false,true]),([true,true]) ++ (rep [false,true,true,false,true,true] (n)) ++ ([false,true,false])⟩ = some ⟨2,([false]) ++ (rep [true,false,false,true,false,false] (n)) ++ ([true]),([true,true,false,true,false])⟩ := by
  simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using sweepR table 2 [false] [true,true] [false,true,true,false,true,true] [true,false,false,true,false,false] 6 local3 n (([true])) (([false,true,false]))

theorem phase4 (n : Nat) : run0 table 6 ⟨2,([false]) ++ (rep [true,false,false,true,false,false] (n)) ++ ([true]),([true,true,false,true,false])⟩ = some ⟨1,([false,true,false,false,true,false,false]) ++ (rep [true,false,false,true,false,false] (n)) ++ ([true]),[]⟩ := by rfl

theorem finalL (n : Nat) : ([false,true,false,false,true,false,false]) ++ (rep [true,false,false,true,false,false] (n)) ++ ([true]) = ([false,true,false,false,true,false,false,true]) ++ (rep [false,false,true,false,false,true] (n)) := by
  calc
    _ = ([false,true,false,false,true,false,false,true]) ++ (rep [false,false,true,false,false,true] (n)) := by symm; simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using moveCut (([false,true,false,false,true,false,false])) ([]) [false,false,true,false,false] true n

theorem finalR (n : Nat) : ([] : List Bool) = [] := by
  rfl

theorem growth (n : Nat) : run0 table (21+12*n) (family n) = some (family (n+1)) := by
  have H := (join0 (join0 (join0 (join0 (phase0 n) (phase1 n)) (phase2 n)) (phase3 n)) (phase4 n))
  rw [finalL n] at H
  rw [show 11+6*n+4+6*n+6=21+12*n by omega] at H
  simpa only [family,rep,List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using H

theorem never (m : Machine) (hm : compatible table m) : NeverHalts m :=
  never_of_growth table family 1 (fun n => 21+12*n) entry (by intro n; omega) growth m hm

#print axioms never

end M12

namespace M19

-- 1RB1RC_1RC1LF_0RD0LB_1LD0RA_0LB1LF_1LE---

def table : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 0,true => some (some ⟨true,true,2⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 1,true => some (some ⟨true,false,5⟩)
  | 2,false => some (some ⟨false,true,3⟩)
  | 2,true => some (some ⟨false,false,1⟩)
  | 3,false => some (some ⟨true,false,3⟩)
  | 3,true => some (some ⟨false,true,0⟩)
  | 4,false => some (some ⟨false,false,1⟩)
  | 4,true => some (some ⟨true,false,5⟩)
  | 5,false => some (some ⟨true,false,4⟩)
  | _,_ => none

def family (n : Nat) : Z0 := ⟨1,([false,true]) ++ (rep [false,false,true,false,false,true,false,false,true] (n)),[]⟩

theorem entry : run0 table 1 ⟨0,[],[]⟩ = some (family 0) := by rfl

theorem phase0 (n : Nat) : run0 table 10 ⟨1,([false,true]) ++ (rep [false,false,true,false,false,true,false,false,true] (n)),[]⟩ = some ⟨5,(rep [false,false,true,false,false,true,false,false,true] (n)),([true,true,true,false])⟩ := by rfl

theorem local1 (L R : List Bool) : run0 table 9 ⟨5,([false,false,true,false,false,true,false,false,true]) ++ (L),(R)⟩ = some ⟨5,(L),([true,false,true,true,false,true,true,false,true]) ++ (R)⟩ := by rfl

theorem phase1 (n : Nat) : run0 table (9*n) ⟨5,(rep [false,false,true,false,false,true,false,false,true] (n)),([true,true,true,false])⟩ = some ⟨5,[],(rep [true,false,true,true,false,true,true,false,true] (n)) ++ ([true,true,true,false])⟩ := by
  simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using sweepL table 5 [] [] [false,false,true,false,false,true,false,false,true] [true,false,true,true,false,true,true,false,true] 9 local1 n ([]) (([true,true,true,false]))

theorem phase2 (n : Nat) : run0 table 3 ⟨5,[],(rep [true,false,true,true,false,true,true,false,true] (n)) ++ ([true,true,true,false])⟩ = some ⟨2,([false,true]),([true]) ++ (rep [true,false,true,true,false,true,true,false,true] (n)) ++ ([true,true,true,false])⟩ := by rfl

theorem local3 (L R : List Bool) : run0 table 9 ⟨2,([false]) ++ (L),([true]) ++ ([true,false,true,true,false,true,true,false,true]) ++ (R)⟩ = some ⟨2,([false]) ++ ([true,false,false,true,false,false,true,false,false]) ++ (L),([true]) ++ (R)⟩ := by rfl

theorem phase3 (n : Nat) : run0 table (9*n) ⟨2,([false,true]),([true]) ++ (rep [true,false,true,true,false,true,true,false,true] (n)) ++ ([true,true,true,false])⟩ = some ⟨2,([false]) ++ (rep [true,false,false,true,false,false,true,false,false] (n)) ++ ([true]),([true,true,true,true,false])⟩ := by
  simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using sweepR table 2 [false] [true] [true,false,true,true,false,true,true,false,true] [true,false,false,true,false,false,true,false,false] 9 local3 n (([true])) (([true,true,true,false]))

theorem phase4 (n : Nat) : run0 table 4 ⟨2,([false]) ++ (rep [true,false,false,true,false,false,true,false,false] (n)) ++ ([true]),([true,true,true,true,false])⟩ = some ⟨1,([true,false,false]) ++ (rep [true,false,false,true,false,false,true,false,false] (n)) ++ ([true]),([false,true,false])⟩ := by rfl

theorem local5 (L R : List Bool) : run0 table 9 ⟨1,([true,false,false]) ++ ([true,false,false,true,false,false,true,false,false]) ++ (L),(R)⟩ = some ⟨1,([true,false,false]) ++ (L),([false,true,true,false,true,true,false,true,true]) ++ (R)⟩ := by rfl

theorem phase5 (n : Nat) : run0 table (9*n) ⟨1,([true,false,false]) ++ (rep [true,false,false,true,false,false,true,false,false] (n)) ++ ([true]),([false,true,false])⟩ = some ⟨1,([true,false,false,true]),(rep [false,true,true,false,true,true,false,true,true] (n)) ++ ([false,true,false])⟩ := by
  simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using sweepL table 1 [true,false,false] [] [true,false,false,true,false,false,true,false,false] [false,true,true,false,true,true,false,true,true] 9 local5 n (([true])) (([false,true,false]))

theorem phase6 (n : Nat) : run0 table 7 ⟨1,([true,false,false,true]),(rep [false,true,true,false,true,true,false,true,true] (n)) ++ ([false,true,false])⟩ = some ⟨2,([false,true]),([true,true,false,true,true]) ++ (rep [false,true,true,false,true,true,false,true,true] (n)) ++ ([false,true,false])⟩ := by rfl

theorem local7 (L R : List Bool) : run0 table 9 ⟨2,([false]) ++ (L),([true,true,false,true,true]) ++ ([false,true,true,false,true,true,false,true,true]) ++ (R)⟩ = some ⟨2,([false]) ++ ([true,false,false,true,false,false,true,false,false]) ++ (L),([true,true,false,true,true]) ++ (R)⟩ := by rfl

theorem phase7 (n : Nat) : run0 table (9*n) ⟨2,([false,true]),([true,true,false,true,true]) ++ (rep [false,true,true,false,true,true,false,true,true] (n)) ++ ([false,true,false])⟩ = some ⟨2,([false]) ++ (rep [true,false,false,true,false,false,true,false,false] (n)) ++ ([true]),([true,true,false,true,true,false,true,false])⟩ := by
  simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using sweepR table 2 [false] [true,true,false,true,true] [false,true,true,false,true,true,false,true,true] [true,false,false,true,false,false,true,false,false] 9 local7 n (([true])) (([false,true,false]))

theorem phase8 (n : Nat) : run0 table 9 ⟨2,([false]) ++ (rep [true,false,false,true,false,false,true,false,false] (n)) ++ ([true]),([true,true,false,true,true,false,true,false])⟩ = some ⟨1,([false,true,false,false,true,false,false,true,false,false]) ++ (rep [true,false,false,true,false,false,true,false,false] (n)) ++ ([true]),[]⟩ := by rfl

theorem finalL (n : Nat) : ([false,true,false,false,true,false,false,true,false,false]) ++ (rep [true,false,false,true,false,false,true,false,false] (n)) ++ ([true]) = ([false,true,false,false,true,false,false,true,false,false,true]) ++ (rep [false,false,true,false,false,true,false,false,true] (n)) := by
  calc
    _ = ([false,true,false,false,true,false,false,true,false,false,true]) ++ (rep [false,false,true,false,false,true,false,false,true] (n)) := by symm; simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using moveCut (([false,true,false,false,true,false,false,true,false,false])) ([]) [false,false,true,false,false,true,false,false] true n

theorem finalR (n : Nat) : ([] : List Bool) = [] := by
  rfl

theorem growth (n : Nat) : run0 table (33+36*n) (family n) = some (family (n+1)) := by
  have H := (join0 (join0 (join0 (join0 (join0 (join0 (join0 (join0 (phase0 n) (phase1 n)) (phase2 n)) (phase3 n)) (phase4 n)) (phase5 n)) (phase6 n)) (phase7 n)) (phase8 n))
  rw [finalL n] at H
  rw [show 10+9*n+3+9*n+4+9*n+7+9*n+9=33+36*n by omega] at H
  simpa only [family,rep,List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using H

theorem never (m : Machine) (hm : compatible table m) : NeverHalts m :=
  never_of_growth table family 1 (fun n => 33+36*n) entry (by intro n; omega) growth m hm

#print axioms never

end M19

namespace M20

-- 1RB1RC_1RC1LF_0RD0LB_1LD0RA_0LB1RC_1LE---

def table : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 0,true => some (some ⟨true,true,2⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 1,true => some (some ⟨true,false,5⟩)
  | 2,false => some (some ⟨false,true,3⟩)
  | 2,true => some (some ⟨false,false,1⟩)
  | 3,false => some (some ⟨true,false,3⟩)
  | 3,true => some (some ⟨false,true,0⟩)
  | 4,false => some (some ⟨false,false,1⟩)
  | 4,true => some (some ⟨true,true,2⟩)
  | 5,false => some (some ⟨true,false,4⟩)
  | _,_ => none

def family (n : Nat) : Z0 := ⟨1,([false,true]) ++ (rep [false,false,true,false,false,true] (n)),[]⟩

theorem entry : run0 table 1 ⟨0,[],[]⟩ = some (family 0) := by rfl

theorem phase0 (n : Nat) : run0 table 11 ⟨1,([false,true]) ++ (rep [false,false,true,false,false,true] (n)),[]⟩ = some ⟨1,([true]) ++ (rep [false,false,true,false,false,true] (n)),([false,true,false])⟩ := by rfl

theorem local1 (L R : List Bool) : run0 table 6 ⟨1,([true]) ++ ([false,false,true,false,false,true]) ++ (L),(R)⟩ = some ⟨1,([true]) ++ (L),([false,true,true,false,true,true]) ++ (R)⟩ := by rfl

theorem phase1 (n : Nat) : run0 table (6*n) ⟨1,([true]) ++ (rep [false,false,true,false,false,true] (n)),([false,true,false])⟩ = some ⟨1,([true]),(rep [false,true,true,false,true,true] (n)) ++ ([false,true,false])⟩ := by
  simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using sweepL table 1 [true] [] [false,false,true,false,false,true] [false,true,true,false,true,true] 6 local1 n ([]) (([false,true,false]))

theorem phase2 (n : Nat) : run0 table 4 ⟨1,([true]),(rep [false,true,true,false,true,true] (n)) ++ ([false,true,false])⟩ = some ⟨2,([false,true]),([true,true]) ++ (rep [false,true,true,false,true,true] (n)) ++ ([false,true,false])⟩ := by rfl

theorem local3 (L R : List Bool) : run0 table 6 ⟨2,([false]) ++ (L),([true,true]) ++ ([false,true,true,false,true,true]) ++ (R)⟩ = some ⟨2,([false]) ++ ([true,false,false,true,false,false]) ++ (L),([true,true]) ++ (R)⟩ := by rfl

theorem phase3 (n : Nat) : run0 table (6*n) ⟨2,([false,true]),([true,true]) ++ (rep [false,true,true,false,true,true] (n)) ++ ([false,true,false])⟩ = some ⟨2,([false]) ++ (rep [true,false,false,true,false,false] (n)) ++ ([true]),([true,true,false,true,false])⟩ := by
  simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using sweepR table 2 [false] [true,true] [false,true,true,false,true,true] [true,false,false,true,false,false] 6 local3 n (([true])) (([false,true,false]))

theorem phase4 (n : Nat) : run0 table 6 ⟨2,([false]) ++ (rep [true,false,false,true,false,false] (n)) ++ ([true]),([true,true,false,true,false])⟩ = some ⟨1,([false,true,false,false,true,false,false]) ++ (rep [true,false,false,true,false,false] (n)) ++ ([true]),[]⟩ := by rfl

theorem finalL (n : Nat) : ([false,true,false,false,true,false,false]) ++ (rep [true,false,false,true,false,false] (n)) ++ ([true]) = ([false,true,false,false,true,false,false,true]) ++ (rep [false,false,true,false,false,true] (n)) := by
  calc
    _ = ([false,true,false,false,true,false,false,true]) ++ (rep [false,false,true,false,false,true] (n)) := by symm; simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using moveCut (([false,true,false,false,true,false,false])) ([]) [false,false,true,false,false] true n

theorem finalR (n : Nat) : ([] : List Bool) = [] := by
  rfl

theorem growth (n : Nat) : run0 table (21+12*n) (family n) = some (family (n+1)) := by
  have H := (join0 (join0 (join0 (join0 (phase0 n) (phase1 n)) (phase2 n)) (phase3 n)) (phase4 n))
  rw [finalL n] at H
  rw [show 11+6*n+4+6*n+6=21+12*n by omega] at H
  simpa only [family,rep,List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using H

theorem never (m : Machine) (hm : compatible table m) : NeverHalts m :=
  never_of_growth table family 1 (fun n => 21+12*n) entry (by intro n; omega) growth m hm

#print axioms never

end M20

namespace M30

-- 1RB1RC_1RC---_0RD0LE_1LD0RA_0LF0LE_0LA1LE

def table : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 0,true => some (some ⟨true,true,2⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 2,false => some (some ⟨false,true,3⟩)
  | 2,true => some (some ⟨false,false,4⟩)
  | 3,false => some (some ⟨true,false,3⟩)
  | 3,true => some (some ⟨false,true,0⟩)
  | 4,false => some (some ⟨false,false,5⟩)
  | 4,true => some (some ⟨false,false,4⟩)
  | 5,false => some (some ⟨false,false,0⟩)
  | 5,true => some (some ⟨true,false,4⟩)
  | _,_ => none

def family (n : Nat) : Z0 := ⟨3,([false,false,true,true]) ++ (rep [false,false,true,true] (n)),[]⟩

theorem entry : run0 table 3 ⟨0,[],[]⟩ = some (family 0) := by rfl

theorem local0 (L R : List Bool) : run0 table 12 ⟨3,([false,false,true,true]) ++ ([false,false,true,true]) ++ (L),(R)⟩ = some ⟨3,([false,false,true,true]) ++ (L),([true,false,false,false]) ++ (R)⟩ := by rfl

theorem phase0 (n : Nat) : run0 table (12*n) ⟨3,([false,false,true,true]) ++ (rep [false,false,true,true] (n)),[]⟩ = some ⟨3,([false,false,true,true]),(rep [true,false,false,false] (n))⟩ := by
  simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using sweepL table 3 [false,false,true,true] [] [false,false,true,true] [true,false,false,false] 12 local0 n ([]) ([])

theorem phase1 (n : Nat) : run0 table 11 ⟨3,([false,false,true,true]),(rep [true,false,false,false] (n))⟩ = some ⟨1,([false,true]),([false,true,false,false,false]) ++ (rep [true,false,false,false] (n))⟩ := by rfl

theorem local2 (L R : List Bool) : run0 table 4 ⟨1,([false]) ++ (L),([false,true,false,false,false]) ++ ([true,false,false,false]) ++ (R)⟩ = some ⟨1,([false]) ++ ([true,false,false,true]) ++ (L),([false,true,false,false,false]) ++ (R)⟩ := by rfl

theorem phase2 (n : Nat) : run0 table (4*n) ⟨1,([false,true]),([false,true,false,false,false]) ++ (rep [true,false,false,false] (n))⟩ = some ⟨1,([false]) ++ (rep [true,false,false,true] (n)) ++ ([true]),([false,true,false,false,false])⟩ := by
  simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using sweepR table 1 [false] [false,true,false,false,false] [true,false,false,false] [true,false,false,true] 4 local2 n (([true])) ([])

theorem phase3 (n : Nat) : run0 table 6 ⟨1,([false]) ++ (rep [true,false,false,true] (n)) ++ ([true]),([false,true,false,false,false])⟩ = some ⟨3,([false,false,true,true,false,false,true]) ++ (rep [true,false,false,true] (n)) ++ ([true]),[]⟩ := by rfl

theorem finalL (n : Nat) : ([false,false,true,true,false,false,true]) ++ (rep [true,false,false,true] (n)) ++ ([true]) = ([false,false,true,true,false,false,true,true]) ++ (rep [false,false,true,true] (n)) := by
  calc
    _ = ([false,false,true,true,false,false,true,true]) ++ (rep [false,false,true,true] (n)) := by symm; simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using moveCut (([false,false,true,true,false,false,true])) ([]) [false,false,true] true n

theorem finalR (n : Nat) : ([] : List Bool) = [] := by
  rfl

theorem growth (n : Nat) : run0 table (17+16*n) (family n) = some (family (n+1)) := by
  have H := (join0 (join0 (join0 (phase0 n) (phase1 n)) (phase2 n)) (phase3 n))
  rw [finalL n] at H
  rw [show 12*n+11+4*n+6=17+16*n by omega] at H
  simpa only [family,rep,List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using H

theorem never (m : Machine) (hm : compatible table m) : NeverHalts m :=
  never_of_growth table family 3 (fun n => 17+16*n) entry (by intro n; omega) growth m hm

#print axioms never

end M30

namespace M44

-- 1RB1RC_1RC0LB_0RD0LE_1LD0RA_1LA0LF_1LC---

def table : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 0,true => some (some ⟨true,true,2⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 1,true => some (some ⟨false,false,1⟩)
  | 2,false => some (some ⟨false,true,3⟩)
  | 2,true => some (some ⟨false,false,4⟩)
  | 3,false => some (some ⟨true,false,3⟩)
  | 3,true => some (some ⟨false,true,0⟩)
  | 4,false => some (some ⟨true,false,0⟩)
  | 4,true => some (some ⟨false,false,5⟩)
  | 5,false => some (some ⟨true,false,2⟩)
  | _,_ => none

def family (n : Nat) : Z0 := ⟨1,[],([false,false,false,true,false,false]) ++ (rep [false,true,false,false] (n))⟩

theorem entry : run0 table 15 ⟨0,[],[]⟩ = some (family 0) := by rfl

theorem phase0 (n : Nat) : run0 table 10 ⟨1,[],([false,false,false,true,false,false]) ++ (rep [false,true,false,false] (n))⟩ = some ⟨3,([true,false]),([false,false,false,true,false,false]) ++ (rep [false,true,false,false] (n))⟩ := by rfl

theorem local1 (L R : List Bool) : run0 table 4 ⟨3,([true]) ++ (L),([false,false,false,true,false,false]) ++ ([false,true,false,false]) ++ (R)⟩ = some ⟨3,([true]) ++ ([false,true,true,false]) ++ (L),([false,false,false,true,false,false]) ++ (R)⟩ := by rfl

theorem phase1 (n : Nat) : run0 table (4*n) ⟨3,([true,false]),([false,false,false,true,false,false]) ++ (rep [false,true,false,false] (n))⟩ = some ⟨3,([true]) ++ (rep [false,true,true,false] (n)) ++ ([false]),([false,false,false,true,false,false])⟩ := by
  simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using sweepR table 3 [true] [false,false,false,true,false,false] [false,true,false,false] [false,true,true,false] 4 local1 n (([false])) ([])

theorem phase2 (n : Nat) : run0 table 8 ⟨3,([true]) ++ (rep [false,true,true,false] (n)) ++ ([false]),([false,false,false,true,false,false])⟩ = some ⟨3,([false,false,true,true,false,false,true,true,false]) ++ (rep [false,true,true,false] (n)) ++ ([false]),[]⟩ := by rfl

theorem local3 (L R : List Bool) : run0 table 28 ⟨3,([false,false,true,true,false,false,true,true,false]) ++ ([false,true,true,false]) ++ (L),(R)⟩ = some ⟨3,([false,false,true,true,false,false,true,true,false]) ++ (L),([false,true,false,false]) ++ (R)⟩ := by rfl

theorem phase3 (n : Nat) : run0 table (28*n) ⟨3,([false,false,true,true,false,false,true,true,false]) ++ (rep [false,true,true,false] (n)) ++ ([false]),[]⟩ = some ⟨3,([false,false,true,true,false,false,true,true,false,false]),(rep [false,true,false,false] (n))⟩ := by
  simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using sweepL table 3 [false,false,true,true,false,false,true,true,false] [] [false,true,true,false] [false,true,false,false] 28 local3 n (([false])) ([])

theorem phase4 (n : Nat) : run0 table 40 ⟨3,([false,false,true,true,false,false,true,true,false,false]),(rep [false,true,false,false] (n))⟩ = some ⟨1,[],([false,false,false,true,false,false,false,true,false,false]) ++ (rep [false,true,false,false] (n))⟩ := by rfl

theorem finalL (n : Nat) : ([] : List Bool) = [] := by
  rfl

theorem finalR (n : Nat) : ([false,false,false,true,false,false,false,true,false,false]) ++ (rep [false,true,false,false] (n)) = ([false,false,false,true,false,false,false,true,false,false]) ++ (rep [false,true,false,false] (n)) := by
  rfl

theorem growth (n : Nat) : run0 table (58+32*n) (family n) = some (family (n+1)) := by
  have H := (join0 (join0 (join0 (join0 (phase0 n) (phase1 n)) (phase2 n)) (phase3 n)) (phase4 n))
  rw [show 10+4*n+8+28*n+40=58+32*n by omega] at H
  simpa only [family,rep,List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using H

theorem never (m : Machine) (hm : compatible table m) : NeverHalts m :=
  never_of_growth table family 15 (fun n => 58+32*n) entry (by intro n; omega) growth m hm

#print axioms never

end M44

namespace M45

-- 1RB1RC_1RC---_0RD0LE_1LD0RA_1LB0LF_1LC0LE

def table : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 0,true => some (some ⟨true,true,2⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 2,false => some (some ⟨false,true,3⟩)
  | 2,true => some (some ⟨false,false,4⟩)
  | 3,false => some (some ⟨true,false,3⟩)
  | 3,true => some (some ⟨false,true,0⟩)
  | 4,false => some (some ⟨true,false,1⟩)
  | 4,true => some (some ⟨false,false,5⟩)
  | 5,false => some (some ⟨true,false,2⟩)
  | 5,true => some (some ⟨false,false,4⟩)
  | _,_ => none

def family (n : Nat) : Z0 := ⟨5,[],([false,false,false,true,false,false]) ++ (rep [false,true,false,false] (n))⟩

theorem entry : run0 table 15 ⟨0,[],[]⟩ = some (family 0) := by rfl

theorem phase0 (n : Nat) : run0 table 2 ⟨5,[],([false,false,false,true,false,false]) ++ (rep [false,true,false,false] (n))⟩ = some ⟨3,([true,false]),([false,false,false,true,false,false]) ++ (rep [false,true,false,false] (n))⟩ := by rfl

theorem local1 (L R : List Bool) : run0 table 4 ⟨3,([true]) ++ (L),([false,false,false,true,false,false]) ++ ([false,true,false,false]) ++ (R)⟩ = some ⟨3,([true]) ++ ([false,true,true,false]) ++ (L),([false,false,false,true,false,false]) ++ (R)⟩ := by rfl

theorem phase1 (n : Nat) : run0 table (4*n) ⟨3,([true,false]),([false,false,false,true,false,false]) ++ (rep [false,true,false,false] (n))⟩ = some ⟨3,([true]) ++ (rep [false,true,true,false] (n)) ++ ([false]),([false,false,false,true,false,false])⟩ := by
  simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using sweepR table 3 [true] [false,false,false,true,false,false] [false,true,false,false] [false,true,true,false] 4 local1 n (([false])) ([])

theorem phase2 (n : Nat) : run0 table 8 ⟨3,([true]) ++ (rep [false,true,true,false] (n)) ++ ([false]),([false,false,false,true,false,false])⟩ = some ⟨3,([false,false,true,true,false,false,true,true,false]) ++ (rep [false,true,true,false] (n)) ++ ([false]),[]⟩ := by rfl

theorem local3 (L R : List Bool) : run0 table 20 ⟨3,([false,false,true,true,false,false,true,true,false]) ++ ([false,true,true,false]) ++ (L),(R)⟩ = some ⟨3,([false,false,true,true,false,false,true,true,false]) ++ (L),([false,true,false,false]) ++ (R)⟩ := by rfl

theorem phase3 (n : Nat) : run0 table (20*n) ⟨3,([false,false,true,true,false,false,true,true,false]) ++ (rep [false,true,true,false] (n)) ++ ([false]),[]⟩ = some ⟨3,([false,false,true,true,false,false,true,true,false,false]),(rep [false,true,false,false] (n))⟩ := by
  simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using sweepL table 3 [false,false,true,true,false,false,true,true,false] [] [false,true,true,false] [false,true,false,false] 20 local3 n (([false])) ([])

theorem phase4 (n : Nat) : run0 table 32 ⟨3,([false,false,true,true,false,false,true,true,false,false]),(rep [false,true,false,false] (n))⟩ = some ⟨5,[],([false,false,false,true,false,false,false,true,false,false]) ++ (rep [false,true,false,false] (n))⟩ := by rfl

theorem finalL (n : Nat) : ([] : List Bool) = [] := by
  rfl

theorem finalR (n : Nat) : ([false,false,false,true,false,false,false,true,false,false]) ++ (rep [false,true,false,false] (n)) = ([false,false,false,true,false,false,false,true,false,false]) ++ (rep [false,true,false,false] (n)) := by
  rfl

theorem growth (n : Nat) : run0 table (42+24*n) (family n) = some (family (n+1)) := by
  have H := (join0 (join0 (join0 (join0 (phase0 n) (phase1 n)) (phase2 n)) (phase3 n)) (phase4 n))
  rw [show 2+4*n+8+20*n+32=42+24*n by omega] at H
  simpa only [family,rep,List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using H

theorem never (m : Machine) (hm : compatible table m) : NeverHalts m :=
  never_of_growth table family 15 (fun n => 42+24*n) entry (by intro n; omega) growth m hm

#print axioms never

end M45

namespace M46

-- 1RB1RC_1RC---_0RD0LE_1LD0RA_1LB0LF_1LC0LF

def table : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 0,true => some (some ⟨true,true,2⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 2,false => some (some ⟨false,true,3⟩)
  | 2,true => some (some ⟨false,false,4⟩)
  | 3,false => some (some ⟨true,false,3⟩)
  | 3,true => some (some ⟨false,true,0⟩)
  | 4,false => some (some ⟨true,false,1⟩)
  | 4,true => some (some ⟨false,false,5⟩)
  | 5,false => some (some ⟨true,false,2⟩)
  | 5,true => some (some ⟨false,false,5⟩)
  | _,_ => none

def family (n : Nat) : Z0 := ⟨5,[],([false,false,false,true,false,false]) ++ (rep [false,true,false,false] (n))⟩

theorem entry : run0 table 15 ⟨0,[],[]⟩ = some (family 0) := by rfl

theorem phase0 (n : Nat) : run0 table 2 ⟨5,[],([false,false,false,true,false,false]) ++ (rep [false,true,false,false] (n))⟩ = some ⟨3,([true,false]),([false,false,false,true,false,false]) ++ (rep [false,true,false,false] (n))⟩ := by rfl

theorem local1 (L R : List Bool) : run0 table 4 ⟨3,([true]) ++ (L),([false,false,false,true,false,false]) ++ ([false,true,false,false]) ++ (R)⟩ = some ⟨3,([true]) ++ ([false,true,true,false]) ++ (L),([false,false,false,true,false,false]) ++ (R)⟩ := by rfl

theorem phase1 (n : Nat) : run0 table (4*n) ⟨3,([true,false]),([false,false,false,true,false,false]) ++ (rep [false,true,false,false] (n))⟩ = some ⟨3,([true]) ++ (rep [false,true,true,false] (n)) ++ ([false]),([false,false,false,true,false,false])⟩ := by
  simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using sweepR table 3 [true] [false,false,false,true,false,false] [false,true,false,false] [false,true,true,false] 4 local1 n (([false])) ([])

theorem phase2 (n : Nat) : run0 table 8 ⟨3,([true]) ++ (rep [false,true,true,false] (n)) ++ ([false]),([false,false,false,true,false,false])⟩ = some ⟨3,([false,false,true,true,false,false,true,true,false]) ++ (rep [false,true,true,false] (n)) ++ ([false]),[]⟩ := by rfl

theorem local3 (L R : List Bool) : run0 table 20 ⟨3,([false,false,true,true,false,false,true,true,false]) ++ ([false,true,true,false]) ++ (L),(R)⟩ = some ⟨3,([false,false,true,true,false,false,true,true,false]) ++ (L),([false,true,false,false]) ++ (R)⟩ := by rfl

theorem phase3 (n : Nat) : run0 table (20*n) ⟨3,([false,false,true,true,false,false,true,true,false]) ++ (rep [false,true,true,false] (n)) ++ ([false]),[]⟩ = some ⟨3,([false,false,true,true,false,false,true,true,false,false]),(rep [false,true,false,false] (n))⟩ := by
  simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using sweepL table 3 [false,false,true,true,false,false,true,true,false] [] [false,true,true,false] [false,true,false,false] 20 local3 n (([false])) ([])

theorem phase4 (n : Nat) : run0 table 32 ⟨3,([false,false,true,true,false,false,true,true,false,false]),(rep [false,true,false,false] (n))⟩ = some ⟨5,[],([false,false,false,true,false,false,false,true,false,false]) ++ (rep [false,true,false,false] (n))⟩ := by rfl

theorem finalL (n : Nat) : ([] : List Bool) = [] := by
  rfl

theorem finalR (n : Nat) : ([false,false,false,true,false,false,false,true,false,false]) ++ (rep [false,true,false,false] (n)) = ([false,false,false,true,false,false,false,true,false,false]) ++ (rep [false,true,false,false] (n)) := by
  rfl

theorem growth (n : Nat) : run0 table (42+24*n) (family n) = some (family (n+1)) := by
  have H := (join0 (join0 (join0 (join0 (phase0 n) (phase1 n)) (phase2 n)) (phase3 n)) (phase4 n))
  rw [show 2+4*n+8+20*n+32=42+24*n by omega] at H
  simpa only [family,rep,List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using H

theorem never (m : Machine) (hm : compatible table m) : NeverHalts m :=
  never_of_growth table family 15 (fun n => 42+24*n) entry (by intro n; omega) growth m hm

#print axioms never

end M46

end BB6.Agent11Raw39B1RCPumps
