import SweepPumping
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedVariables false
namespace BB6.Agent11Raw39B1RCPumps
open BB6Coverage BB6Coverage.Agent31Pump


namespace M1200

-- 1RB1RC_1RC1RE_0RD1LE_1LD0RA_1LC0LF_1LE---

def table : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 0,true => some (some ⟨true,true,2⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 1,true => some (some ⟨true,true,4⟩)
  | 2,false => some (some ⟨false,true,3⟩)
  | 2,true => some (some ⟨true,false,4⟩)
  | 3,false => some (some ⟨true,false,3⟩)
  | 3,true => some (some ⟨false,true,0⟩)
  | 4,false => some (some ⟨true,false,2⟩)
  | 4,true => some (some ⟨false,false,5⟩)
  | 5,false => some (some ⟨true,false,4⟩)
  | _,_ => none

def family (n : Nat) : Z0 := ⟨4,([false,true,true,false,false,true,false,false]) ++ (rep [true,false,false,true,false,false,true,false,false] (n)),[]⟩

theorem entry : run0 table 20 ⟨0,[],[]⟩ = some (family 0) := by rfl

theorem phase0 (n : Nat) : run0 table 1 ⟨4,([false,true,true,false,false,true,false,false]) ++ (rep [true,false,false,true,false,false,true,false,false] (n)),[]⟩ = some ⟨2,([true,true,false,false,true,false,false]) ++ (rep [true,false,false,true,false,false,true,false,false] (n)),([true])⟩ := by rfl

theorem local1 (L R : List Bool) : run0 table 27 ⟨2,([true,true,false,false,true,false,false]) ++ ([true,false,false,true,false,false,true,false,false]) ++ (L),(R)⟩ = some ⟨2,([true,true,false,false,true,false,false]) ++ (L),([true,false,true,true,false,true,true,false,true]) ++ (R)⟩ := by rfl

theorem phase1 (n : Nat) : run0 table (27*n) ⟨2,([true,true,false,false,true,false,false]) ++ (rep [true,false,false,true,false,false,true,false,false] (n)),([true])⟩ = some ⟨2,([true,true,false,false,true,false,false]),(rep [true,false,true,true,false,true,true,false,true] (n)) ++ ([true])⟩ := by
  simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using sweepL table 2 [true,true,false,false,true,false,false] [] [true,false,false,true,false,false,true,false,false] [true,false,true,true,false,true,true,false,true] 27 local1 n ([]) (([true]))

theorem phase2 (n : Nat) : run0 table 14 ⟨2,([true,true,false,false,true,false,false]),(rep [true,false,true,true,false,true,true,false,true] (n)) ++ ([true])⟩ = some ⟨3,([true,false]),([true,false,true,true,false,true]) ++ (rep [true,false,true,true,false,true,true,false,true] (n)) ++ ([true])⟩ := by rfl

theorem local3 (L R : List Bool) : run0 table 9 ⟨3,([true]) ++ (L),([true,false,true,true,false,true]) ++ ([true,false,true,true,false,true,true,false,true]) ++ (R)⟩ = some ⟨3,([true]) ++ ([false,true,false,false,true,false,false,true,false]) ++ (L),([true,false,true,true,false,true]) ++ (R)⟩ := by rfl

theorem phase3 (n : Nat) : run0 table (9*n) ⟨3,([true,false]),([true,false,true,true,false,true]) ++ (rep [true,false,true,true,false,true,true,false,true] (n)) ++ ([true])⟩ = some ⟨3,([true]) ++ (rep [false,true,false,false,true,false,false,true,false] (n)) ++ ([false]),([true,false,true,true,false,true,true])⟩ := by
  simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using sweepR table 3 [true] [true,false,true,true,false,true] [true,false,true,true,false,true,true,false,true] [false,true,false,false,true,false,false,true,false] 9 local3 n (([false])) (([true]))

theorem phase4 (n : Nat) : run0 table 32 ⟨3,([true]) ++ (rep [false,true,false,false,true,false,false,true,false] (n)) ++ ([false]),([true,false,true,true,false,true,true])⟩ = some ⟨4,([true,false,false,true,false,false,true,false,false,true,false]) ++ (rep [false,true,false,false,true,false,false,true,false] (n)) ++ ([false]),([true,false,true])⟩ := by rfl

theorem local5 (L R : List Bool) : run0 table 27 ⟨4,([true,false,false,true,false,false,true,false,false,true,false]) ++ ([false,true,false,false,true,false,false,true,false]) ++ (L),(R)⟩ = some ⟨4,([true,false,false,true,false,false,true,false,false,true,false]) ++ (L),([true,true,false,true,true,false,true,true,false]) ++ (R)⟩ := by rfl

theorem phase5 (n : Nat) : run0 table (27*n) ⟨4,([true,false,false,true,false,false,true,false,false,true,false]) ++ (rep [false,true,false,false,true,false,false,true,false] (n)) ++ ([false]),([true,false,true])⟩ = some ⟨4,([true,false,false,true,false,false,true,false,false,true,false,false]),(rep [true,true,false,true,true,false,true,true,false] (n)) ++ ([true,false,true])⟩ := by
  simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using sweepL table 4 [true,false,false,true,false,false,true,false,false,true,false] [] [false,true,false,false,true,false,false,true,false] [true,true,false,true,true,false,true,true,false] 27 local5 n (([false])) (([true,false,true]))

theorem phase6 (n : Nat) : run0 table 31 ⟨4,([true,false,false,true,false,false,true,false,false,true,false,false]),(rep [true,true,false,true,true,false,true,true,false] (n)) ++ ([true,false,true])⟩ = some ⟨3,([true,false]),([true,false,true,true,false,true,true,false,true,true,false]) ++ (rep [true,true,false,true,true,false,true,true,false] (n)) ++ ([true,false,true])⟩ := by rfl

theorem local7 (L R : List Bool) : run0 table 9 ⟨3,([true]) ++ (L),([true,false,true,true,false,true,true,false,true,true,false]) ++ ([true,true,false,true,true,false,true,true,false]) ++ (R)⟩ = some ⟨3,([true]) ++ ([false,true,false,false,true,false,false,true,false]) ++ (L),([true,false,true,true,false,true,true,false,true,true,false]) ++ (R)⟩ := by rfl

theorem phase7 (n : Nat) : run0 table (9*n) ⟨3,([true,false]),([true,false,true,true,false,true,true,false,true,true,false]) ++ (rep [true,true,false,true,true,false,true,true,false] (n)) ++ ([true,false,true])⟩ = some ⟨3,([true]) ++ (rep [false,true,false,false,true,false,false,true,false] (n)) ++ ([false]),([true,false,true,true,false,true,true,false,true,true,false,true,false,true])⟩ := by
  simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using sweepR table 3 [true] [true,false,true,true,false,true,true,false,true,true,false] [true,true,false,true,true,false,true,true,false] [false,true,false,false,true,false,false,true,false] 9 local7 n (([false])) (([true,false,true]))

theorem phase8 (n : Nat) : run0 table 15 ⟨3,([true]) ++ (rep [false,true,false,false,true,false,false,true,false] (n)) ++ ([false]),([true,false,true,true,false,true,true,false,true,true,false,true,false,true])⟩ = some ⟨4,([false,true,true,false,false,true,false,false,true,false,false,true,false,false,true,false]) ++ (rep [false,true,false,false,true,false,false,true,false] (n)) ++ ([false]),[]⟩ := by rfl

theorem finalL (n : Nat) : ([false,true,true,false,false,true,false,false,true,false,false,true,false,false,true,false]) ++ (rep [false,true,false,false,true,false,false,true,false] (n)) ++ ([false]) = ([false,true,true,false,false,true,false,false,true,false,false,true,false,false,true,false,false]) ++ (rep [true,false,false,true,false,false,true,false,false] (n)) := by
  calc
    _ = ([false,true,true,false,false,true,false,false,true,false,false,true,false,false,true,false,false]) ++ (rep [true,false,false,true,false,false,true,false,false] (n)) := by symm; simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using moveCut (([false,true,true,false,false,true,false,false,true,false,false,true,false,false,true,false])) ([]) [true,false,false,true,false,false,true,false] false n

theorem finalR (n : Nat) : ([] : List Bool) = [] := by
  rfl

theorem growth (n : Nat) : run0 table (93+72*n) (family n) = some (family (n+1)) := by
  have H := (join0 (join0 (join0 (join0 (join0 (join0 (join0 (join0 (phase0 n) (phase1 n)) (phase2 n)) (phase3 n)) (phase4 n)) (phase5 n)) (phase6 n)) (phase7 n)) (phase8 n))
  rw [finalL n] at H
  rw [show 1+27*n+14+9*n+32+27*n+31+9*n+15=93+72*n by omega] at H
  simpa only [family,rep,List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using H

theorem never (m : Machine) (hm : compatible table m) : NeverHalts m :=
  never_of_growth table family 20 (fun n => 93+72*n) entry (by intro n; omega) growth m hm

#print axioms never

end M1200

namespace M1325

-- 1RB1RC_1RC1RD_0RD1LE_1LD0RA_0LB1LF_0LC---

def table : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 0,true => some (some ⟨true,true,2⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 1,true => some (some ⟨true,true,3⟩)
  | 2,false => some (some ⟨false,true,3⟩)
  | 2,true => some (some ⟨true,false,4⟩)
  | 3,false => some (some ⟨true,false,3⟩)
  | 3,true => some (some ⟨false,true,0⟩)
  | 4,false => some (some ⟨false,false,1⟩)
  | 4,true => some (some ⟨true,false,5⟩)
  | 5,false => some (some ⟨false,false,2⟩)
  | _,_ => none

def family (n : Nat) : Z0 := ⟨0,([false,false,true,true,false]) ++ (rep [true,true,false] (n)) ++ ([false,true]) ++ (rep [true] (n)),[]⟩

theorem entry : run0 table 18 ⟨0,[],[]⟩ = some (family 0) := by rfl

theorem phase0 (n : Nat) : run0 table 4 ⟨0,([false,false,true,true,false]) ++ (rep [true,true,false] (n)) ++ ([false,true]) ++ (rep [true] (n)),[]⟩ = some ⟨3,([false,true,true,false,true,true,false]) ++ (rep [true,true,false] (n)) ++ ([false,true]) ++ (rep [true] (n)),([true])⟩ := by rfl

theorem local1 (L R : List Bool) : run0 table 9 ⟨3,([false,true,true,false,true,true,false]) ++ ([true,true,false]) ++ (L),([true]) ++ (R)⟩ = some ⟨3,([false,true,true,false,true,true,false]) ++ (L),([true]) ++ ([false,true,true]) ++ (R)⟩ := by rfl

theorem phase1 (n : Nat) : run0 table (9*n) ⟨3,([false,true,true,false,true,true,false]) ++ (rep [true,true,false] (n)) ++ ([false,true]) ++ (rep [true] (n)),([true])⟩ = some ⟨3,([false,true,true,false,true,true,false,false,true]) ++ (rep [true] (n)),([true]) ++ (rep [false,true,true] (n))⟩ := by
  simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using sweepL table 3 [false,true,true,false,true,true,false] [true] [true,true,false] [false,true,true] 9 local1 n (([false,true]) ++ (rep [true] (n))) ([])

theorem phase2 (n : Nat) : run0 table 19 ⟨3,([false,true,true,false,true,true,false,false,true]) ++ (rep [true] (n)),([true]) ++ (rep [false,true,true] (n))⟩ = some ⟨3,([true,false,true,true]) ++ (rep [true] (n)),([false,true,true,false,true,true]) ++ (rep [false,true,true] (n))⟩ := by rfl

theorem local3 (L R : List Bool) : run0 table 3 ⟨3,([true]) ++ (L),([false,true,true,false,true,true]) ++ ([false,true,true]) ++ (R)⟩ = some ⟨3,([true]) ++ ([true,true,false]) ++ (L),([false,true,true,false,true,true]) ++ (R)⟩ := by rfl

theorem phase3 (n : Nat) : run0 table (3*n) ⟨3,([true,false,true,true]) ++ (rep [true] (n)),([false,true,true,false,true,true]) ++ (rep [false,true,true] (n))⟩ = some ⟨3,([true]) ++ (rep [true,true,false] (n)) ++ ([false,true,true]) ++ (rep [true] (n)),([false,true,true,false,true,true])⟩ := by
  simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using sweepR table 3 [true] [false,true,true,false,true,true] [false,true,true] [true,true,false] 3 local3 n (([false,true,true]) ++ (rep [true] (n))) ([])

theorem phase4 (n : Nat) : run0 table 7 ⟨3,([true]) ++ (rep [true,true,false] (n)) ++ ([false,true,true]) ++ (rep [true] (n)),([false,true,true,false,true,true])⟩ = some ⟨0,([false,false,true,true,false,true,true,false]) ++ (rep [true,true,false] (n)) ++ ([false,true,true]) ++ (rep [true] (n)),[]⟩ := by rfl

theorem finalL (n : Nat) : ([false,false,true,true,false,true,true,false]) ++ (rep [true,true,false] (n)) ++ ([false,true,true]) ++ (rep [true] (n)) = ([false,false,true,true,false,true,true,false]) ++ (rep [true,true,false] (n)) ++ ([false,true,true]) ++ (rep [true] (n)) := by
  rfl

theorem finalR (n : Nat) : ([] : List Bool) = [] := by
  rfl

theorem growth (n : Nat) : run0 table (30+12*n) (family n) = some (family (n+1)) := by
  have H := (join0 (join0 (join0 (join0 (phase0 n) (phase1 n)) (phase2 n)) (phase3 n)) (phase4 n))
  rw [show 4+9*n+19+3*n+7=30+12*n by omega] at H
  simpa only [family,rep,List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using H

theorem never (m : Machine) (hm : compatible table m) : NeverHalts m :=
  never_of_growth table family 18 (fun n => 30+12*n) entry (by intro n; omega) growth m hm

#print axioms never

end M1325

namespace M1347

-- 1RB1RC_1RC1LF_0RD1LE_1LD0RA_0LB1LF_1LE---

def table : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 0,true => some (some ⟨true,true,2⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 1,true => some (some ⟨true,false,5⟩)
  | 2,false => some (some ⟨false,true,3⟩)
  | 2,true => some (some ⟨true,false,4⟩)
  | 3,false => some (some ⟨true,false,3⟩)
  | 3,true => some (some ⟨false,true,0⟩)
  | 4,false => some (some ⟨false,false,1⟩)
  | 4,true => some (some ⟨true,false,5⟩)
  | 5,false => some (some ⟨true,false,4⟩)
  | _,_ => none

def family (n : Nat) : Z0 := ⟨5,[],([true]) ++ (rep [false,true,true] (n)) ++ ([true,true,true])⟩

theorem entry : run0 table 11 ⟨0,[],[]⟩ = some (family 0) := by rfl

theorem phase0 (n : Nat) : run0 table 3 ⟨5,[],([true]) ++ (rep [false,true,true] (n)) ++ ([true,true,true])⟩ = some ⟨2,([false,true]),([true,true]) ++ (rep [false,true,true] (n)) ++ ([true,true,true])⟩ := by rfl

theorem local1 (L R : List Bool) : run0 table 3 ⟨2,([false]) ++ (L),([true,true]) ++ ([false,true,true]) ++ (R)⟩ = some ⟨2,([false]) ++ ([true,false,false]) ++ (L),([true,true]) ++ (R)⟩ := by rfl

theorem phase1 (n : Nat) : run0 table (3*n) ⟨2,([false,true]),([true,true]) ++ (rep [false,true,true] (n)) ++ ([true,true,true])⟩ = some ⟨2,([false]) ++ (rep [true,false,false] (n)) ++ ([true]),([true,true,true,true,true])⟩ := by
  simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using sweepR table 2 [false] [true,true] [false,true,true] [true,false,false] 3 local1 n (([true])) (([true,true,true]))

theorem phase2 (n : Nat) : run0 table 5 ⟨2,([false]) ++ (rep [true,false,false] (n)) ++ ([true]),([true,true,true,true,true])⟩ = some ⟨5,([false,false]) ++ (rep [true,false,false] (n)) ++ ([true]),([true,true,true,true])⟩ := by rfl

theorem local3 (L R : List Bool) : run0 table 3 ⟨5,([false,false]) ++ ([true,false,false]) ++ (L),(R)⟩ = some ⟨5,([false,false]) ++ (L),([true,false,true]) ++ (R)⟩ := by rfl

theorem phase3 (n : Nat) : run0 table (3*n) ⟨5,([false,false]) ++ (rep [true,false,false] (n)) ++ ([true]),([true,true,true,true])⟩ = some ⟨5,([false,false,true]),(rep [true,false,true] (n)) ++ ([true,true,true,true])⟩ := by
  simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using sweepL table 5 [false,false] [] [true,false,false] [true,false,true] 3 local3 n (([true])) (([true,true,true,true]))

theorem phase4 (n : Nat) : run0 table 3 ⟨5,([false,false,true]),(rep [true,false,true] (n)) ++ ([true,true,true,true])⟩ = some ⟨5,[],([true,false,true]) ++ (rep [true,false,true] (n)) ++ ([true,true,true,true])⟩ := by rfl

theorem finalL (n : Nat) : ([] : List Bool) = [] := by
  rfl

theorem finalR (n : Nat) : ([true,false,true]) ++ (rep [true,false,true] (n)) ++ ([true,true,true,true]) = ([true,false,true,true]) ++ (rep [false,true,true] (n)) ++ ([true,true,true]) := by
  calc
    _ = ([true,false,true,true]) ++ (rep [false,true,true] (n)) ++ ([true,true,true]) := by symm; simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using moveCut (([true,false,true])) (([true,true,true])) [false,true] true n

theorem growth (n : Nat) : run0 table (11+6*n) (family n) = some (family (n+1)) := by
  have H := (join0 (join0 (join0 (join0 (phase0 n) (phase1 n)) (phase2 n)) (phase3 n)) (phase4 n))
  rw [finalR n] at H
  rw [show 3+3*n+5+3*n+3=11+6*n by omega] at H
  simpa only [family,rep,List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using H

theorem never (m : Machine) (hm : compatible table m) : NeverHalts m :=
  never_of_growth table family 11 (fun n => 11+6*n) entry (by intro n; omega) growth m hm

#print axioms never

end M1347

namespace M1352

-- 1RB1RC_1RC---_0RD1LE_1LD0RA_1LB1LF_1RA0LE

def table : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 0,true => some (some ⟨true,true,2⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 2,false => some (some ⟨false,true,3⟩)
  | 2,true => some (some ⟨true,false,4⟩)
  | 3,false => some (some ⟨true,false,3⟩)
  | 3,true => some (some ⟨false,true,0⟩)
  | 4,false => some (some ⟨true,false,1⟩)
  | 4,true => some (some ⟨true,false,5⟩)
  | 5,false => some (some ⟨true,true,0⟩)
  | 5,true => some (some ⟨false,false,4⟩)
  | _,_ => none

def family (n : Nat) : Z0 := ⟨2,([false,true]) ++ (rep [false,false,true] (n)) ++ ([true]),[]⟩

theorem entry : run0 table 2 ⟨0,[],[]⟩ = some (family 0) := by rfl

theorem phase0 (n : Nat) : run0 table 9 ⟨2,([false,true]) ++ (rep [false,false,true] (n)) ++ ([true]),[]⟩ = some ⟨2,([true,true,true]) ++ (rep [false,false,true] (n)) ++ ([true]),[]⟩ := by rfl

theorem local1 (L R : List Bool) : run0 table 5 ⟨2,([true,true,true]) ++ ([false,false,true]) ++ (L),(R)⟩ = some ⟨2,([true,true,true]) ++ (L),([false,true,true]) ++ (R)⟩ := by rfl

theorem phase1 (n : Nat) : run0 table (5*n) ⟨2,([true,true,true]) ++ (rep [false,false,true] (n)) ++ ([true]),[]⟩ = some ⟨2,([true,true,true,true]),(rep [false,true,true] (n))⟩ := by
  simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using sweepL table 2 [true,true,true] [] [false,false,true] [false,true,true] 5 local1 n (([true])) ([])

theorem phase2 (n : Nat) : run0 table 5 ⟨2,([true,true,true,true]),(rep [false,true,true] (n))⟩ = some ⟨0,([true,true]),([false,true,true]) ++ (rep [false,true,true] (n))⟩ := by rfl

theorem local3 (L R : List Bool) : run0 table 3 ⟨0,([true]) ++ (L),([false,true,true]) ++ ([false,true,true]) ++ (R)⟩ = some ⟨0,([true]) ++ ([false,false,true]) ++ (L),([false,true,true]) ++ (R)⟩ := by rfl

theorem phase3 (n : Nat) : run0 table (3*n) ⟨0,([true,true]),([false,true,true]) ++ (rep [false,true,true] (n))⟩ = some ⟨0,([true]) ++ (rep [false,false,true] (n)) ++ ([true]),([false,true,true])⟩ := by
  simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using sweepR table 0 [true] [false,true,true] [false,true,true] [false,false,true] 3 local3 n (([true])) ([])

theorem phase4 (n : Nat) : run0 table 4 ⟨0,([true]) ++ (rep [false,false,true] (n)) ++ ([true]),([false,true,true])⟩ = some ⟨2,([false,true,false,false,true]) ++ (rep [false,false,true] (n)) ++ ([true]),[]⟩ := by rfl

theorem finalL (n : Nat) : ([false,true,false,false,true]) ++ (rep [false,false,true] (n)) ++ ([true]) = ([false,true,false,false,true]) ++ (rep [false,false,true] (n)) ++ ([true]) := by
  rfl

theorem finalR (n : Nat) : ([] : List Bool) = [] := by
  rfl

theorem growth (n : Nat) : run0 table (18+8*n) (family n) = some (family (n+1)) := by
  have H := (join0 (join0 (join0 (join0 (phase0 n) (phase1 n)) (phase2 n)) (phase3 n)) (phase4 n))
  rw [show 9+5*n+5+3*n+4=18+8*n by omega] at H
  simpa only [family,rep,List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using H

theorem never (m : Machine) (hm : compatible table m) : NeverHalts m :=
  never_of_growth table family 2 (fun n => 18+8*n) entry (by intro n; omega) growth m hm

#print axioms never

end M1352

namespace M1410

-- 1RB1RC_1RC---_0RD1LE_1LD0RA_1LB1RF_1LC0LF

def table : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 0,true => some (some ⟨true,true,2⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 2,false => some (some ⟨false,true,3⟩)
  | 2,true => some (some ⟨true,false,4⟩)
  | 3,false => some (some ⟨true,false,3⟩)
  | 3,true => some (some ⟨false,true,0⟩)
  | 4,false => some (some ⟨true,false,1⟩)
  | 4,true => some (some ⟨true,true,5⟩)
  | 5,false => some (some ⟨true,false,2⟩)
  | 5,true => some (some ⟨false,false,5⟩)
  | _,_ => none

def family (n : Nat) : Z0 := ⟨5,[],([false,false,true,true,false,false]) ++ (rep [true,true,false,false] (n))⟩

theorem entry : run0 table 19 ⟨0,[],[]⟩ = some (family 0) := by rfl

theorem phase0 (n : Nat) : run0 table 2 ⟨5,[],([false,false,true,true,false,false]) ++ (rep [true,true,false,false] (n))⟩ = some ⟨3,([true,false]),([false,false,true,true,false,false]) ++ (rep [true,true,false,false] (n))⟩ := by rfl

theorem local1 (L R : List Bool) : run0 table 14 ⟨3,([true,false]) ++ (L),([false,false,true,true,false,false]) ++ ([true,true,false,false]) ++ (R)⟩ = some ⟨3,([true,false]) ++ ([true,true,false,false]) ++ (L),([false,false,true,true,false,false]) ++ (R)⟩ := by rfl

theorem phase1 (n : Nat) : run0 table (14*n) ⟨3,([true,false]),([false,false,true,true,false,false]) ++ (rep [true,true,false,false] (n))⟩ = some ⟨3,([true,false]) ++ (rep [true,true,false,false] (n)),([false,false,true,true,false,false])⟩ := by
  simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using sweepR table 3 [true,false] [false,false,true,true,false,false] [true,true,false,false] [true,true,false,false] 14 local1 n ([]) ([])

theorem phase2 (n : Nat) : run0 table 18 ⟨3,([true,false]) ++ (rep [true,true,false,false] (n)),([false,false,true,true,false,false])⟩ = some ⟨3,([false,false,true,true,false,false,true,true,false,false]) ++ (rep [true,true,false,false] (n)),[]⟩ := by rfl

theorem local3 (L R : List Bool) : run0 table 24 ⟨3,([false,false,true,true,false,false,true,true,false,false]) ++ ([true,true,false,false]) ++ (L),(R)⟩ = some ⟨3,([false,false,true,true,false,false,true,true,false,false]) ++ (L),([true,true,false,false]) ++ (R)⟩ := by rfl

theorem phase3 (n : Nat) : run0 table (24*n) ⟨3,([false,false,true,true,false,false,true,true,false,false]) ++ (rep [true,true,false,false] (n)),[]⟩ = some ⟨3,([false,false,true,true,false,false,true,true,false,false]),(rep [true,true,false,false] (n))⟩ := by
  simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using sweepL table 3 [false,false,true,true,false,false,true,true,false,false] [] [true,true,false,false] [true,true,false,false] 24 local3 n ([]) ([])

theorem phase4 (n : Nat) : run0 table 40 ⟨3,([false,false,true,true,false,false,true,true,false,false]),(rep [true,true,false,false] (n))⟩ = some ⟨5,[],([false,false,true,true,false,false,true,true,false,false]) ++ (rep [true,true,false,false] (n))⟩ := by rfl

theorem finalL (n : Nat) : ([] : List Bool) = [] := by
  rfl

theorem finalR (n : Nat) : ([false,false,true,true,false,false,true,true,false,false]) ++ (rep [true,true,false,false] (n)) = ([false,false,true,true,false,false,true,true,false,false]) ++ (rep [true,true,false,false] (n)) := by
  rfl

theorem growth (n : Nat) : run0 table (60+38*n) (family n) = some (family (n+1)) := by
  have H := (join0 (join0 (join0 (join0 (phase0 n) (phase1 n)) (phase2 n)) (phase3 n)) (phase4 n))
  rw [show 2+14*n+18+24*n+40=60+38*n by omega] at H
  simpa only [family,rep,List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using H

theorem never (m : Machine) (hm : compatible table m) : NeverHalts m :=
  never_of_growth table family 19 (fun n => 60+38*n) entry (by intro n; omega) growth m hm

#print axioms never

end M1410

namespace M1431

-- 1RB1RC_1RC---_0RD1LF_1LD0RA_0LC0LA_0LA0LE

def table : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 0,true => some (some ⟨true,true,2⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 2,false => some (some ⟨false,true,3⟩)
  | 2,true => some (some ⟨true,false,5⟩)
  | 3,false => some (some ⟨true,false,3⟩)
  | 3,true => some (some ⟨false,true,0⟩)
  | 4,false => some (some ⟨false,false,2⟩)
  | 4,true => some (some ⟨false,false,0⟩)
  | 5,false => some (some ⟨false,false,0⟩)
  | 5,true => some (some ⟨false,false,4⟩)
  | _,_ => none

def family (n : Nat) : Z0 := ⟨0,([false,false,false,true]) ++ (rep [false,false,true,false,false,true] (n)) ++ ([true,false,true,true]),[]⟩

theorem entry : run0 table 30 ⟨0,[],[]⟩ = some (family 0) := by rfl

theorem phase0 (n : Nat) : run0 table 19 ⟨0,([false,false,false,true]) ++ (rep [false,false,true,false,false,true] (n)) ++ ([true,false,true,true]),[]⟩ = some ⟨3,([false,false,true]) ++ (rep [false,false,true,false,false,true] (n)) ++ ([true,false,true,true]),([true,false,false,true])⟩ := by rfl

theorem local1 (L R : List Bool) : run0 table 18 ⟨3,([false,false,true]) ++ ([false,false,true,false,false,true]) ++ (L),(R)⟩ = some ⟨3,([false,false,true]) ++ (L),([true,false,true,true,false,true]) ++ (R)⟩ := by rfl

theorem phase1 (n : Nat) : run0 table (18*n) ⟨3,([false,false,true]) ++ (rep [false,false,true,false,false,true] (n)) ++ ([true,false,true,true]),([true,false,false,true])⟩ = some ⟨3,([false,false,true,true,false,true,true]),(rep [true,false,true,true,false,true] (n)) ++ ([true,false,false,true])⟩ := by
  simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using sweepL table 3 [false,false,true] [] [false,false,true,false,false,true] [true,false,true,true,false,true] 18 local1 n (([true,false,true,true])) (([true,false,false,true]))

theorem phase2 (n : Nat) : run0 table 19 ⟨3,([false,false,true,true,false,true,true]),(rep [true,false,true,true,false,true] (n)) ++ ([true,false,false,true])⟩ = some ⟨2,([false,true,true,false,true,true]),([true]) ++ (rep [true,false,true,true,false,true] (n)) ++ ([true,false,false,true])⟩ := by rfl

theorem local3 (L R : List Bool) : run0 table 6 ⟨2,([false]) ++ (L),([true]) ++ ([true,false,true,true,false,true]) ++ (R)⟩ = some ⟨2,([false]) ++ ([true,false,false,true,false,false]) ++ (L),([true]) ++ (R)⟩ := by rfl

theorem phase3 (n : Nat) : run0 table (6*n) ⟨2,([false,true,true,false,true,true]),([true]) ++ (rep [true,false,true,true,false,true] (n)) ++ ([true,false,false,true])⟩ = some ⟨2,([false]) ++ (rep [true,false,false,true,false,false] (n)) ++ ([true,true,false,true,true]),([true,true,false,false,true])⟩ := by
  simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using sweepR table 2 [false] [true] [true,false,true,true,false,true] [true,false,false,true,false,false] 6 local3 n (([true,true,false,true,true])) (([true,false,false,true]))

theorem phase4 (n : Nat) : run0 table 4 ⟨2,([false]) ++ (rep [true,false,false,true,false,false] (n)) ++ ([true,true,false,true,true]),([true,true,false,false,true])⟩ = some ⟨3,([false,false,true,false,false]) ++ (rep [true,false,false,true,false,false] (n)) ++ ([true,true,false,true,true]),([true])⟩ := by rfl

theorem local5 (L R : List Bool) : run0 table 18 ⟨3,([false,false,true,false,false]) ++ ([true,false,false,true,false,false]) ++ (L),(R)⟩ = some ⟨3,([false,false,true,false,false]) ++ (L),([true,false,true,true,false,true]) ++ (R)⟩ := by rfl

theorem phase5 (n : Nat) : run0 table (18*n) ⟨3,([false,false,true,false,false]) ++ (rep [true,false,false,true,false,false] (n)) ++ ([true,true,false,true,true]),([true])⟩ = some ⟨3,([false,false,true,false,false,true,true,false,true,true]),(rep [true,false,true,true,false,true] (n)) ++ ([true])⟩ := by
  simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using sweepL table 3 [false,false,true,false,false] [] [true,false,false,true,false,false] [true,false,true,true,false,true] 18 local5 n (([true,true,false,true,true])) (([true]))

theorem phase6 (n : Nat) : run0 table 28 ⟨3,([false,false,true,false,false,true,true,false,true,true]),(rep [true,false,true,true,false,true] (n)) ++ ([true])⟩ = some ⟨2,([false,true,true,false,true,true]),([true,true,false,true]) ++ (rep [true,false,true,true,false,true] (n)) ++ ([true])⟩ := by rfl

theorem local7 (L R : List Bool) : run0 table 6 ⟨2,([false]) ++ (L),([true,true,false,true]) ++ ([true,false,true,true,false,true]) ++ (R)⟩ = some ⟨2,([false]) ++ ([true,false,false,true,false,false]) ++ (L),([true,true,false,true]) ++ (R)⟩ := by rfl

theorem phase7 (n : Nat) : run0 table (6*n) ⟨2,([false,true,true,false,true,true]),([true,true,false,true]) ++ (rep [true,false,true,true,false,true] (n)) ++ ([true])⟩ = some ⟨2,([false]) ++ (rep [true,false,false,true,false,false] (n)) ++ ([true,true,false,true,true]),([true,true,false,true,true])⟩ := by
  simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using sweepR table 2 [false] [true,true,false,true] [true,false,true,true,false,true] [true,false,false,true,false,false] 6 local7 n (([true,true,false,true,true])) (([true]))

theorem phase8 (n : Nat) : run0 table 7 ⟨2,([false]) ++ (rep [true,false,false,true,false,false] (n)) ++ ([true,true,false,true,true]),([true,true,false,true,true])⟩ = some ⟨3,([false,false,true,false,false,true,false,false]) ++ (rep [true,false,false,true,false,false] (n)) ++ ([true,true,false,true,true]),[]⟩ := by rfl

theorem local9 (L R : List Bool) : run0 table 18 ⟨3,([false,false,true,false,false,true,false,false]) ++ ([true,false,false,true,false,false]) ++ (L),(R)⟩ = some ⟨3,([false,false,true,false,false,true,false,false]) ++ (L),([true,false,true,true,false,true]) ++ (R)⟩ := by rfl

theorem phase9 (n : Nat) : run0 table (18*n) ⟨3,([false,false,true,false,false,true,false,false]) ++ (rep [true,false,false,true,false,false] (n)) ++ ([true,true,false,true,true]),[]⟩ = some ⟨3,([false,false,true,false,false,true,false,false,true,true,false,true,true]),(rep [true,false,true,true,false,true] (n))⟩ := by
  simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using sweepL table 3 [false,false,true,false,false,true,false,false] [] [true,false,false,true,false,false] [true,false,true,true,false,true] 18 local9 n (([true,true,false,true,true])) ([])

theorem phase10 (n : Nat) : run0 table 37 ⟨3,([false,false,true,false,false,true,false,false,true,true,false,true,true]),(rep [true,false,true,true,false,true] (n))⟩ = some ⟨2,([false,true,true,false,true,true]),([true,true,false,true,true,false,true]) ++ (rep [true,false,true,true,false,true] (n))⟩ := by rfl

theorem local11 (L R : List Bool) : run0 table 6 ⟨2,([false]) ++ (L),([true,true,false,true,true,false,true]) ++ ([true,false,true,true,false,true]) ++ (R)⟩ = some ⟨2,([false]) ++ ([true,false,false,true,false,false]) ++ (L),([true,true,false,true,true,false,true]) ++ (R)⟩ := by rfl

theorem phase11 (n : Nat) : run0 table (6*n) ⟨2,([false,true,true,false,true,true]),([true,true,false,true,true,false,true]) ++ (rep [true,false,true,true,false,true] (n))⟩ = some ⟨2,([false]) ++ (rep [true,false,false,true,false,false] (n)) ++ ([true,true,false,true,true]),([true,true,false,true,true,false,true])⟩ := by
  simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using sweepR table 2 [false] [true,true,false,true,true,false,true] [true,false,true,true,false,true] [true,false,false,true,false,false] 6 local11 n (([true,true,false,true,true])) ([])

theorem phase12 (n : Nat) : run0 table 8 ⟨2,([false]) ++ (rep [true,false,false,true,false,false] (n)) ++ ([true,true,false,true,true]),([true,true,false,true,true,false,true])⟩ = some ⟨0,([false,false,false,true,false,false,true,false,false]) ++ (rep [true,false,false,true,false,false] (n)) ++ ([true,true,false,true,true]),[]⟩ := by rfl

theorem finalL (n : Nat) : ([false,false,false,true,false,false,true,false,false]) ++ (rep [true,false,false,true,false,false] (n)) ++ ([true,true,false,true,true]) = ([false,false,false,true,false,false,true,false,false,true]) ++ (rep [false,false,true,false,false,true] (n)) ++ ([true,false,true,true]) := by
  calc
    _ = ([false,false,false,true,false,false,true,false,false,true]) ++ (rep [false,false,true,false,false,true] (n)) ++ ([true,false,true,true]) := by symm; simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using moveCut (([false,false,false,true,false,false,true,false,false])) (([true,false,true,true])) [false,false,true,false,false] true n

theorem finalR (n : Nat) : ([] : List Bool) = [] := by
  rfl

theorem growth (n : Nat) : run0 table (122+72*n) (family n) = some (family (n+1)) := by
  have H := (join0 (join0 (join0 (join0 (join0 (join0 (join0 (join0 (join0 (join0 (join0 (join0 (phase0 n) (phase1 n)) (phase2 n)) (phase3 n)) (phase4 n)) (phase5 n)) (phase6 n)) (phase7 n)) (phase8 n)) (phase9 n)) (phase10 n)) (phase11 n)) (phase12 n))
  rw [finalL n] at H
  rw [show 19+18*n+19+6*n+4+18*n+28+6*n+7+18*n+37+6*n+8=122+72*n by omega] at H
  simpa only [family,rep,List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using H

theorem never (m : Machine) (hm : compatible table m) : NeverHalts m :=
  never_of_growth table family 30 (fun n => 122+72*n) entry (by intro n; omega) growth m hm

#print axioms never

end M1431

namespace M1463

-- 1RB1RC_1RC0RA_0RD1LF_1LD0RA_1LF---_1LA0LE

def table : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 0,true => some (some ⟨true,true,2⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 1,true => some (some ⟨false,true,0⟩)
  | 2,false => some (some ⟨false,true,3⟩)
  | 2,true => some (some ⟨true,false,5⟩)
  | 3,false => some (some ⟨true,false,3⟩)
  | 3,true => some (some ⟨false,true,0⟩)
  | 4,false => some (some ⟨true,false,5⟩)
  | 5,false => some (some ⟨true,false,0⟩)
  | 5,true => some (some ⟨false,false,4⟩)
  | _,_ => none

def family (n : Nat) : Z0 := ⟨1,([false,true]) ++ (rep [false,true] (n)) ++ (rep [false,false,true,false,true] (n)),[]⟩

theorem entry : run0 table 1 ⟨0,[],[]⟩ = some (family 0) := by rfl

theorem phase0 (n : Nat) : run0 table 7 ⟨1,([false,true]) ++ (rep [false,true] (n)) ++ (rep [false,false,true,false,true] (n)),[]⟩ = some ⟨5,([true,false,true]) ++ (rep [false,true] (n)) ++ (rep [false,false,true,false,true] (n)),([true])⟩ := by rfl

theorem local1 (L R : List Bool) : run0 table 2 ⟨5,([true,false,true]) ++ ([false,true]) ++ (L),(R)⟩ = some ⟨5,([true,false,true]) ++ (L),([true,false]) ++ (R)⟩ := by rfl

theorem phase1 (n : Nat) : run0 table (2*n) ⟨5,([true,false,true]) ++ (rep [false,true] (n)) ++ (rep [false,false,true,false,true] (n)),([true])⟩ = some ⟨5,([true,false,true]) ++ (rep [false,false,true,false,true] (n)),(rep [true,false] (n)) ++ ([true])⟩ := by
  simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using sweepL table 5 [true,false,true] [] [false,true] [true,false] 2 local1 n ((rep [false,false,true,false,true] (n))) (([true]))

theorem local2 (L R : List Bool) : run0 table 7 ⟨5,([true,false,true]) ++ ([false,false,true,false,true]) ++ (L),(R)⟩ = some ⟨5,([true,false,true]) ++ (L),([true,true,false,true,false]) ++ (R)⟩ := by rfl

theorem phase2 (n : Nat) : run0 table (7*n) ⟨5,([true,false,true]) ++ (rep [false,false,true,false,true] (n)),(rep [true,false] (n)) ++ ([true])⟩ = some ⟨5,([true,false,true]),(rep [true,true,false,true,false] (n)) ++ (rep [true,false] (n)) ++ ([true])⟩ := by
  simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using sweepL table 5 [true,false,true] [] [false,false,true,false,true] [true,true,false,true,false] 7 local2 n ([]) ((rep [true,false] (n)) ++ ([true]))

theorem phase3 (n : Nat) : run0 table 6 ⟨5,([true,false,true]),(rep [true,true,false,true,false] (n)) ++ (rep [true,false] (n)) ++ ([true])⟩ = some ⟨1,([true,true]),([true,false,true,false]) ++ (rep [true,true,false,true,false] (n)) ++ (rep [true,false] (n)) ++ ([true])⟩ := by rfl

theorem local4 (L R : List Bool) : run0 table 5 ⟨1,([true]) ++ (L),([true,false,true,false]) ++ ([true,true,false,true,false]) ++ (R)⟩ = some ⟨1,([true]) ++ ([true,false,false,true,false]) ++ (L),([true,false,true,false]) ++ (R)⟩ := by rfl

theorem phase4 (n : Nat) : run0 table (5*n) ⟨1,([true,true]),([true,false,true,false]) ++ (rep [true,true,false,true,false] (n)) ++ (rep [true,false] (n)) ++ ([true])⟩ = some ⟨1,([true]) ++ (rep [true,false,false,true,false] (n)) ++ ([true]),([true,false,true,false]) ++ (rep [true,false] (n)) ++ ([true])⟩ := by
  simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using sweepR table 1 [true] [true,false,true,false] [true,true,false,true,false] [true,false,false,true,false] 5 local4 n (([true])) ((rep [true,false] (n)) ++ ([true]))

theorem phase5 (n : Nat) : run0 table 4 ⟨1,([true]) ++ (rep [true,false,false,true,false] (n)) ++ ([true]),([true,false,true,false]) ++ (rep [true,false] (n)) ++ ([true])⟩ = some ⟨0,([false,false,false,true,false]) ++ (rep [true,false,false,true,false] (n)) ++ ([true]),(rep [true,false] (n)) ++ ([true])⟩ := by rfl

theorem local6 (L R : List Bool) : run0 table 2 ⟨0,([false]) ++ (L),([true,false]) ++ (R)⟩ = some ⟨0,([false]) ++ ([false,true]) ++ (L),(R)⟩ := by rfl

theorem phase6 (n : Nat) : run0 table (2*n) ⟨0,([false,false,false,true,false]) ++ (rep [true,false,false,true,false] (n)) ++ ([true]),(rep [true,false] (n)) ++ ([true])⟩ = some ⟨0,([false]) ++ (rep [false,true] (n)) ++ ([false,false,true,false]) ++ (rep [true,false,false,true,false] (n)) ++ ([true]),([true])⟩ := by
  simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using sweepR table 0 [false] [] [true,false] [false,true] 2 local6 n (([false,false,true,false]) ++ (rep [true,false,false,true,false] (n)) ++ ([true])) (([true]))

theorem phase7 (n : Nat) : run0 table 3 ⟨0,([false]) ++ (rep [false,true] (n)) ++ ([false,false,true,false]) ++ (rep [true,false,false,true,false] (n)) ++ ([true]),([true])⟩ = some ⟨1,([false,true,false,true]) ++ (rep [false,true] (n)) ++ ([false,false,true,false]) ++ (rep [true,false,false,true,false] (n)) ++ ([true]),[]⟩ := by rfl

theorem finalL (n : Nat) : ([false,true,false,true]) ++ (rep [false,true] (n)) ++ ([false,false,true,false]) ++ (rep [true,false,false,true,false] (n)) ++ ([true]) = ([false,true,false,true]) ++ (rep [false,true] (n)) ++ ([false,false,true,false,true]) ++ (rep [false,false,true,false,true] (n)) := by
  calc
    _ = ([false,true,false]) ++ (rep [true,false] (n)) ++ ([true,false,false,true,false]) ++ (rep [true,false,false,true,false] (n)) ++ ([true]) := by simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using moveCut (([false,true,false])) (([false,false,true,false]) ++ (rep [true,false,false,true,false] (n)) ++ ([true])) [false] true n
    _ = ([false,true]) ++ (rep [false,true] (n)) ++ ([false,true,false,false,true,false]) ++ (rep [true,false,false,true,false] (n)) ++ ([true]) := by simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using moveCut (([false,true])) (([true,false,false,true,false]) ++ (rep [true,false,false,true,false] (n)) ++ ([true])) [true] false n
    _ = ([false]) ++ (rep [true,false] (n)) ++ ([true,false,true,false,false,true,false]) ++ (rep [true,false,false,true,false] (n)) ++ ([true]) := by simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using moveCut (([false])) (([false,true,false,false,true,false]) ++ (rep [true,false,false,true,false] (n)) ++ ([true])) [false] true n
    _ = (rep [false,true] (n)) ++ ([false,true,false,true,false,false,true,false]) ++ (rep [true,false,false,true,false] (n)) ++ ([true]) := by simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using moveCut ([]) (([true,false,true,false,false,true,false]) ++ (rep [true,false,false,true,false] (n)) ++ ([true])) [true] false n
    _ = (rep [false,true] (n)) ++ ([false,true,false,true,false,false,true,false,true]) ++ (rep [false,false,true,false,true] (n)) := by symm; simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using moveCut ((rep [false,true] (n)) ++ ([false,true,false,true,false,false,true,false])) ([]) [false,false,true,false] true n
    _ = ([false]) ++ (rep [true,false] (n)) ++ ([true,false,true,false,false,true,false,true]) ++ (rep [false,false,true,false,true] (n)) := by symm; simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using moveCut ([]) (([true,false,true,false,false,true,false,true]) ++ (rep [false,false,true,false,true] (n))) [true] false n
    _ = ([false,true]) ++ (rep [false,true] (n)) ++ ([false,true,false,false,true,false,true]) ++ (rep [false,false,true,false,true] (n)) := by symm; simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using moveCut (([false])) (([false,true,false,false,true,false,true]) ++ (rep [false,false,true,false,true] (n))) [false] true n
    _ = ([false,true,false]) ++ (rep [true,false] (n)) ++ ([true,false,false,true,false,true]) ++ (rep [false,false,true,false,true] (n)) := by symm; simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using moveCut (([false,true])) (([true,false,false,true,false,true]) ++ (rep [false,false,true,false,true] (n))) [true] false n
    _ = ([false,true,false,true]) ++ (rep [false,true] (n)) ++ ([false,false,true,false,true]) ++ (rep [false,false,true,false,true] (n)) := by symm; simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using moveCut (([false,true,false])) (([false,false,true,false,true]) ++ (rep [false,false,true,false,true] (n))) [false] true n

theorem finalR (n : Nat) : ([] : List Bool) = [] := by
  rfl

theorem growth (n : Nat) : run0 table (20+16*n) (family n) = some (family (n+1)) := by
  have H := (join0 (join0 (join0 (join0 (join0 (join0 (join0 (phase0 n) (phase1 n)) (phase2 n)) (phase3 n)) (phase4 n)) (phase5 n)) (phase6 n)) (phase7 n))
  rw [finalL n] at H
  rw [show 7+2*n+7*n+6+5*n+4+2*n+3=20+16*n by omega] at H
  simpa only [family,rep,List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using H

theorem never (m : Machine) (hm : compatible table m) : NeverHalts m :=
  never_of_growth table family 1 (fun n => 20+16*n) entry (by intro n; omega) growth m hm

#print axioms never

end M1463

namespace M1472

-- 1RB1RC_1RC0RE_0RD1LF_1LD0RA_1LF---_1LC0LE

def table : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 0,true => some (some ⟨true,true,2⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 1,true => some (some ⟨false,true,4⟩)
  | 2,false => some (some ⟨false,true,3⟩)
  | 2,true => some (some ⟨true,false,5⟩)
  | 3,false => some (some ⟨true,false,3⟩)
  | 3,true => some (some ⟨false,true,0⟩)
  | 4,false => some (some ⟨true,false,5⟩)
  | 5,false => some (some ⟨true,false,2⟩)
  | 5,true => some (some ⟨false,false,4⟩)
  | _,_ => none

def family (n : Nat) : Z0 := ⟨4,([false,false,true,false,false,true,false,false]) ++ (rep [true,false,false,true,false,false,true,false,false] (n)),[]⟩

theorem entry : run0 table 20 ⟨0,[],[]⟩ = some (family 0) := by rfl

theorem local0 (L R : List Bool) : run0 table 27 ⟨4,([false,false,true,false,false,true,false,false]) ++ ([true,false,false,true,false,false,true,false,false]) ++ (L),(R)⟩ = some ⟨4,([false,false,true,false,false,true,false,false]) ++ (L),([false,true,true,false,true,true,false,true,true]) ++ (R)⟩ := by rfl

theorem phase0 (n : Nat) : run0 table (27*n) ⟨4,([false,false,true,false,false,true,false,false]) ++ (rep [true,false,false,true,false,false,true,false,false] (n)),[]⟩ = some ⟨4,([false,false,true,false,false,true,false,false]),(rep [false,true,true,false,true,true,false,true,true] (n))⟩ := by
  simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using sweepL table 4 [false,false,true,false,false,true,false,false] [] [true,false,false,true,false,false,true,false,false] [false,true,true,false,true,true,false,true,true] 27 local0 n ([]) ([])

theorem phase1 (n : Nat) : run0 table 21 ⟨4,([false,false,true,false,false,true,false,false]),(rep [false,true,true,false,true,true,false,true,true] (n))⟩ = some ⟨3,([true,false]),([true,false,true,true,false,true,true]) ++ (rep [false,true,true,false,true,true,false,true,true] (n))⟩ := by rfl

theorem local2 (L R : List Bool) : run0 table 9 ⟨3,([true]) ++ (L),([true,false,true,true,false,true,true]) ++ ([false,true,true,false,true,true,false,true,true]) ++ (R)⟩ = some ⟨3,([true]) ++ ([false,true,false,false,true,false,false,true,false]) ++ (L),([true,false,true,true,false,true,true]) ++ (R)⟩ := by rfl

theorem phase2 (n : Nat) : run0 table (9*n) ⟨3,([true,false]),([true,false,true,true,false,true,true]) ++ (rep [false,true,true,false,true,true,false,true,true] (n))⟩ = some ⟨3,([true]) ++ (rep [false,true,false,false,true,false,false,true,false] (n)) ++ ([false]),([true,false,true,true,false,true,true])⟩ := by
  simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using sweepR table 3 [true] [true,false,true,true,false,true,true] [false,true,true,false,true,true,false,true,true] [false,true,false,false,true,false,false,true,false] 9 local2 n (([false])) ([])

theorem phase3 (n : Nat) : run0 table 32 ⟨3,([true]) ++ (rep [false,true,false,false,true,false,false,true,false] (n)) ++ ([false]),([true,false,true,true,false,true,true])⟩ = some ⟨5,([true,false,false,true,false,false,true,false,false,true,false]) ++ (rep [false,true,false,false,true,false,false,true,false] (n)) ++ ([false]),([true,false,true])⟩ := by rfl

theorem local4 (L R : List Bool) : run0 table 27 ⟨5,([true,false,false,true,false,false,true,false,false,true,false]) ++ ([false,true,false,false,true,false,false,true,false]) ++ (L),(R)⟩ = some ⟨5,([true,false,false,true,false,false,true,false,false,true,false]) ++ (L),([true,true,false,true,true,false,true,true,false]) ++ (R)⟩ := by rfl

theorem phase4 (n : Nat) : run0 table (27*n) ⟨5,([true,false,false,true,false,false,true,false,false,true,false]) ++ (rep [false,true,false,false,true,false,false,true,false] (n)) ++ ([false]),([true,false,true])⟩ = some ⟨5,([true,false,false,true,false,false,true,false,false,true,false,false]),(rep [true,true,false,true,true,false,true,true,false] (n)) ++ ([true,false,true])⟩ := by
  simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using sweepL table 5 [true,false,false,true,false,false,true,false,false,true,false] [] [false,true,false,false,true,false,false,true,false] [true,true,false,true,true,false,true,true,false] 27 local4 n (([false])) (([true,false,true]))

theorem phase5 (n : Nat) : run0 table 31 ⟨5,([true,false,false,true,false,false,true,false,false,true,false,false]),(rep [true,true,false,true,true,false,true,true,false] (n)) ++ ([true,false,true])⟩ = some ⟨3,([true,false]),([true,false,true,true,false,true,true,false,true,true,false]) ++ (rep [true,true,false,true,true,false,true,true,false] (n)) ++ ([true,false,true])⟩ := by rfl

theorem local6 (L R : List Bool) : run0 table 9 ⟨3,([true]) ++ (L),([true,false,true,true,false,true,true,false,true,true,false]) ++ ([true,true,false,true,true,false,true,true,false]) ++ (R)⟩ = some ⟨3,([true]) ++ ([false,true,false,false,true,false,false,true,false]) ++ (L),([true,false,true,true,false,true,true,false,true,true,false]) ++ (R)⟩ := by rfl

theorem phase6 (n : Nat) : run0 table (9*n) ⟨3,([true,false]),([true,false,true,true,false,true,true,false,true,true,false]) ++ (rep [true,true,false,true,true,false,true,true,false] (n)) ++ ([true,false,true])⟩ = some ⟨3,([true]) ++ (rep [false,true,false,false,true,false,false,true,false] (n)) ++ ([false]),([true,false,true,true,false,true,true,false,true,true,false,true,false,true])⟩ := by
  simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using sweepR table 3 [true] [true,false,true,true,false,true,true,false,true,true,false] [true,true,false,true,true,false,true,true,false] [false,true,false,false,true,false,false,true,false] 9 local6 n (([false])) (([true,false,true]))

theorem phase7 (n : Nat) : run0 table 15 ⟨3,([true]) ++ (rep [false,true,false,false,true,false,false,true,false] (n)) ++ ([false]),([true,false,true,true,false,true,true,false,true,true,false,true,false,true])⟩ = some ⟨4,([false,false,true,false,false,true,false,false,true,false,false,true,false,false,true,false]) ++ (rep [false,true,false,false,true,false,false,true,false] (n)) ++ ([false]),[]⟩ := by rfl

theorem finalL (n : Nat) : ([false,false,true,false,false,true,false,false,true,false,false,true,false,false,true,false]) ++ (rep [false,true,false,false,true,false,false,true,false] (n)) ++ ([false]) = ([false,false,true,false,false,true,false,false,true,false,false,true,false,false,true,false,false]) ++ (rep [true,false,false,true,false,false,true,false,false] (n)) := by
  calc
    _ = ([false,false,true,false,false,true,false,false,true,false,false,true,false,false,true,false,false]) ++ (rep [true,false,false,true,false,false,true,false,false] (n)) := by symm; simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using moveCut (([false,false,true,false,false,true,false,false,true,false,false,true,false,false,true,false])) ([]) [true,false,false,true,false,false,true,false] false n

theorem finalR (n : Nat) : ([] : List Bool) = [] := by
  rfl

theorem growth (n : Nat) : run0 table (99+72*n) (family n) = some (family (n+1)) := by
  have H := (join0 (join0 (join0 (join0 (join0 (join0 (join0 (phase0 n) (phase1 n)) (phase2 n)) (phase3 n)) (phase4 n)) (phase5 n)) (phase6 n)) (phase7 n))
  rw [finalL n] at H
  rw [show 27*n+21+9*n+32+27*n+31+9*n+15=99+72*n by omega] at H
  simpa only [family,rep,List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using H

theorem never (m : Machine) (hm : compatible table m) : NeverHalts m :=
  never_of_growth table family 20 (fun n => 99+72*n) entry (by intro n; omega) growth m hm

#print axioms never

end M1472

namespace M1477

-- 1RB1RC_1RC1RC_0RD1LF_1LD0RA_1LF---_1LC0LE

def table : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 0,true => some (some ⟨true,true,2⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 1,true => some (some ⟨true,true,2⟩)
  | 2,false => some (some ⟨false,true,3⟩)
  | 2,true => some (some ⟨true,false,5⟩)
  | 3,false => some (some ⟨true,false,3⟩)
  | 3,true => some (some ⟨false,true,0⟩)
  | 4,false => some (some ⟨true,false,5⟩)
  | 5,false => some (some ⟨true,false,2⟩)
  | 5,true => some (some ⟨false,false,4⟩)
  | _,_ => none

def family (n : Nat) : Z0 := ⟨2,[],([true,true,false,true]) ++ (rep [true,false,true] (n)) ++ ([false,true])⟩

theorem entry : run0 table 13 ⟨0,[],[]⟩ = some (family 0) := by rfl

theorem phase0 (n : Nat) : run0 table 1 ⟨2,[],([true,true,false,true]) ++ (rep [true,false,true] (n)) ++ ([false,true])⟩ = some ⟨3,([true,false]),([true,false,true]) ++ (rep [true,false,true] (n)) ++ ([false,true])⟩ := by rfl

theorem local1 (L R : List Bool) : run0 table 3 ⟨3,([true]) ++ (L),([true,false,true]) ++ ([true,false,true]) ++ (R)⟩ = some ⟨3,([true]) ++ ([false,true,false]) ++ (L),([true,false,true]) ++ (R)⟩ := by rfl

theorem phase1 (n : Nat) : run0 table (3*n) ⟨3,([true,false]),([true,false,true]) ++ (rep [true,false,true] (n)) ++ ([false,true])⟩ = some ⟨3,([true]) ++ (rep [false,true,false] (n)) ++ ([false]),([true,false,true,false,true])⟩ := by
  simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using sweepR table 3 [true] [true,false,true] [true,false,true] [false,true,false] 3 local1 n (([false])) (([false,true]))

theorem phase2 (n : Nat) : run0 table 14 ⟨3,([true]) ++ (rep [false,true,false] (n)) ++ ([false]),([true,false,true,false,true])⟩ = some ⟨5,([true,false,false,true,false]) ++ (rep [false,true,false] (n)) ++ ([false]),([true,false,true])⟩ := by rfl

theorem local3 (L R : List Bool) : run0 table 9 ⟨5,([true,false,false,true,false]) ++ ([false,true,false]) ++ (L),(R)⟩ = some ⟨5,([true,false,false,true,false]) ++ (L),([true,true,false]) ++ (R)⟩ := by rfl

theorem phase3 (n : Nat) : run0 table (9*n) ⟨5,([true,false,false,true,false]) ++ (rep [false,true,false] (n)) ++ ([false]),([true,false,true])⟩ = some ⟨5,([true,false,false,true,false,false]),(rep [true,true,false] (n)) ++ ([true,false,true])⟩ := by
  simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using sweepL table 5 [true,false,false,true,false] [] [false,true,false] [true,true,false] 9 local3 n (([false])) (([true,false,true]))

theorem phase4 (n : Nat) : run0 table 12 ⟨5,([true,false,false,true,false,false]),(rep [true,true,false] (n)) ++ ([true,false,true])⟩ = some ⟨2,[],([true,true,false,true,true,false]) ++ (rep [true,true,false] (n)) ++ ([true,false,true])⟩ := by rfl

theorem finalL (n : Nat) : ([] : List Bool) = [] := by
  rfl

theorem finalR (n : Nat) : ([true,true,false,true,true,false]) ++ (rep [true,true,false] (n)) ++ ([true,false,true]) = ([true,true,false,true,true,false,true]) ++ (rep [true,false,true] (n)) ++ ([false,true]) := by
  calc
    _ = ([true,true,false,true,true,false,true]) ++ (rep [true,false,true] (n)) ++ ([false,true]) := by symm; simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using moveCut (([true,true,false,true,true,false])) (([false,true])) [true,false] true n

theorem growth (n : Nat) : run0 table (27+12*n) (family n) = some (family (n+1)) := by
  have H := (join0 (join0 (join0 (join0 (phase0 n) (phase1 n)) (phase2 n)) (phase3 n)) (phase4 n))
  rw [finalR n] at H
  rw [show 1+3*n+14+9*n+12=27+12*n by omega] at H
  simpa only [family,rep,List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using H

theorem never (m : Machine) (hm : compatible table m) : NeverHalts m :=
  never_of_growth table family 13 (fun n => 27+12*n) entry (by intro n; omega) growth m hm

#print axioms never

end M1477

namespace M1478

-- 1RB1RC_1RC1RD_0RD1LF_1LD0RA_1LF---_1LC0LE

def table : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 0,true => some (some ⟨true,true,2⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 1,true => some (some ⟨true,true,3⟩)
  | 2,false => some (some ⟨false,true,3⟩)
  | 2,true => some (some ⟨true,false,5⟩)
  | 3,false => some (some ⟨true,false,3⟩)
  | 3,true => some (some ⟨false,true,0⟩)
  | 4,false => some (some ⟨true,false,5⟩)
  | 5,false => some (some ⟨true,false,2⟩)
  | 5,true => some (some ⟨false,false,4⟩)
  | _,_ => none

def family (n : Nat) : Z0 := ⟨0,([false,false,false,true,false,false,true,false,false,true,false,false]) ++ (rep [true,false,false,true,false,false,true,false,false] (n)),[]⟩

theorem entry : run0 table 61 ⟨0,[],[]⟩ = some (family 0) := by rfl

theorem phase0 (n : Nat) : run0 table 10 ⟨0,([false,false,false,true,false,false,true,false,false,true,false,false]) ++ (rep [true,false,false,true,false,false,true,false,false] (n)),[]⟩ = some ⟨5,([true,false,false,true,false,false,true,false,false,true,false,false]) ++ (rep [true,false,false,true,false,false,true,false,false] (n)),([true,false,true])⟩ := by rfl

theorem local1 (L R : List Bool) : run0 table 27 ⟨5,([true,false,false,true,false,false,true,false,false,true,false,false]) ++ ([true,false,false,true,false,false,true,false,false]) ++ (L),(R)⟩ = some ⟨5,([true,false,false,true,false,false,true,false,false,true,false,false]) ++ (L),([true,true,false,true,true,false,true,true,false]) ++ (R)⟩ := by rfl

theorem phase1 (n : Nat) : run0 table (27*n) ⟨5,([true,false,false,true,false,false,true,false,false,true,false,false]) ++ (rep [true,false,false,true,false,false,true,false,false] (n)),([true,false,true])⟩ = some ⟨5,([true,false,false,true,false,false,true,false,false,true,false,false]),(rep [true,true,false,true,true,false,true,true,false] (n)) ++ ([true,false,true])⟩ := by
  simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using sweepL table 5 [true,false,false,true,false,false,true,false,false,true,false,false] [] [true,false,false,true,false,false,true,false,false] [true,true,false,true,true,false,true,true,false] 27 local1 n ([]) (([true,false,true]))

theorem phase2 (n : Nat) : run0 table 31 ⟨5,([true,false,false,true,false,false,true,false,false,true,false,false]),(rep [true,true,false,true,true,false,true,true,false] (n)) ++ ([true,false,true])⟩ = some ⟨3,([true,false]),([true,false,true,true,false,true,true,false,true,true,false]) ++ (rep [true,true,false,true,true,false,true,true,false] (n)) ++ ([true,false,true])⟩ := by rfl

theorem local3 (L R : List Bool) : run0 table 9 ⟨3,([true]) ++ (L),([true,false,true,true,false,true,true,false,true,true,false]) ++ ([true,true,false,true,true,false,true,true,false]) ++ (R)⟩ = some ⟨3,([true]) ++ ([false,true,false,false,true,false,false,true,false]) ++ (L),([true,false,true,true,false,true,true,false,true,true,false]) ++ (R)⟩ := by rfl

theorem phase3 (n : Nat) : run0 table (9*n) ⟨3,([true,false]),([true,false,true,true,false,true,true,false,true,true,false]) ++ (rep [true,true,false,true,true,false,true,true,false] (n)) ++ ([true,false,true])⟩ = some ⟨3,([true]) ++ (rep [false,true,false,false,true,false,false,true,false] (n)) ++ ([false]),([true,false,true,true,false,true,true,false,true,true,false,true,false,true])⟩ := by
  simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using sweepR table 3 [true] [true,false,true,true,false,true,true,false,true,true,false] [true,true,false,true,true,false,true,true,false] [false,true,false,false,true,false,false,true,false] 9 local3 n (([false])) (([true,false,true]))

theorem phase4 (n : Nat) : run0 table 21 ⟨3,([true]) ++ (rep [false,true,false,false,true,false,false,true,false] (n)) ++ ([false]),([true,false,true,true,false,true,true,false,true,true,false,true,false,true])⟩ = some ⟨3,([true,false,true,false,false,true,false,false,true,false,false,true,false,false,true,false]) ++ (rep [false,true,false,false,true,false,false,true,false] (n)) ++ ([false]),([true,true])⟩ := by rfl

theorem local5 (L R : List Bool) : run0 table 27 ⟨3,([true,false,true,false,false,true,false,false,true,false,false,true,false,false,true,false]) ++ ([false,true,false,false,true,false,false,true,false]) ++ (L),([true,true]) ++ (R)⟩ = some ⟨3,([true,false,true,false,false,true,false,false,true,false,false,true,false,false,true,false]) ++ (L),([true,true]) ++ ([true,false,true,true,false,true,true,false,true]) ++ (R)⟩ := by rfl

theorem phase5 (n : Nat) : run0 table (27*n) ⟨3,([true,false,true,false,false,true,false,false,true,false,false,true,false,false,true,false]) ++ (rep [false,true,false,false,true,false,false,true,false] (n)) ++ ([false]),([true,true])⟩ = some ⟨3,([true,false,true,false,false,true,false,false,true,false,false,true,false,false,true,false,false]),([true,true]) ++ (rep [true,false,true,true,false,true,true,false,true] (n))⟩ := by
  simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using sweepL table 3 [true,false,true,false,false,true,false,false,true,false,false,true,false,false,true,false] [true,true] [false,true,false,false,true,false,false,true,false] [true,false,true,true,false,true,true,false,true] 27 local5 n (([false])) ([])

theorem phase6 (n : Nat) : run0 table 52 ⟨3,([true,false,true,false,false,true,false,false,true,false,false,true,false,false,true,false,false]),([true,true]) ++ (rep [true,false,true,true,false,true,true,false,true] (n))⟩ = some ⟨3,([true,false]),([true,false,true,true,false,true,true,false,true,true,false,true,true,false,true,true,false,true]) ++ (rep [true,false,true,true,false,true,true,false,true] (n))⟩ := by rfl

theorem local7 (L R : List Bool) : run0 table 9 ⟨3,([true]) ++ (L),([true,false,true,true,false,true,true,false,true,true,false,true,true,false,true,true,false,true]) ++ ([true,false,true,true,false,true,true,false,true]) ++ (R)⟩ = some ⟨3,([true]) ++ ([false,true,false,false,true,false,false,true,false]) ++ (L),([true,false,true,true,false,true,true,false,true,true,false,true,true,false,true,true,false,true]) ++ (R)⟩ := by rfl

theorem phase7 (n : Nat) : run0 table (9*n) ⟨3,([true,false]),([true,false,true,true,false,true,true,false,true,true,false,true,true,false,true,true,false,true]) ++ (rep [true,false,true,true,false,true,true,false,true] (n))⟩ = some ⟨3,([true]) ++ (rep [false,true,false,false,true,false,false,true,false] (n)) ++ ([false]),([true,false,true,true,false,true,true,false,true,true,false,true,true,false,true,true,false,true])⟩ := by
  simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using sweepR table 3 [true] [true,false,true,true,false,true,true,false,true,true,false,true,true,false,true,true,false,true] [true,false,true,true,false,true,true,false,true] [false,true,false,false,true,false,false,true,false] 9 local7 n (([false])) ([])

theorem phase8 (n : Nat) : run0 table 19 ⟨3,([true]) ++ (rep [false,true,false,false,true,false,false,true,false] (n)) ++ ([false]),([true,false,true,true,false,true,true,false,true,true,false,true,true,false,true,true,false,true])⟩ = some ⟨0,([false,false,false,true,false,false,true,false,false,true,false,false,true,false,false,true,false,false,true,false]) ++ (rep [false,true,false,false,true,false,false,true,false] (n)) ++ ([false]),[]⟩ := by rfl

theorem finalL (n : Nat) : ([false,false,false,true,false,false,true,false,false,true,false,false,true,false,false,true,false,false,true,false]) ++ (rep [false,true,false,false,true,false,false,true,false] (n)) ++ ([false]) = ([false,false,false,true,false,false,true,false,false,true,false,false,true,false,false,true,false,false,true,false,false]) ++ (rep [true,false,false,true,false,false,true,false,false] (n)) := by
  calc
    _ = ([false,false,false,true,false,false,true,false,false,true,false,false,true,false,false,true,false,false,true,false,false]) ++ (rep [true,false,false,true,false,false,true,false,false] (n)) := by symm; simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using moveCut (([false,false,false,true,false,false,true,false,false,true,false,false,true,false,false,true,false,false,true,false])) ([]) [true,false,false,true,false,false,true,false] false n

theorem finalR (n : Nat) : ([] : List Bool) = [] := by
  rfl

theorem growth (n : Nat) : run0 table (133+72*n) (family n) = some (family (n+1)) := by
  have H := (join0 (join0 (join0 (join0 (join0 (join0 (join0 (join0 (phase0 n) (phase1 n)) (phase2 n)) (phase3 n)) (phase4 n)) (phase5 n)) (phase6 n)) (phase7 n)) (phase8 n))
  rw [finalL n] at H
  rw [show 10+27*n+31+9*n+21+27*n+52+9*n+19=133+72*n by omega] at H
  simpa only [family,rep,List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using H

theorem never (m : Machine) (hm : compatible table m) : NeverHalts m :=
  never_of_growth table family 61 (fun n => 133+72*n) entry (by intro n; omega) growth m hm

#print axioms never

end M1478

end BB6.Agent11Raw39B1RCPumps
