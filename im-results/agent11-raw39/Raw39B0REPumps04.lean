import SweepPumping
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedVariables false
namespace BB6.Agent11Raw39B0REPumps
open BB6Coverage BB6Coverage.Agent31Pump


namespace M1567

-- 1RB0RE_1RC0LE_0RD1RC_1LD0RA_1LF1LE_0LB---

def table : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 0,true => some (some ⟨false,true,4⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 1,true => some (some ⟨false,false,4⟩)
  | 2,false => some (some ⟨false,true,3⟩)
  | 2,true => some (some ⟨true,true,2⟩)
  | 3,false => some (some ⟨true,false,3⟩)
  | 3,true => some (some ⟨false,true,0⟩)
  | 4,false => some (some ⟨true,false,5⟩)
  | 4,true => some (some ⟨true,false,4⟩)
  | 5,false => some (some ⟨false,false,1⟩)
  | _,_ => none

def family (n : Nat) : Z0 := ⟨4,[],([false,false,true,true,true]) ++ (rep [true] (n)) ++ ([false,false,true,true]) ++ (rep [true,true] (n))⟩

theorem entry : run0 table 34 ⟨0,[],[]⟩ = some (family 0) := by rfl

theorem phase0 (n : Nat) : run0 table 7 ⟨4,[],([false,false,true,true,true]) ++ (rep [true] (n)) ++ ([false,false,true,true]) ++ (rep [true,true] (n))⟩ = some ⟨2,([true,true,true,false,false,true]),([true,true]) ++ (rep [true] (n)) ++ ([false,false,true,true]) ++ (rep [true,true] (n))⟩ := by rfl

theorem local1 (L R : List Bool) : run0 table 1 ⟨2,([true]) ++ (L),([true,true]) ++ ([true]) ++ (R)⟩ = some ⟨2,([true]) ++ ([true]) ++ (L),([true,true]) ++ (R)⟩ := by rfl

theorem phase1 (n : Nat) : run0 table (1*n) ⟨2,([true,true,true,false,false,true]),([true,true]) ++ (rep [true] (n)) ++ ([false,false,true,true]) ++ (rep [true,true] (n))⟩ = some ⟨2,([true]) ++ (rep [true] (n)) ++ ([true,true,false,false,true]),([true,true,false,false,true,true]) ++ (rep [true,true] (n))⟩ := by
  simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using sweepR table 2 [true] [true,true] [true] [true] 1 local1 n (([true,true,false,false,true])) (([false,false,true,true]) ++ (rep [true,true] (n)))

theorem phase2 (n : Nat) : run0 table 12 ⟨2,([true]) ++ (rep [true] (n)) ++ ([true,true,false,false,true]),([true,true,false,false,true,true]) ++ (rep [true,true] (n))⟩ = some ⟨4,([true]) ++ (rep [true] (n)) ++ ([true,true,false,false,true]),([false,false,true,true,true,true]) ++ (rep [true,true] (n))⟩ := by rfl

theorem local3 (L R : List Bool) : run0 table 1 ⟨4,([true]) ++ ([true]) ++ (L),(R)⟩ = some ⟨4,([true]) ++ (L),([true]) ++ (R)⟩ := by rfl

theorem phase3 (n : Nat) : run0 table (1*n) ⟨4,([true]) ++ (rep [true] (n)) ++ ([true,true,false,false,true]),([false,false,true,true,true,true]) ++ (rep [true,true] (n))⟩ = some ⟨4,([true,true,true,false,false,true]),(rep [true] (n)) ++ ([false,false,true,true,true,true]) ++ (rep [true,true] (n))⟩ := by
  simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using sweepL table 4 [true] [] [true] [true] 1 local3 n (([true,true,false,false,true])) (([false,false,true,true,true,true]) ++ (rep [true,true] (n)))

theorem phase4 (n : Nat) : run0 table 6 ⟨4,([true,true,true,false,false,true]),(rep [true] (n)) ++ ([false,false,true,true,true,true]) ++ (rep [true,true] (n))⟩ = some ⟨4,[],([false,false,true,true,true,true]) ++ (rep [true] (n)) ++ ([false,false,true,true,true,true]) ++ (rep [true,true] (n))⟩ := by rfl

theorem finalL (n : Nat) : ([] : List Bool) = [] := by
  rfl

theorem finalR (n : Nat) : ([false,false,true,true,true,true]) ++ (rep [true] (n)) ++ ([false,false,true,true,true,true]) ++ (rep [true,true] (n)) = ([false,false,true,true,true,true]) ++ (rep [true] (n)) ++ ([false,false,true,true,true,true]) ++ (rep [true,true] (n)) := by
  rfl

theorem growth (n : Nat) : run0 table (25+2*n) (family n) = some (family (n+1)) := by
  have H := (join0 (join0 (join0 (join0 (phase0 n) (phase1 n)) (phase2 n)) (phase3 n)) (phase4 n))
  rw [show 7+1*n+12+1*n+6=25+2*n by omega] at H
  simpa only [family,rep,List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using H

theorem never (m : Machine) (hm : compatible table m) : NeverHalts m :=
  never_of_growth table family 34 (fun n => 25+2*n) entry (by intro n; omega) growth m hm

#print axioms never

end M1567

namespace M1653

-- 1RB0RE_1RC0LE_0RD---_1LD0RA_1LF1LE_1RA0LB

def table : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 0,true => some (some ⟨false,true,4⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 1,true => some (some ⟨false,false,4⟩)
  | 2,false => some (some ⟨false,true,3⟩)
  | 3,false => some (some ⟨true,false,3⟩)
  | 3,true => some (some ⟨false,true,0⟩)
  | 4,false => some (some ⟨true,false,5⟩)
  | 4,true => some (some ⟨true,false,4⟩)
  | 5,false => some (some ⟨true,true,0⟩)
  | 5,true => some (some ⟨false,false,1⟩)
  | _,_ => none

def family (n : Nat) : Z0 := ⟨4,[],([true]) ++ (rep [true] (n)) ++ ([false,false,true,true,true]) ++ (rep [true,true] (n))⟩

theorem entry : run0 table 29 ⟨0,[],[]⟩ = some (family 0) := by rfl

theorem phase0 (n : Nat) : run0 table 7 ⟨4,[],([true]) ++ (rep [true] (n)) ++ ([false,false,true,true,true]) ++ (rep [true,true] (n))⟩ = some ⟨2,([false,true]),([true,true]) ++ (rep [true] (n)) ++ ([false,false,true,true,true]) ++ (rep [true,true] (n))⟩ := by rfl

theorem local1 (L R : List Bool) : run0 table 11 ⟨2,([false]) ++ (L),([true,true]) ++ ([true]) ++ (R)⟩ = some ⟨2,([false]) ++ ([true]) ++ (L),([true,true]) ++ (R)⟩ := by rfl

theorem phase1 (n : Nat) : run0 table (11*n) ⟨2,([false,true]),([true,true]) ++ (rep [true] (n)) ++ ([false,false,true,true,true]) ++ (rep [true,true] (n))⟩ = some ⟨2,([false]) ++ (rep [true] (n)) ++ ([true]),([true,true,false,false,true,true,true]) ++ (rep [true,true] (n))⟩ := by
  simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using sweepR table 2 [false] [true,true] [true] [true] 11 local1 n (([true])) (([false,false,true,true,true]) ++ (rep [true,true] (n)))

theorem phase2 (n : Nat) : run0 table 26 ⟨2,([false]) ++ (rep [true] (n)) ++ ([true]),([true,true,false,false,true,true,true]) ++ (rep [true,true] (n))⟩ = some ⟨4,([true]) ++ (rep [true] (n)) ++ ([true]),([false,false,true,true,true,true,true]) ++ (rep [true,true] (n))⟩ := by rfl

theorem local3 (L R : List Bool) : run0 table 1 ⟨4,([true]) ++ ([true]) ++ (L),(R)⟩ = some ⟨4,([true]) ++ (L),([true]) ++ (R)⟩ := by rfl

theorem phase3 (n : Nat) : run0 table (1*n) ⟨4,([true]) ++ (rep [true] (n)) ++ ([true]),([false,false,true,true,true,true,true]) ++ (rep [true,true] (n))⟩ = some ⟨4,([true,true]),(rep [true] (n)) ++ ([false,false,true,true,true,true,true]) ++ (rep [true,true] (n))⟩ := by
  simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using sweepL table 4 [true] [] [true] [true] 1 local3 n (([true])) (([false,false,true,true,true,true,true]) ++ (rep [true,true] (n)))

theorem phase4 (n : Nat) : run0 table 2 ⟨4,([true,true]),(rep [true] (n)) ++ ([false,false,true,true,true,true,true]) ++ (rep [true,true] (n))⟩ = some ⟨4,[],([true,true]) ++ (rep [true] (n)) ++ ([false,false,true,true,true,true,true]) ++ (rep [true,true] (n))⟩ := by rfl

theorem finalL (n : Nat) : ([] : List Bool) = [] := by
  rfl

theorem finalR (n : Nat) : ([true,true]) ++ (rep [true] (n)) ++ ([false,false,true,true,true,true,true]) ++ (rep [true,true] (n)) = ([true,true]) ++ (rep [true] (n)) ++ ([false,false,true,true,true,true,true]) ++ (rep [true,true] (n)) := by
  rfl

theorem growth (n : Nat) : run0 table (35+12*n) (family n) = some (family (n+1)) := by
  have H := (join0 (join0 (join0 (join0 (phase0 n) (phase1 n)) (phase2 n)) (phase3 n)) (phase4 n))
  rw [show 7+11*n+26+1*n+2=35+12*n by omega] at H
  simpa only [family,rep,List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using H

theorem never (m : Machine) (hm : compatible table m) : NeverHalts m :=
  never_of_growth table family 29 (fun n => 35+12*n) entry (by intro n; omega) growth m hm

#print axioms never

end M1653

namespace M1664

-- 1RB0RE_1RC---_0RD0RF_1LD0RA_1LF1LE_1RC0LE

def table : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 0,true => some (some ⟨false,true,4⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 2,false => some (some ⟨false,true,3⟩)
  | 2,true => some (some ⟨false,true,5⟩)
  | 3,false => some (some ⟨true,false,3⟩)
  | 3,true => some (some ⟨false,true,0⟩)
  | 4,false => some (some ⟨true,false,5⟩)
  | 4,true => some (some ⟨true,false,4⟩)
  | 5,false => some (some ⟨true,true,2⟩)
  | 5,true => some (some ⟨false,false,4⟩)
  | _,_ => none

def family (n : Nat) : Z0 := ⟨2,([false,true]) ++ (rep [false,true] (n)) ++ ([true,false,false,true,false,true,false,true]) ++ (rep [false,true,false,true] (n)),[]⟩

theorem entry : run0 table 31 ⟨0,[],[]⟩ = some (family 0) := by rfl

theorem phase0 (n : Nat) : run0 table 9 ⟨2,([false,true]) ++ (rep [false,true] (n)) ++ ([true,false,false,true,false,true,false,true]) ++ (rep [false,true,false,true] (n)),[]⟩ = some ⟨5,([true,false,true]) ++ (rep [false,true] (n)) ++ ([true,false,false,true,false,true,false,true]) ++ (rep [false,true,false,true] (n)),[]⟩ := by rfl

theorem local1 (L R : List Bool) : run0 table 2 ⟨5,([true,false,true]) ++ ([false,true]) ++ (L),(R)⟩ = some ⟨5,([true,false,true]) ++ (L),([true,false]) ++ (R)⟩ := by rfl

theorem phase1 (n : Nat) : run0 table (2*n) ⟨5,([true,false,true]) ++ (rep [false,true] (n)) ++ ([true,false,false,true,false,true,false,true]) ++ (rep [false,true,false,true] (n)),[]⟩ = some ⟨5,([true,false,true,true,false,false,true,false,true,false,true]) ++ (rep [false,true,false,true] (n)),(rep [true,false] (n))⟩ := by
  simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using sweepL table 5 [true,false,true] [] [false,true] [true,false] 2 local1 n (([true,false,false,true,false,true,false,true]) ++ (rep [false,true,false,true] (n))) ([])

theorem phase2 (n : Nat) : run0 table 11 ⟨5,([true,false,true,true,false,false,true,false,true,false,true]) ++ (rep [false,true,false,true] (n)),(rep [true,false] (n))⟩ = some ⟨4,([false,true,false,true]) ++ (rep [false,true,false,true] (n)),([true,false,true,false,false,true,false]) ++ (rep [true,false] (n))⟩ := by rfl

theorem local3 (L R : List Bool) : run0 table 4 ⟨4,([false,true,false,true]) ++ ([false,true,false,true]) ++ (L),(R)⟩ = some ⟨4,([false,true,false,true]) ++ (L),([false,true,false,true]) ++ (R)⟩ := by rfl

theorem phase3 (n : Nat) : run0 table (4*n) ⟨4,([false,true,false,true]) ++ (rep [false,true,false,true] (n)),([true,false,true,false,false,true,false]) ++ (rep [true,false] (n))⟩ = some ⟨4,([false,true,false,true]),(rep [false,true,false,true] (n)) ++ ([true,false,true,false,false,true,false]) ++ (rep [true,false] (n))⟩ := by
  simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using sweepL table 4 [false,true,false,true] [] [false,true,false,true] [false,true,false,true] 4 local3 n ([]) (([true,false,true,false,false,true,false]) ++ (rep [true,false] (n)))

theorem phase4 (n : Nat) : run0 table 6 ⟨4,([false,true,false,true]),(rep [false,true,false,true] (n)) ++ ([true,false,true,false,false,true,false]) ++ (rep [true,false] (n))⟩ = some ⟨2,([true,true]),([false,true,false,true]) ++ (rep [false,true,false,true] (n)) ++ ([true,false,true,false,false,true,false]) ++ (rep [true,false] (n))⟩ := by rfl

theorem local5 (L R : List Bool) : run0 table 4 ⟨2,([true]) ++ (L),([false,true,false,true]) ++ ([false,true,false,true]) ++ (R)⟩ = some ⟨2,([true]) ++ ([true,false,true,false]) ++ (L),([false,true,false,true]) ++ (R)⟩ := by rfl

theorem phase5 (n : Nat) : run0 table (4*n) ⟨2,([true,true]),([false,true,false,true]) ++ (rep [false,true,false,true] (n)) ++ ([true,false,true,false,false,true,false]) ++ (rep [true,false] (n))⟩ = some ⟨2,([true]) ++ (rep [true,false,true,false] (n)) ++ ([true]),([false,true,false,true,true,false,true,false,false,true,false]) ++ (rep [true,false] (n))⟩ := by
  simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using sweepR table 2 [true] [false,true,false,true] [false,true,false,true] [true,false,true,false] 4 local5 n (([true])) (([true,false,true,false,false,true,false]) ++ (rep [true,false] (n)))

theorem phase6 (n : Nat) : run0 table 5 ⟨2,([true]) ++ (rep [true,false,true,false] (n)) ++ ([true]),([false,true,false,true,true,false,true,false,false,true,false]) ++ (rep [true,false] (n))⟩ = some ⟨5,([true,false,true,false,true,false]) ++ (rep [true,false,true,false] (n)) ++ ([true]),([false,true,false,false,true,false]) ++ (rep [true,false] (n))⟩ := by rfl

theorem local7 (L R : List Bool) : run0 table 4 ⟨5,([true,false,true,false,true,false]) ++ ([true,false,true,false]) ++ (L),(R)⟩ = some ⟨5,([true,false,true,false,true,false]) ++ (L),([true,false,true,false]) ++ (R)⟩ := by rfl

theorem phase7 (n : Nat) : run0 table (4*n) ⟨5,([true,false,true,false,true,false]) ++ (rep [true,false,true,false] (n)) ++ ([true]),([false,true,false,false,true,false]) ++ (rep [true,false] (n))⟩ = some ⟨5,([true,false,true,false,true,false,true]),(rep [true,false,true,false] (n)) ++ ([false,true,false,false,true,false]) ++ (rep [true,false] (n))⟩ := by
  simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using sweepL table 5 [true,false,true,false,true,false] [] [true,false,true,false] [true,false,true,false] 4 local7 n (([true])) (([false,true,false,false,true,false]) ++ (rep [true,false] (n)))

theorem phase8 (n : Nat) : run0 table 9 ⟨5,([true,false,true,false,true,false,true]),(rep [true,false,true,false] (n)) ++ ([false,true,false,false,true,false]) ++ (rep [true,false] (n))⟩ = some ⟨2,([true,true]),([false,true,false,true,false,true,false]) ++ (rep [true,false,true,false] (n)) ++ ([false,true,false,false,true,false]) ++ (rep [true,false] (n))⟩ := by rfl

theorem local9 (L R : List Bool) : run0 table 4 ⟨2,([true]) ++ (L),([false,true,false,true,false,true,false]) ++ ([true,false,true,false]) ++ (R)⟩ = some ⟨2,([true]) ++ ([true,false,true,false]) ++ (L),([false,true,false,true,false,true,false]) ++ (R)⟩ := by rfl

theorem phase9 (n : Nat) : run0 table (4*n) ⟨2,([true,true]),([false,true,false,true,false,true,false]) ++ (rep [true,false,true,false] (n)) ++ ([false,true,false,false,true,false]) ++ (rep [true,false] (n))⟩ = some ⟨2,([true]) ++ (rep [true,false,true,false] (n)) ++ ([true]),([false,true,false,true,false,true,false,false,true,false,false,true,false]) ++ (rep [true,false] (n))⟩ := by
  simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using sweepR table 2 [true] [false,true,false,true,false,true,false] [true,false,true,false] [true,false,true,false] 4 local9 n (([true])) (([false,true,false,false,true,false]) ++ (rep [true,false] (n)))

theorem phase10 (n : Nat) : run0 table 12 ⟨2,([true]) ++ (rep [true,false,true,false] (n)) ++ ([true]),([false,true,false,true,false,true,false,false,true,false,false,true,false]) ++ (rep [true,false] (n))⟩ = some ⟨2,([true,true,true,false,false,true,false,true,false,true,false,true,false]) ++ (rep [true,false,true,false] (n)) ++ ([true]),([false]) ++ (rep [true,false] (n))⟩ := by rfl

theorem local11 (L R : List Bool) : run0 table 2 ⟨2,([true]) ++ (L),([false]) ++ ([true,false]) ++ (R)⟩ = some ⟨2,([true]) ++ ([true,false]) ++ (L),([false]) ++ (R)⟩ := by rfl

theorem phase11 (n : Nat) : run0 table (2*n) ⟨2,([true,true,true,false,false,true,false,true,false,true,false,true,false]) ++ (rep [true,false,true,false] (n)) ++ ([true]),([false]) ++ (rep [true,false] (n))⟩ = some ⟨2,([true]) ++ (rep [true,false] (n)) ++ ([true,true,false,false,true,false,true,false,true,false,true,false]) ++ (rep [true,false,true,false] (n)) ++ ([true]),([false])⟩ := by
  simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using sweepR table 2 [true] [false] [true,false] [true,false] 2 local11 n (([true,true,false,false,true,false,true,false,true,false,true,false]) ++ (rep [true,false,true,false] (n)) ++ ([true])) ([])

theorem phase12 (n : Nat) : run0 table 2 ⟨2,([true]) ++ (rep [true,false] (n)) ++ ([true,true,false,false,true,false,true,false,true,false,true,false]) ++ (rep [true,false,true,false] (n)) ++ ([true]),([false])⟩ = some ⟨2,([false,true,false]) ++ (rep [true,false] (n)) ++ ([true,true,false,false,true,false,true,false,true,false,true,false]) ++ (rep [true,false,true,false] (n)) ++ ([true]),[]⟩ := by rfl

theorem finalL (n : Nat) : ([false,true,false]) ++ (rep [true,false] (n)) ++ ([true,true,false,false,true,false,true,false,true,false,true,false]) ++ (rep [true,false,true,false] (n)) ++ ([true]) = ([false,true,false,true]) ++ (rep [false,true] (n)) ++ ([true,false,false,true,false,true,false,true,false,true,false,true]) ++ (rep [false,true,false,true] (n)) := by
  calc
    _ = ([false,true]) ++ (rep [false,true] (n)) ++ ([false,true,true,false,false,true,false,true,false,true,false,true,false]) ++ (rep [true,false,true,false] (n)) ++ ([true]) := by simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using moveCut (([false,true])) (([true,true,false,false,true,false,true,false,true,false,true,false]) ++ (rep [true,false,true,false] (n)) ++ ([true])) [true] false n
    _ = ([false]) ++ (rep [true,false] (n)) ++ ([true,false,true,true,false,false,true,false,true,false,true,false,true,false]) ++ (rep [true,false,true,false] (n)) ++ ([true]) := by simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using moveCut (([false])) (([false,true,true,false,false,true,false,true,false,true,false,true,false]) ++ (rep [true,false,true,false] (n)) ++ ([true])) [false] true n
    _ = (rep [false,true] (n)) ++ ([false,true,false,true,true,false,false,true,false,true,false,true,false,true,false]) ++ (rep [true,false,true,false] (n)) ++ ([true]) := by simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using moveCut ([]) (([true,false,true,true,false,false,true,false,true,false,true,false,true,false]) ++ (rep [true,false,true,false] (n)) ++ ([true])) [true] false n
    _ = (rep [false,true] (n)) ++ ([false,true,false,true,true,false,false,true,false,true,false,true,false,true,false,true]) ++ (rep [false,true,false,true] (n)) := by symm; simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using moveCut ((rep [false,true] (n)) ++ ([false,true,false,true,true,false,false,true,false,true,false,true,false,true,false])) ([]) [false,true,false] true n
    _ = ([false]) ++ (rep [true,false] (n)) ++ ([true,false,true,true,false,false,true,false,true,false,true,false,true,false,true]) ++ (rep [false,true,false,true] (n)) := by symm; simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using moveCut ([]) (([true,false,true,true,false,false,true,false,true,false,true,false,true,false,true]) ++ (rep [false,true,false,true] (n))) [true] false n
    _ = ([false,true]) ++ (rep [false,true] (n)) ++ ([false,true,true,false,false,true,false,true,false,true,false,true,false,true]) ++ (rep [false,true,false,true] (n)) := by symm; simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using moveCut (([false])) (([false,true,true,false,false,true,false,true,false,true,false,true,false,true]) ++ (rep [false,true,false,true] (n))) [false] true n
    _ = ([false,true,false]) ++ (rep [true,false] (n)) ++ ([true,true,false,false,true,false,true,false,true,false,true,false,true]) ++ (rep [false,true,false,true] (n)) := by symm; simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using moveCut (([false,true])) (([true,true,false,false,true,false,true,false,true,false,true,false,true]) ++ (rep [false,true,false,true] (n))) [true] false n
    _ = ([false,true,false,true]) ++ (rep [false,true] (n)) ++ ([true,false,false,true,false,true,false,true,false,true,false,true]) ++ (rep [false,true,false,true] (n)) := by symm; simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using moveCut (([false,true,false])) (([true,false,false,true,false,true,false,true,false,true,false,true]) ++ (rep [false,true,false,true] (n))) [false] true n

theorem finalR (n : Nat) : ([] : List Bool) = [] := by
  rfl

theorem growth (n : Nat) : run0 table (54+20*n) (family n) = some (family (n+1)) := by
  have H := (join0 (join0 (join0 (join0 (join0 (join0 (join0 (join0 (join0 (join0 (join0 (join0 (phase0 n) (phase1 n)) (phase2 n)) (phase3 n)) (phase4 n)) (phase5 n)) (phase6 n)) (phase7 n)) (phase8 n)) (phase9 n)) (phase10 n)) (phase11 n)) (phase12 n))
  rw [finalL n] at H
  rw [show 9+2*n+11+4*n+6+4*n+5+4*n+9+4*n+12+2*n+2=54+20*n by omega] at H
  simpa only [family,rep,List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using H

theorem never (m : Machine) (hm : compatible table m) : NeverHalts m :=
  never_of_growth table family 31 (fun n => 54+20*n) entry (by intro n; omega) growth m hm

#print axioms never

end M1664

namespace M1776

-- 1RB0RE_1RC1LE_0RD0RA_1LD0RA_0LB1LF_0LE---

def table : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 0,true => some (some ⟨false,true,4⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 1,true => some (some ⟨true,false,4⟩)
  | 2,false => some (some ⟨false,true,3⟩)
  | 2,true => some (some ⟨false,true,0⟩)
  | 3,false => some (some ⟨true,false,3⟩)
  | 3,true => some (some ⟨false,true,0⟩)
  | 4,false => some (some ⟨false,false,1⟩)
  | 4,true => some (some ⟨true,false,5⟩)
  | 5,false => some (some ⟨false,false,4⟩)
  | _,_ => none

def family (n : Nat) : Z0 := ⟨1,([false,true]) ++ (rep [false,true,true,false,false,true] (n)),[]⟩

theorem entry : run0 table 1 ⟨0,[],[]⟩ = some (family 0) := by rfl

theorem phase0 (n : Nat) : run0 table 6 ⟨1,([false,true]) ++ (rep [false,true,true,false,false,true] (n)),[]⟩ = some ⟨4,([true,false,false,true]) ++ (rep [false,true,true,false,false,true] (n)),[]⟩ := by rfl

theorem local1 (L R : List Bool) : run0 table 6 ⟨4,([true,false,false,true]) ++ ([false,true,true,false,false,true]) ++ (L),(R)⟩ = some ⟨4,([true,false,false,true]) ++ (L),([true,false,true,false,false,true]) ++ (R)⟩ := by rfl

theorem phase1 (n : Nat) : run0 table (6*n) ⟨4,([true,false,false,true]) ++ (rep [false,true,true,false,false,true] (n)),[]⟩ = some ⟨4,([true,false,false,true]),(rep [true,false,true,false,false,true] (n))⟩ := by
  simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using sweepL table 4 [true,false,false,true] [] [false,true,true,false,false,true] [true,false,true,false,false,true] 6 local1 n ([]) ([])

theorem phase2 (n : Nat) : run0 table 6 ⟨4,([true,false,false,true]),(rep [true,false,true,false,false,true] (n))⟩ = some ⟨2,([false,true]),([true,false,false,true]) ++ (rep [true,false,true,false,false,true] (n))⟩ := by rfl

theorem local3 (L R : List Bool) : run0 table 8 ⟨2,([false]) ++ (L),([true,false,false,true]) ++ ([true,false,true,false,false,true]) ++ (R)⟩ = some ⟨2,([false]) ++ ([true,false,true,true,false,false]) ++ (L),([true,false,false,true]) ++ (R)⟩ := by rfl

theorem phase3 (n : Nat) : run0 table (8*n) ⟨2,([false,true]),([true,false,false,true]) ++ (rep [true,false,true,false,false,true] (n))⟩ = some ⟨2,([false]) ++ (rep [true,false,true,true,false,false] (n)) ++ ([true]),([true,false,false,true])⟩ := by
  simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using sweepR table 2 [false] [true,false,false,true] [true,false,true,false,false,true] [true,false,true,true,false,false] 8 local3 n (([true])) ([])

theorem phase4 (n : Nat) : run0 table 6 ⟨2,([false]) ++ (rep [true,false,true,true,false,false] (n)) ++ ([true]),([true,false,false,true])⟩ = some ⟨1,([false,true,false,true,true,false,false]) ++ (rep [true,false,true,true,false,false] (n)) ++ ([true]),[]⟩ := by rfl

theorem finalL (n : Nat) : ([false,true,false,true,true,false,false]) ++ (rep [true,false,true,true,false,false] (n)) ++ ([true]) = ([false,true,false,true,true,false,false,true]) ++ (rep [false,true,true,false,false,true] (n)) := by
  calc
    _ = ([false,true,false,true,true,false,false,true]) ++ (rep [false,true,true,false,false,true] (n)) := by symm; simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using moveCut (([false,true,false,true,true,false,false])) ([]) [false,true,true,false,false] true n

theorem finalR (n : Nat) : ([] : List Bool) = [] := by
  rfl

theorem growth (n : Nat) : run0 table (18+14*n) (family n) = some (family (n+1)) := by
  have H := (join0 (join0 (join0 (join0 (phase0 n) (phase1 n)) (phase2 n)) (phase3 n)) (phase4 n))
  rw [finalL n] at H
  rw [show 6+6*n+6+8*n+6=18+14*n by omega] at H
  simpa only [family,rep,List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using H

theorem never (m : Machine) (hm : compatible table m) : NeverHalts m :=
  never_of_growth table family 1 (fun n => 18+14*n) entry (by intro n; omega) growth m hm

#print axioms never

end M1776

namespace M1777

-- 1RB0RE_1RC1LE_0RD0RC_1LD0RA_0LB1LF_0LE---

def table : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 0,true => some (some ⟨false,true,4⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 1,true => some (some ⟨true,false,4⟩)
  | 2,false => some (some ⟨false,true,3⟩)
  | 2,true => some (some ⟨false,true,2⟩)
  | 3,false => some (some ⟨true,false,3⟩)
  | 3,true => some (some ⟨false,true,0⟩)
  | 4,false => some (some ⟨false,false,1⟩)
  | 4,true => some (some ⟨true,false,5⟩)
  | 5,false => some (some ⟨false,false,4⟩)
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

end M1777

namespace M1847

-- 1RB0RE_1RC---_0RD0RC_1LD0RA_0LB1LF_0LF1LE

def table : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 0,true => some (some ⟨false,true,4⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 2,false => some (some ⟨false,true,3⟩)
  | 2,true => some (some ⟨false,true,2⟩)
  | 3,false => some (some ⟨true,false,3⟩)
  | 3,true => some (some ⟨false,true,0⟩)
  | 4,false => some (some ⟨false,false,1⟩)
  | 4,true => some (some ⟨true,false,5⟩)
  | 5,false => some (some ⟨false,false,5⟩)
  | 5,true => some (some ⟨true,false,4⟩)
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

end M1847

namespace M1890

-- 1RB0RE_1RC0LF_0RD1RB_1LD0RA_---1LF_1LA1LB

def table : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 0,true => some (some ⟨false,true,4⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 1,true => some (some ⟨false,false,5⟩)
  | 2,false => some (some ⟨false,true,3⟩)
  | 2,true => some (some ⟨true,true,1⟩)
  | 3,false => some (some ⟨true,false,3⟩)
  | 3,true => some (some ⟨false,true,0⟩)
  | 4,true => some (some ⟨true,false,5⟩)
  | 5,false => some (some ⟨true,false,0⟩)
  | 5,true => some (some ⟨true,false,1⟩)
  | _,_ => none

def family (n : Nat) : Z0 := ⟨1,[],([true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true]) ++ (rep [false,true,false,true] (n))⟩

theorem entry : run0 table 486 ⟨0,[],[]⟩ = some (family 0) := by rfl

theorem phase0 (n : Nat) : run0 table 1 ⟨1,[],([true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true]) ++ (rep [false,true,false,true] (n))⟩ = some ⟨2,([true,true]),([false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true]) ++ (rep [false,true,false,true] (n))⟩ := by rfl

theorem local1 (L R : List Bool) : run0 table 4 ⟨2,([true]) ++ (L),([false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true]) ++ ([false,true,false,true]) ++ (R)⟩ = some ⟨2,([true]) ++ ([true,true,true,true]) ++ (L),([false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true]) ++ (R)⟩ := by rfl

theorem phase1 (n : Nat) : run0 table (4*n) ⟨2,([true,true]),([false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true]) ++ (rep [false,true,false,true] (n))⟩ = some ⟨2,([true]) ++ (rep [true,true,true,true] (n)) ++ ([true]),([false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true])⟩ := by
  simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using sweepR table 2 [true] [false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true] [false,true,false,true] [true,true,true,true] 4 local1 n (([true])) ([])

theorem phase2 (n : Nat) : run0 table 48 ⟨2,([true]) ++ (rep [true,true,true,true] (n)) ++ ([true]),([false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true])⟩ = some ⟨1,([true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true]) ++ (rep [true,true,true,true] (n)) ++ ([true]),([true])⟩ := by rfl

theorem local3 (L R : List Bool) : run0 table 4 ⟨1,([true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true]) ++ ([true,true,true,true]) ++ (L),(R)⟩ = some ⟨1,([true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true]) ++ (L),([true,false,true,false]) ++ (R)⟩ := by rfl

theorem phase3 (n : Nat) : run0 table (4*n) ⟨1,([true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true]) ++ (rep [true,true,true,true] (n)) ++ ([true]),([true])⟩ = some ⟨1,([true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true]),(rep [true,false,true,false] (n)) ++ ([true])⟩ := by
  simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using sweepL table 1 [true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true] [] [true,true,true,true] [true,false,true,false] 4 local3 n (([true])) (([true]))

theorem phase4 (n : Nat) : run0 table 42 ⟨1,([true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true]),(rep [true,false,true,false] (n)) ++ ([true])⟩ = some ⟨1,[],([true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false]) ++ (rep [true,false,true,false] (n)) ++ ([true])⟩ := by rfl

theorem finalL (n : Nat) : ([] : List Bool) = [] := by
  rfl

theorem finalR (n : Nat) : ([true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false]) ++ (rep [true,false,true,false] (n)) ++ ([true]) = ([true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true]) ++ (rep [false,true,false,true] (n)) := by
  calc
    _ = ([true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true]) ++ (rep [false,true,false,true] (n)) := by symm; simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using moveCut (([true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false])) ([]) [false,true,false] true n

theorem growth (n : Nat) : run0 table (91+8*n) (family n) = some (family (n+1)) := by
  have H := (join0 (join0 (join0 (join0 (phase0 n) (phase1 n)) (phase2 n)) (phase3 n)) (phase4 n))
  rw [finalR n] at H
  rw [show 1+4*n+48+4*n+42=91+8*n by omega] at H
  simpa only [family,rep,List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using H

theorem never (m : Machine) (hm : compatible table m) : NeverHalts m :=
  never_of_growth table family 486 (fun n => 91+8*n) entry (by intro n; omega) growth m hm

#print axioms never

end M1890

namespace M1973

-- 1RB0RE_1RC0LE_0RD0RB_1LD0RA_1LB1LF_1LB---

def table : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 0,true => some (some ⟨false,true,4⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 1,true => some (some ⟨false,false,4⟩)
  | 2,false => some (some ⟨false,true,3⟩)
  | 2,true => some (some ⟨false,true,1⟩)
  | 3,false => some (some ⟨true,false,3⟩)
  | 3,true => some (some ⟨false,true,0⟩)
  | 4,false => some (some ⟨true,false,1⟩)
  | 4,true => some (some ⟨true,false,5⟩)
  | 5,false => some (some ⟨true,false,1⟩)
  | _,_ => none

def family (n : Nat) : Z0 := ⟨2,([false,true]) ++ (rep [false,true] (n)) ++ ([true,false,false,true,false,true,false,true]) ++ (rep [false,true,false,true] (n)),[]⟩

theorem entry : run0 table 31 ⟨0,[],[]⟩ = some (family 0) := by rfl

theorem phase0 (n : Nat) : run0 table 9 ⟨2,([false,true]) ++ (rep [false,true] (n)) ++ ([true,false,false,true,false,true,false,true]) ++ (rep [false,true,false,true] (n)),[]⟩ = some ⟨1,([true,false,true]) ++ (rep [false,true] (n)) ++ ([true,false,false,true,false,true,false,true]) ++ (rep [false,true,false,true] (n)),[]⟩ := by rfl

theorem local1 (L R : List Bool) : run0 table 2 ⟨1,([true,false,true]) ++ ([false,true]) ++ (L),(R)⟩ = some ⟨1,([true,false,true]) ++ (L),([true,false]) ++ (R)⟩ := by rfl

theorem phase1 (n : Nat) : run0 table (2*n) ⟨1,([true,false,true]) ++ (rep [false,true] (n)) ++ ([true,false,false,true,false,true,false,true]) ++ (rep [false,true,false,true] (n)),[]⟩ = some ⟨1,([true,false,true,true,false,false,true,false,true,false,true]) ++ (rep [false,true,false,true] (n)),(rep [true,false] (n))⟩ := by
  simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using sweepL table 1 [true,false,true] [] [false,true] [true,false] 2 local1 n (([true,false,false,true,false,true,false,true]) ++ (rep [false,true,false,true] (n))) ([])

theorem phase2 (n : Nat) : run0 table 12 ⟨1,([true,false,true,true,false,false,true,false,true,false,true]) ++ (rep [false,true,false,true] (n)),(rep [true,false] (n))⟩ = some ⟨1,([true,false,true]) ++ (rep [false,true,false,true] (n)),([true,true,false,true,false,false,true,false]) ++ (rep [true,false] (n))⟩ := by rfl

theorem local3 (L R : List Bool) : run0 table 4 ⟨1,([true,false,true]) ++ ([false,true,false,true]) ++ (L),(R)⟩ = some ⟨1,([true,false,true]) ++ (L),([true,false,true,false]) ++ (R)⟩ := by rfl

theorem phase3 (n : Nat) : run0 table (4*n) ⟨1,([true,false,true]) ++ (rep [false,true,false,true] (n)),([true,true,false,true,false,false,true,false]) ++ (rep [true,false] (n))⟩ = some ⟨1,([true,false,true]),(rep [true,false,true,false] (n)) ++ ([true,true,false,true,false,false,true,false]) ++ (rep [true,false] (n))⟩ := by
  simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using sweepL table 1 [true,false,true] [] [false,true,false,true] [true,false,true,false] 4 local3 n ([]) (([true,true,false,true,false,false,true,false]) ++ (rep [true,false] (n)))

theorem phase4 (n : Nat) : run0 table 5 ⟨1,([true,false,true]),(rep [true,false,true,false] (n)) ++ ([true,true,false,true,false,false,true,false]) ++ (rep [true,false] (n))⟩ = some ⟨2,([true,true]),([false,true,false]) ++ (rep [true,false,true,false] (n)) ++ ([true,true,false,true,false,false,true,false]) ++ (rep [true,false] (n))⟩ := by rfl

theorem local5 (L R : List Bool) : run0 table 4 ⟨2,([true]) ++ (L),([false,true,false]) ++ ([true,false,true,false]) ++ (R)⟩ = some ⟨2,([true]) ++ ([true,false,true,false]) ++ (L),([false,true,false]) ++ (R)⟩ := by rfl

theorem phase5 (n : Nat) : run0 table (4*n) ⟨2,([true,true]),([false,true,false]) ++ (rep [true,false,true,false] (n)) ++ ([true,true,false,true,false,false,true,false]) ++ (rep [true,false] (n))⟩ = some ⟨2,([true]) ++ (rep [true,false,true,false] (n)) ++ ([true]),([false,true,false,true,true,false,true,false,false,true,false]) ++ (rep [true,false] (n))⟩ := by
  simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using sweepR table 2 [true] [false,true,false] [true,false,true,false] [true,false,true,false] 4 local5 n (([true])) (([true,true,false,true,false,false,true,false]) ++ (rep [true,false] (n)))

theorem phase6 (n : Nat) : run0 table 5 ⟨2,([true]) ++ (rep [true,false,true,false] (n)) ++ ([true]),([false,true,false,true,true,false,true,false,false,true,false]) ++ (rep [true,false] (n))⟩ = some ⟨1,([true,false,true,false,true,false]) ++ (rep [true,false,true,false] (n)) ++ ([true]),([false,true,false,false,true,false]) ++ (rep [true,false] (n))⟩ := by rfl

theorem local7 (L R : List Bool) : run0 table 4 ⟨1,([true,false,true,false,true,false]) ++ ([true,false,true,false]) ++ (L),(R)⟩ = some ⟨1,([true,false,true,false,true,false]) ++ (L),([true,false,true,false]) ++ (R)⟩ := by rfl

theorem phase7 (n : Nat) : run0 table (4*n) ⟨1,([true,false,true,false,true,false]) ++ (rep [true,false,true,false] (n)) ++ ([true]),([false,true,false,false,true,false]) ++ (rep [true,false] (n))⟩ = some ⟨1,([true,false,true,false,true,false,true]),(rep [true,false,true,false] (n)) ++ ([false,true,false,false,true,false]) ++ (rep [true,false] (n))⟩ := by
  simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using sweepL table 1 [true,false,true,false,true,false] [] [true,false,true,false] [true,false,true,false] 4 local7 n (([true])) (([false,true,false,false,true,false]) ++ (rep [true,false] (n)))

theorem phase8 (n : Nat) : run0 table 9 ⟨1,([true,false,true,false,true,false,true]),(rep [true,false,true,false] (n)) ++ ([false,true,false,false,true,false]) ++ (rep [true,false] (n))⟩ = some ⟨2,([true,true]),([false,true,false,true,false,true,false]) ++ (rep [true,false,true,false] (n)) ++ ([false,true,false,false,true,false]) ++ (rep [true,false] (n))⟩ := by rfl

theorem local9 (L R : List Bool) : run0 table 4 ⟨2,([true]) ++ (L),([false,true,false,true,false,true,false]) ++ ([true,false,true,false]) ++ (R)⟩ = some ⟨2,([true]) ++ ([true,false,true,false]) ++ (L),([false,true,false,true,false,true,false]) ++ (R)⟩ := by rfl

theorem phase9 (n : Nat) : run0 table (4*n) ⟨2,([true,true]),([false,true,false,true,false,true,false]) ++ (rep [true,false,true,false] (n)) ++ ([false,true,false,false,true,false]) ++ (rep [true,false] (n))⟩ = some ⟨2,([true]) ++ (rep [true,false,true,false] (n)) ++ ([true]),([false,true,false,true,false,true,false,false,true,false,false,true,false]) ++ (rep [true,false] (n))⟩ := by
  simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using sweepR table 2 [true] [false,true,false,true,false,true,false] [true,false,true,false] [true,false,true,false] 4 local9 n (([true])) (([false,true,false,false,true,false]) ++ (rep [true,false] (n)))

theorem phase10 (n : Nat) : run0 table 11 ⟨2,([true]) ++ (rep [true,false,true,false] (n)) ++ ([true]),([false,true,false,true,false,true,false,false,true,false,false,true,false]) ++ (rep [true,false] (n))⟩ = some ⟨1,([false,true,false,false,true,false,true,false,true,false,true,false]) ++ (rep [true,false,true,false] (n)) ++ ([true]),([true,false]) ++ (rep [true,false] (n))⟩ := by rfl

theorem local11 (L R : List Bool) : run0 table 2 ⟨1,([false]) ++ (L),([true,false]) ++ ([true,false]) ++ (R)⟩ = some ⟨1,([false]) ++ ([false,true]) ++ (L),([true,false]) ++ (R)⟩ := by rfl

theorem phase11 (n : Nat) : run0 table (2*n) ⟨1,([false,true,false,false,true,false,true,false,true,false,true,false]) ++ (rep [true,false,true,false] (n)) ++ ([true]),([true,false]) ++ (rep [true,false] (n))⟩ = some ⟨1,([false]) ++ (rep [false,true] (n)) ++ ([true,false,false,true,false,true,false,true,false,true,false]) ++ (rep [true,false,true,false] (n)) ++ ([true]),([true,false])⟩ := by
  simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using sweepR table 1 [false] [true,false] [true,false] [false,true] 2 local11 n (([true,false,false,true,false,true,false,true,false,true,false]) ++ (rep [true,false,true,false] (n)) ++ ([true])) ([])

theorem phase12 (n : Nat) : run0 table 3 ⟨1,([false]) ++ (rep [false,true] (n)) ++ ([true,false,false,true,false,true,false,true,false,true,false]) ++ (rep [true,false,true,false] (n)) ++ ([true]),([true,false])⟩ = some ⟨2,([false,true,false,true]) ++ (rep [false,true] (n)) ++ ([true,false,false,true,false,true,false,true,false,true,false]) ++ (rep [true,false,true,false] (n)) ++ ([true]),[]⟩ := by rfl

theorem finalL (n : Nat) : ([false,true,false,true]) ++ (rep [false,true] (n)) ++ ([true,false,false,true,false,true,false,true,false,true,false]) ++ (rep [true,false,true,false] (n)) ++ ([true]) = ([false,true,false,true]) ++ (rep [false,true] (n)) ++ ([true,false,false,true,false,true,false,true,false,true,false,true]) ++ (rep [false,true,false,true] (n)) := by
  calc
    _ = ([false,true,false]) ++ (rep [true,false] (n)) ++ ([true,true,false,false,true,false,true,false,true,false,true,false]) ++ (rep [true,false,true,false] (n)) ++ ([true]) := by simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using moveCut (([false,true,false])) (([true,false,false,true,false,true,false,true,false,true,false]) ++ (rep [true,false,true,false] (n)) ++ ([true])) [false] true n
    _ = ([false,true]) ++ (rep [false,true] (n)) ++ ([false,true,true,false,false,true,false,true,false,true,false,true,false]) ++ (rep [true,false,true,false] (n)) ++ ([true]) := by simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using moveCut (([false,true])) (([true,true,false,false,true,false,true,false,true,false,true,false]) ++ (rep [true,false,true,false] (n)) ++ ([true])) [true] false n
    _ = ([false]) ++ (rep [true,false] (n)) ++ ([true,false,true,true,false,false,true,false,true,false,true,false,true,false]) ++ (rep [true,false,true,false] (n)) ++ ([true]) := by simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using moveCut (([false])) (([false,true,true,false,false,true,false,true,false,true,false,true,false]) ++ (rep [true,false,true,false] (n)) ++ ([true])) [false] true n
    _ = (rep [false,true] (n)) ++ ([false,true,false,true,true,false,false,true,false,true,false,true,false,true,false]) ++ (rep [true,false,true,false] (n)) ++ ([true]) := by simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using moveCut ([]) (([true,false,true,true,false,false,true,false,true,false,true,false,true,false]) ++ (rep [true,false,true,false] (n)) ++ ([true])) [true] false n
    _ = (rep [false,true] (n)) ++ ([false,true,false,true,true,false,false,true,false,true,false,true,false,true,false,true]) ++ (rep [false,true,false,true] (n)) := by symm; simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using moveCut ((rep [false,true] (n)) ++ ([false,true,false,true,true,false,false,true,false,true,false,true,false,true,false])) ([]) [false,true,false] true n
    _ = ([false]) ++ (rep [true,false] (n)) ++ ([true,false,true,true,false,false,true,false,true,false,true,false,true,false,true]) ++ (rep [false,true,false,true] (n)) := by symm; simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using moveCut ([]) (([true,false,true,true,false,false,true,false,true,false,true,false,true,false,true]) ++ (rep [false,true,false,true] (n))) [true] false n
    _ = ([false,true]) ++ (rep [false,true] (n)) ++ ([false,true,true,false,false,true,false,true,false,true,false,true,false,true]) ++ (rep [false,true,false,true] (n)) := by symm; simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using moveCut (([false])) (([false,true,true,false,false,true,false,true,false,true,false,true,false,true]) ++ (rep [false,true,false,true] (n))) [false] true n
    _ = ([false,true,false]) ++ (rep [true,false] (n)) ++ ([true,true,false,false,true,false,true,false,true,false,true,false,true]) ++ (rep [false,true,false,true] (n)) := by symm; simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using moveCut (([false,true])) (([true,true,false,false,true,false,true,false,true,false,true,false,true]) ++ (rep [false,true,false,true] (n))) [true] false n
    _ = ([false,true,false,true]) ++ (rep [false,true] (n)) ++ ([true,false,false,true,false,true,false,true,false,true,false,true]) ++ (rep [false,true,false,true] (n)) := by symm; simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using moveCut (([false,true,false])) (([true,false,false,true,false,true,false,true,false,true,false,true]) ++ (rep [false,true,false,true] (n))) [false] true n

theorem finalR (n : Nat) : ([] : List Bool) = [] := by
  rfl

theorem growth (n : Nat) : run0 table (54+20*n) (family n) = some (family (n+1)) := by
  have H := (join0 (join0 (join0 (join0 (join0 (join0 (join0 (join0 (join0 (join0 (join0 (join0 (phase0 n) (phase1 n)) (phase2 n)) (phase3 n)) (phase4 n)) (phase5 n)) (phase6 n)) (phase7 n)) (phase8 n)) (phase9 n)) (phase10 n)) (phase11 n)) (phase12 n))
  rw [finalL n] at H
  rw [show 9+2*n+12+4*n+5+4*n+5+4*n+9+4*n+11+2*n+3=54+20*n by omega] at H
  simpa only [family,rep,List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using H

theorem never (m : Machine) (hm : compatible table m) : NeverHalts m :=
  never_of_growth table family 31 (fun n => 54+20*n) entry (by intro n; omega) growth m hm

#print axioms never

end M1973

namespace M1978

-- 1RB0RE_1RC0LF_0RD0RB_1LD0RA_---1LF_1LB1LF

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
  | 4,true => some (some ⟨true,false,5⟩)
  | 5,false => some (some ⟨true,false,1⟩)
  | 5,true => some (some ⟨true,false,5⟩)
  | _,_ => none

def family (n : Nat) : Z0 := ⟨2,([false,true]) ++ (rep [false,true] (n)) ++ ([true,false,false,true,false,true,false,true]) ++ (rep [false,true,false,true] (n)),[]⟩

theorem entry : run0 table 31 ⟨0,[],[]⟩ = some (family 0) := by rfl

theorem phase0 (n : Nat) : run0 table 9 ⟨2,([false,true]) ++ (rep [false,true] (n)) ++ ([true,false,false,true,false,true,false,true]) ++ (rep [false,true,false,true] (n)),[]⟩ = some ⟨1,([true,false,true]) ++ (rep [false,true] (n)) ++ ([true,false,false,true,false,true,false,true]) ++ (rep [false,true,false,true] (n)),[]⟩ := by rfl

theorem local1 (L R : List Bool) : run0 table 2 ⟨1,([true,false,true]) ++ ([false,true]) ++ (L),(R)⟩ = some ⟨1,([true,false,true]) ++ (L),([true,false]) ++ (R)⟩ := by rfl

theorem phase1 (n : Nat) : run0 table (2*n) ⟨1,([true,false,true]) ++ (rep [false,true] (n)) ++ ([true,false,false,true,false,true,false,true]) ++ (rep [false,true,false,true] (n)),[]⟩ = some ⟨1,([true,false,true,true,false,false,true,false,true,false,true]) ++ (rep [false,true,false,true] (n)),(rep [true,false] (n))⟩ := by
  simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using sweepL table 1 [true,false,true] [] [false,true] [true,false] 2 local1 n (([true,false,false,true,false,true,false,true]) ++ (rep [false,true,false,true] (n))) ([])

theorem phase2 (n : Nat) : run0 table 11 ⟨1,([true,false,true,true,false,false,true,false,true,false,true]) ++ (rep [false,true,false,true] (n)),(rep [true,false] (n))⟩ = some ⟨5,([false,true,false,true]) ++ (rep [false,true,false,true] (n)),([true,false,true,false,false,true,false]) ++ (rep [true,false] (n))⟩ := by rfl

theorem local3 (L R : List Bool) : run0 table 4 ⟨5,([false,true,false,true]) ++ ([false,true,false,true]) ++ (L),(R)⟩ = some ⟨5,([false,true,false,true]) ++ (L),([false,true,false,true]) ++ (R)⟩ := by rfl

theorem phase3 (n : Nat) : run0 table (4*n) ⟨5,([false,true,false,true]) ++ (rep [false,true,false,true] (n)),([true,false,true,false,false,true,false]) ++ (rep [true,false] (n))⟩ = some ⟨5,([false,true,false,true]),(rep [false,true,false,true] (n)) ++ ([true,false,true,false,false,true,false]) ++ (rep [true,false] (n))⟩ := by
  simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using sweepL table 5 [false,true,false,true] [] [false,true,false,true] [false,true,false,true] 4 local3 n ([]) (([true,false,true,false,false,true,false]) ++ (rep [true,false] (n)))

theorem phase4 (n : Nat) : run0 table 6 ⟨5,([false,true,false,true]),(rep [false,true,false,true] (n)) ++ ([true,false,true,false,false,true,false]) ++ (rep [true,false] (n))⟩ = some ⟨2,([true,true]),([false,true,false,true]) ++ (rep [false,true,false,true] (n)) ++ ([true,false,true,false,false,true,false]) ++ (rep [true,false] (n))⟩ := by rfl

theorem local5 (L R : List Bool) : run0 table 4 ⟨2,([true]) ++ (L),([false,true,false,true]) ++ ([false,true,false,true]) ++ (R)⟩ = some ⟨2,([true]) ++ ([true,false,true,false]) ++ (L),([false,true,false,true]) ++ (R)⟩ := by rfl

theorem phase5 (n : Nat) : run0 table (4*n) ⟨2,([true,true]),([false,true,false,true]) ++ (rep [false,true,false,true] (n)) ++ ([true,false,true,false,false,true,false]) ++ (rep [true,false] (n))⟩ = some ⟨2,([true]) ++ (rep [true,false,true,false] (n)) ++ ([true]),([false,true,false,true,true,false,true,false,false,true,false]) ++ (rep [true,false] (n))⟩ := by
  simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using sweepR table 2 [true] [false,true,false,true] [false,true,false,true] [true,false,true,false] 4 local5 n (([true])) (([true,false,true,false,false,true,false]) ++ (rep [true,false] (n)))

theorem phase6 (n : Nat) : run0 table 5 ⟨2,([true]) ++ (rep [true,false,true,false] (n)) ++ ([true]),([false,true,false,true,true,false,true,false,false,true,false]) ++ (rep [true,false] (n))⟩ = some ⟨1,([true,false,true,false,true,false]) ++ (rep [true,false,true,false] (n)) ++ ([true]),([false,true,false,false,true,false]) ++ (rep [true,false] (n))⟩ := by rfl

theorem local7 (L R : List Bool) : run0 table 4 ⟨1,([true,false,true,false,true,false]) ++ ([true,false,true,false]) ++ (L),(R)⟩ = some ⟨1,([true,false,true,false,true,false]) ++ (L),([true,false,true,false]) ++ (R)⟩ := by rfl

theorem phase7 (n : Nat) : run0 table (4*n) ⟨1,([true,false,true,false,true,false]) ++ (rep [true,false,true,false] (n)) ++ ([true]),([false,true,false,false,true,false]) ++ (rep [true,false] (n))⟩ = some ⟨1,([true,false,true,false,true,false,true]),(rep [true,false,true,false] (n)) ++ ([false,true,false,false,true,false]) ++ (rep [true,false] (n))⟩ := by
  simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using sweepL table 1 [true,false,true,false,true,false] [] [true,false,true,false] [true,false,true,false] 4 local7 n (([true])) (([false,true,false,false,true,false]) ++ (rep [true,false] (n)))

theorem phase8 (n : Nat) : run0 table 9 ⟨1,([true,false,true,false,true,false,true]),(rep [true,false,true,false] (n)) ++ ([false,true,false,false,true,false]) ++ (rep [true,false] (n))⟩ = some ⟨2,([true,true]),([false,true,false,true,false,true,false]) ++ (rep [true,false,true,false] (n)) ++ ([false,true,false,false,true,false]) ++ (rep [true,false] (n))⟩ := by rfl

theorem local9 (L R : List Bool) : run0 table 4 ⟨2,([true]) ++ (L),([false,true,false,true,false,true,false]) ++ ([true,false,true,false]) ++ (R)⟩ = some ⟨2,([true]) ++ ([true,false,true,false]) ++ (L),([false,true,false,true,false,true,false]) ++ (R)⟩ := by rfl

theorem phase9 (n : Nat) : run0 table (4*n) ⟨2,([true,true]),([false,true,false,true,false,true,false]) ++ (rep [true,false,true,false] (n)) ++ ([false,true,false,false,true,false]) ++ (rep [true,false] (n))⟩ = some ⟨2,([true]) ++ (rep [true,false,true,false] (n)) ++ ([true]),([false,true,false,true,false,true,false,false,true,false,false,true,false]) ++ (rep [true,false] (n))⟩ := by
  simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using sweepR table 2 [true] [false,true,false,true,false,true,false] [true,false,true,false] [true,false,true,false] 4 local9 n (([true])) (([false,true,false,false,true,false]) ++ (rep [true,false] (n)))

theorem phase10 (n : Nat) : run0 table 11 ⟨2,([true]) ++ (rep [true,false,true,false] (n)) ++ ([true]),([false,true,false,true,false,true,false,false,true,false,false,true,false]) ++ (rep [true,false] (n))⟩ = some ⟨1,([false,true,false,false,true,false,true,false,true,false,true,false]) ++ (rep [true,false,true,false] (n)) ++ ([true]),([true,false]) ++ (rep [true,false] (n))⟩ := by rfl

theorem local11 (L R : List Bool) : run0 table 2 ⟨1,([false]) ++ (L),([true,false]) ++ ([true,false]) ++ (R)⟩ = some ⟨1,([false]) ++ ([false,true]) ++ (L),([true,false]) ++ (R)⟩ := by rfl

theorem phase11 (n : Nat) : run0 table (2*n) ⟨1,([false,true,false,false,true,false,true,false,true,false,true,false]) ++ (rep [true,false,true,false] (n)) ++ ([true]),([true,false]) ++ (rep [true,false] (n))⟩ = some ⟨1,([false]) ++ (rep [false,true] (n)) ++ ([true,false,false,true,false,true,false,true,false,true,false]) ++ (rep [true,false,true,false] (n)) ++ ([true]),([true,false])⟩ := by
  simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using sweepR table 1 [false] [true,false] [true,false] [false,true] 2 local11 n (([true,false,false,true,false,true,false,true,false,true,false]) ++ (rep [true,false,true,false] (n)) ++ ([true])) ([])

theorem phase12 (n : Nat) : run0 table 3 ⟨1,([false]) ++ (rep [false,true] (n)) ++ ([true,false,false,true,false,true,false,true,false,true,false]) ++ (rep [true,false,true,false] (n)) ++ ([true]),([true,false])⟩ = some ⟨2,([false,true,false,true]) ++ (rep [false,true] (n)) ++ ([true,false,false,true,false,true,false,true,false,true,false]) ++ (rep [true,false,true,false] (n)) ++ ([true]),[]⟩ := by rfl

theorem finalL (n : Nat) : ([false,true,false,true]) ++ (rep [false,true] (n)) ++ ([true,false,false,true,false,true,false,true,false,true,false]) ++ (rep [true,false,true,false] (n)) ++ ([true]) = ([false,true,false,true]) ++ (rep [false,true] (n)) ++ ([true,false,false,true,false,true,false,true,false,true,false,true]) ++ (rep [false,true,false,true] (n)) := by
  calc
    _ = ([false,true,false]) ++ (rep [true,false] (n)) ++ ([true,true,false,false,true,false,true,false,true,false,true,false]) ++ (rep [true,false,true,false] (n)) ++ ([true]) := by simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using moveCut (([false,true,false])) (([true,false,false,true,false,true,false,true,false,true,false]) ++ (rep [true,false,true,false] (n)) ++ ([true])) [false] true n
    _ = ([false,true]) ++ (rep [false,true] (n)) ++ ([false,true,true,false,false,true,false,true,false,true,false,true,false]) ++ (rep [true,false,true,false] (n)) ++ ([true]) := by simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using moveCut (([false,true])) (([true,true,false,false,true,false,true,false,true,false,true,false]) ++ (rep [true,false,true,false] (n)) ++ ([true])) [true] false n
    _ = ([false]) ++ (rep [true,false] (n)) ++ ([true,false,true,true,false,false,true,false,true,false,true,false,true,false]) ++ (rep [true,false,true,false] (n)) ++ ([true]) := by simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using moveCut (([false])) (([false,true,true,false,false,true,false,true,false,true,false,true,false]) ++ (rep [true,false,true,false] (n)) ++ ([true])) [false] true n
    _ = (rep [false,true] (n)) ++ ([false,true,false,true,true,false,false,true,false,true,false,true,false,true,false]) ++ (rep [true,false,true,false] (n)) ++ ([true]) := by simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using moveCut ([]) (([true,false,true,true,false,false,true,false,true,false,true,false,true,false]) ++ (rep [true,false,true,false] (n)) ++ ([true])) [true] false n
    _ = (rep [false,true] (n)) ++ ([false,true,false,true,true,false,false,true,false,true,false,true,false,true,false,true]) ++ (rep [false,true,false,true] (n)) := by symm; simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using moveCut ((rep [false,true] (n)) ++ ([false,true,false,true,true,false,false,true,false,true,false,true,false,true,false])) ([]) [false,true,false] true n
    _ = ([false]) ++ (rep [true,false] (n)) ++ ([true,false,true,true,false,false,true,false,true,false,true,false,true,false,true]) ++ (rep [false,true,false,true] (n)) := by symm; simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using moveCut ([]) (([true,false,true,true,false,false,true,false,true,false,true,false,true,false,true]) ++ (rep [false,true,false,true] (n))) [true] false n
    _ = ([false,true]) ++ (rep [false,true] (n)) ++ ([false,true,true,false,false,true,false,true,false,true,false,true,false,true]) ++ (rep [false,true,false,true] (n)) := by symm; simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using moveCut (([false])) (([false,true,true,false,false,true,false,true,false,true,false,true,false,true]) ++ (rep [false,true,false,true] (n))) [false] true n
    _ = ([false,true,false]) ++ (rep [true,false] (n)) ++ ([true,true,false,false,true,false,true,false,true,false,true,false,true]) ++ (rep [false,true,false,true] (n)) := by symm; simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using moveCut (([false,true])) (([true,true,false,false,true,false,true,false,true,false,true,false,true]) ++ (rep [false,true,false,true] (n))) [true] false n
    _ = ([false,true,false,true]) ++ (rep [false,true] (n)) ++ ([true,false,false,true,false,true,false,true,false,true,false,true]) ++ (rep [false,true,false,true] (n)) := by symm; simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using moveCut (([false,true,false])) (([true,false,false,true,false,true,false,true,false,true,false,true]) ++ (rep [false,true,false,true] (n))) [false] true n

theorem finalR (n : Nat) : ([] : List Bool) = [] := by
  rfl

theorem growth (n : Nat) : run0 table (54+20*n) (family n) = some (family (n+1)) := by
  have H := (join0 (join0 (join0 (join0 (join0 (join0 (join0 (join0 (join0 (join0 (join0 (join0 (phase0 n) (phase1 n)) (phase2 n)) (phase3 n)) (phase4 n)) (phase5 n)) (phase6 n)) (phase7 n)) (phase8 n)) (phase9 n)) (phase10 n)) (phase11 n)) (phase12 n))
  rw [finalL n] at H
  rw [show 9+2*n+11+4*n+6+4*n+5+4*n+9+4*n+11+2*n+3=54+20*n by omega] at H
  simpa only [family,rep,List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using H

theorem never (m : Machine) (hm : compatible table m) : NeverHalts m :=
  never_of_growth table family 31 (fun n => 54+20*n) entry (by intro n; omega) growth m hm

#print axioms never

end M1978

namespace M1981

-- 1RB0RE_1RC0LF_0RD0RB_1LD0RA_---1LF_1LB1RF

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
  | 4,true => some (some ⟨true,false,5⟩)
  | 5,false => some (some ⟨true,false,1⟩)
  | 5,true => some (some ⟨true,true,5⟩)
  | _,_ => none

def family (n : Nat) : Z0 := ⟨3,([false,false,true,false,true,false,true,false,true]) ++ (rep [false,true,false,true] (n)),[]⟩

theorem entry : run0 table 36 ⟨0,[],[]⟩ = some (family 0) := by rfl

theorem phase0 (n : Nat) : run0 table 8 ⟨3,([false,false,true,false,true,false,true,false,true]) ++ (rep [false,true,false,true] (n)),[]⟩ = some ⟨1,([true,false,true,false,true,false,true,false,true]) ++ (rep [false,true,false,true] (n)),[]⟩ := by rfl

theorem local1 (L R : List Bool) : run0 table 4 ⟨1,([true,false,true,false,true,false,true,false,true]) ++ ([false,true,false,true]) ++ (L),(R)⟩ = some ⟨1,([true,false,true,false,true,false,true,false,true]) ++ (L),([true,false,true,false]) ++ (R)⟩ := by rfl

theorem phase1 (n : Nat) : run0 table (4*n) ⟨1,([true,false,true,false,true,false,true,false,true]) ++ (rep [false,true,false,true] (n)),[]⟩ = some ⟨1,([true,false,true,false,true,false,true,false,true]),(rep [true,false,true,false] (n))⟩ := by
  simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using sweepL table 1 [true,false,true,false,true,false,true,false,true] [] [false,true,false,true] [true,false,true,false] 4 local1 n ([]) ([])

theorem phase2 (n : Nat) : run0 table 11 ⟨1,([true,false,true,false,true,false,true,false,true]),(rep [true,false,true,false] (n))⟩ = some ⟨2,([true,true]),([false,true,false,true,false,true,false,true,false]) ++ (rep [true,false,true,false] (n))⟩ := by rfl

theorem local3 (L R : List Bool) : run0 table 4 ⟨2,([true]) ++ (L),([false,true,false,true,false,true,false,true,false]) ++ ([true,false,true,false]) ++ (R)⟩ = some ⟨2,([true]) ++ ([true,false,true,false]) ++ (L),([false,true,false,true,false,true,false,true,false]) ++ (R)⟩ := by rfl

theorem phase3 (n : Nat) : run0 table (4*n) ⟨2,([true,true]),([false,true,false,true,false,true,false,true,false]) ++ (rep [true,false,true,false] (n))⟩ = some ⟨2,([true]) ++ (rep [true,false,true,false] (n)) ++ ([true]),([false,true,false,true,false,true,false,true,false])⟩ := by
  simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using sweepR table 2 [true] [false,true,false,true,false,true,false,true,false] [true,false,true,false] [true,false,true,false] 4 local3 n (([true])) ([])

theorem phase4 (n : Nat) : run0 table 11 ⟨2,([true]) ++ (rep [true,false,true,false] (n)) ++ ([true]),([false,true,false,true,false,true,false,true,false])⟩ = some ⟨3,([false,false,true,false,true,false,true,false,true,false,true,false]) ++ (rep [true,false,true,false] (n)) ++ ([true]),[]⟩ := by rfl

theorem finalL (n : Nat) : ([false,false,true,false,true,false,true,false,true,false,true,false]) ++ (rep [true,false,true,false] (n)) ++ ([true]) = ([false,false,true,false,true,false,true,false,true,false,true,false,true]) ++ (rep [false,true,false,true] (n)) := by
  calc
    _ = ([false,false,true,false,true,false,true,false,true,false,true,false,true]) ++ (rep [false,true,false,true] (n)) := by symm; simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using moveCut (([false,false,true,false,true,false,true,false,true,false,true,false])) ([]) [false,true,false] true n

theorem finalR (n : Nat) : ([] : List Bool) = [] := by
  rfl

theorem growth (n : Nat) : run0 table (30+8*n) (family n) = some (family (n+1)) := by
  have H := (join0 (join0 (join0 (join0 (phase0 n) (phase1 n)) (phase2 n)) (phase3 n)) (phase4 n))
  rw [finalL n] at H
  rw [show 8+4*n+11+4*n+11=30+8*n by omega] at H
  simpa only [family,rep,List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using H

theorem never (m : Machine) (hm : compatible table m) : NeverHalts m :=
  never_of_growth table family 36 (fun n => 30+8*n) entry (by intro n; omega) growth m hm

#print axioms never

end M1981

end BB6.Agent11Raw39B0REPumps
