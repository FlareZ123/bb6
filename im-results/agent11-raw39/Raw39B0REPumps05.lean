import SweepPumping
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedVariables false
namespace BB6.Agent11Raw39B0REPumps
open BB6Coverage BB6Coverage.Agent31Pump


namespace M2150

-- 1RB0RE_1RC---_0RD0RF_1LD0RA_0LE1LF_1RA0LA

def table : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 0,true => some (some ⟨false,true,4⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 2,false => some (some ⟨false,true,3⟩)
  | 2,true => some (some ⟨false,true,5⟩)
  | 3,false => some (some ⟨true,false,3⟩)
  | 3,true => some (some ⟨false,true,0⟩)
  | 4,false => some (some ⟨false,false,4⟩)
  | 4,true => some (some ⟨true,false,5⟩)
  | 5,false => some (some ⟨true,true,0⟩)
  | 5,true => some (some ⟨false,false,0⟩)
  | _,_ => none

def family (n : Nat) : Z0 := ⟨2,([false,true,true]) ++ (rep [true,false,true,true] (n)),[]⟩

theorem entry : run0 table 2 ⟨0,[],[]⟩ = some (family 0) := by rfl

theorem phase0 (n : Nat) : run0 table 13 ⟨2,([false,true,true]) ++ (rep [true,false,true,true] (n)),[]⟩ = some ⟨4,([false,false,true,true]) ++ (rep [true,false,true,true] (n)),([false])⟩ := by rfl

theorem local1 (L R : List Bool) : run0 table 6 ⟨4,([false,false,true,true]) ++ ([true,false,true,true]) ++ (L),(R)⟩ = some ⟨4,([false,false,true,true]) ++ (L),([false,true,false,false]) ++ (R)⟩ := by rfl

theorem phase1 (n : Nat) : run0 table (6*n) ⟨4,([false,false,true,true]) ++ (rep [true,false,true,true] (n)),([false])⟩ = some ⟨4,([false,false,true,true]),(rep [false,true,false,false] (n)) ++ ([false])⟩ := by
  simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using sweepL table 4 [false,false,true,true] [] [true,false,true,true] [false,true,false,false] 6 local1 n ([]) (([false]))

theorem phase2 (n : Nat) : run0 table 5 ⟨4,([false,false,true,true]),(rep [false,true,false,false] (n)) ++ ([false])⟩ = some ⟨1,([false,true]),([true,false,false]) ++ (rep [false,true,false,false] (n)) ++ ([false])⟩ := by rfl

theorem local3 (L R : List Bool) : run0 table 4 ⟨1,([false]) ++ (L),([true,false,false]) ++ ([false,true,false,false]) ++ (R)⟩ = some ⟨1,([false]) ++ ([true,true,false,true]) ++ (L),([true,false,false]) ++ (R)⟩ := by rfl

theorem phase3 (n : Nat) : run0 table (4*n) ⟨1,([false,true]),([true,false,false]) ++ (rep [false,true,false,false] (n)) ++ ([false])⟩ = some ⟨1,([false]) ++ (rep [true,true,false,true] (n)) ++ ([true]),([true,false,false,false])⟩ := by
  simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using sweepR table 1 [false] [true,false,false] [false,true,false,false] [true,true,false,true] 4 local3 n (([true])) (([false]))

theorem phase4 (n : Nat) : run0 table 5 ⟨1,([false]) ++ (rep [true,true,false,true] (n)) ++ ([true]),([true,false,false,false])⟩ = some ⟨2,([false,true,true,true,false,true]) ++ (rep [true,true,false,true] (n)) ++ ([true]),[]⟩ := by rfl

theorem finalL (n : Nat) : ([false,true,true,true,false,true]) ++ (rep [true,true,false,true] (n)) ++ ([true]) = ([false,true,true,true,false,true,true]) ++ (rep [true,false,true,true] (n)) := by
  calc
    _ = ([false,true,true,true,false,true,true]) ++ (rep [true,false,true,true] (n)) := by symm; simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using moveCut (([false,true,true,true,false,true])) ([]) [true,false,true] true n

theorem finalR (n : Nat) : ([] : List Bool) = [] := by
  rfl

theorem growth (n : Nat) : run0 table (23+10*n) (family n) = some (family (n+1)) := by
  have H := (join0 (join0 (join0 (join0 (phase0 n) (phase1 n)) (phase2 n)) (phase3 n)) (phase4 n))
  rw [finalL n] at H
  rw [show 13+6*n+5+4*n+5=23+10*n by omega] at H
  simpa only [family,rep,List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using H

theorem never (m : Machine) (hm : compatible table m) : NeverHalts m :=
  never_of_growth table family 2 (fun n => 23+10*n) entry (by intro n; omega) growth m hm

#print axioms never

end M2150

namespace M2379

-- 1RB0RE_1RC0RF_0RD0LE_1LD0RA_1LC1RE_1RE---

def table : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 0,true => some (some ⟨false,true,4⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 1,true => some (some ⟨false,true,5⟩)
  | 2,false => some (some ⟨false,true,3⟩)
  | 2,true => some (some ⟨false,false,4⟩)
  | 3,false => some (some ⟨true,false,3⟩)
  | 3,true => some (some ⟨false,true,0⟩)
  | 4,false => some (some ⟨true,false,2⟩)
  | 4,true => some (some ⟨true,true,4⟩)
  | 5,false => some (some ⟨true,true,4⟩)
  | _,_ => none

def family (n : Nat) : Z0 := ⟨4,([false,true]) ++ (rep [true] (n)) ++ ([false,true,false,false,true]),[]⟩

theorem entry : run0 table 16 ⟨0,[],[]⟩ = some (family 0) := by rfl

theorem local0 (L R : List Bool) : run0 table 3 ⟨4,([false,true]) ++ ([true]) ++ (L),(R)⟩ = some ⟨4,([false,true]) ++ (L),([true]) ++ (R)⟩ := by rfl

theorem phase0 (n : Nat) : run0 table (3*n) ⟨4,([false,true]) ++ (rep [true] (n)) ++ ([false,true,false,false,true]),[]⟩ = some ⟨4,([false,true,false,true,false,false,true]),(rep [true] (n))⟩ := by
  simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using sweepL table 4 [false,true] [] [true] [true] 3 local0 n (([false,true,false,false,true])) ([])

theorem phase1 (n : Nat) : run0 table 10 ⟨4,([false,true,false,true,false,false,true]),(rep [true] (n))⟩ = some ⟨4,([true,true,false,true,false,false,true]),(rep [true] (n))⟩ := by rfl

theorem local2 (L R : List Bool) : run0 table 1 ⟨4,([true]) ++ (L),([true]) ++ (R)⟩ = some ⟨4,([true]) ++ ([true]) ++ (L),(R)⟩ := by rfl

theorem phase2 (n : Nat) : run0 table (1*n) ⟨4,([true,true,false,true,false,false,true]),(rep [true] (n))⟩ = some ⟨4,([true]) ++ (rep [true] (n)) ++ ([true,false,true,false,false,true]),[]⟩ := by
  simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using sweepR table 4 [true] [] [true] [true] 1 local2 n (([true,false,true,false,false,true])) ([])

theorem phase3 (n : Nat) : run0 table 1 ⟨4,([true]) ++ (rep [true] (n)) ++ ([true,false,true,false,false,true]),[]⟩ = some ⟨4,([false,true]) ++ (rep [true] (n)) ++ ([true,false,true,false,false,true]),[]⟩ := by rfl

theorem finalL (n : Nat) : ([false,true]) ++ (rep [true] (n)) ++ ([true,false,true,false,false,true]) = ([false,true,true]) ++ (rep [true] (n)) ++ ([false,true,false,false,true]) := by
  calc
    _ = ([false,true,true]) ++ (rep [true] (n)) ++ ([false,true,false,false,true]) := by symm; simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using moveCut (([false,true])) (([false,true,false,false,true])) [] true n

theorem finalR (n : Nat) : ([] : List Bool) = [] := by
  rfl

theorem growth (n : Nat) : run0 table (11+4*n) (family n) = some (family (n+1)) := by
  have H := (join0 (join0 (join0 (phase0 n) (phase1 n)) (phase2 n)) (phase3 n))
  rw [finalL n] at H
  rw [show 3*n+10+1*n+1=11+4*n by omega] at H
  simpa only [family,rep,List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using H

theorem never (m : Machine) (hm : compatible table m) : NeverHalts m :=
  never_of_growth table family 16 (fun n => 11+4*n) entry (by intro n; omega) growth m hm

#print axioms never

end M2379

namespace M2383

-- 1RB0RE_1RC1RF_0RD0LE_1LD0RA_1LC1RE_1LA---

def table : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 0,true => some (some ⟨false,true,4⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 1,true => some (some ⟨true,true,5⟩)
  | 2,false => some (some ⟨false,true,3⟩)
  | 2,true => some (some ⟨false,false,4⟩)
  | 3,false => some (some ⟨true,false,3⟩)
  | 3,true => some (some ⟨false,true,0⟩)
  | 4,false => some (some ⟨true,false,2⟩)
  | 4,true => some (some ⟨true,true,4⟩)
  | 5,false => some (some ⟨true,false,0⟩)
  | _,_ => none

def family (n : Nat) : Z0 := ⟨4,([false,true]) ++ (rep [true] (n)) ++ ([false,true,false,false,true]),[]⟩

theorem entry : run0 table 18 ⟨0,[],[]⟩ = some (family 0) := by rfl

theorem local0 (L R : List Bool) : run0 table 3 ⟨4,([false,true]) ++ ([true]) ++ (L),(R)⟩ = some ⟨4,([false,true]) ++ (L),([true]) ++ (R)⟩ := by rfl

theorem phase0 (n : Nat) : run0 table (3*n) ⟨4,([false,true]) ++ (rep [true] (n)) ++ ([false,true,false,false,true]),[]⟩ = some ⟨4,([false,true,false,true,false,false,true]),(rep [true] (n))⟩ := by
  simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using sweepL table 4 [false,true] [] [true] [true] 3 local0 n (([false,true,false,false,true])) ([])

theorem phase1 (n : Nat) : run0 table 11 ⟨4,([false,true,false,true,false,false,true]),(rep [true] (n))⟩ = some ⟨4,([true,false,true,false,false,true]),([true]) ++ (rep [true] (n))⟩ := by rfl

theorem local2 (L R : List Bool) : run0 table 1 ⟨4,([true]) ++ (L),([true]) ++ ([true]) ++ (R)⟩ = some ⟨4,([true]) ++ ([true]) ++ (L),([true]) ++ (R)⟩ := by rfl

theorem phase2 (n : Nat) : run0 table (1*n) ⟨4,([true,false,true,false,false,true]),([true]) ++ (rep [true] (n))⟩ = some ⟨4,([true]) ++ (rep [true] (n)) ++ ([false,true,false,false,true]),([true])⟩ := by
  simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using sweepR table 4 [true] [true] [true] [true] 1 local2 n (([false,true,false,false,true])) ([])

theorem phase3 (n : Nat) : run0 table 2 ⟨4,([true]) ++ (rep [true] (n)) ++ ([false,true,false,false,true]),([true])⟩ = some ⟨4,([false,true,true]) ++ (rep [true] (n)) ++ ([false,true,false,false,true]),[]⟩ := by rfl

theorem finalL (n : Nat) : ([false,true,true]) ++ (rep [true] (n)) ++ ([false,true,false,false,true]) = ([false,true,true]) ++ (rep [true] (n)) ++ ([false,true,false,false,true]) := by
  rfl

theorem finalR (n : Nat) : ([] : List Bool) = [] := by
  rfl

theorem growth (n : Nat) : run0 table (13+4*n) (family n) = some (family (n+1)) := by
  have H := (join0 (join0 (join0 (phase0 n) (phase1 n)) (phase2 n)) (phase3 n))
  rw [show 3*n+11+1*n+2=13+4*n by omega] at H
  simpa only [family,rep,List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using H

theorem never (m : Machine) (hm : compatible table m) : NeverHalts m :=
  never_of_growth table family 18 (fun n => 13+4*n) entry (by intro n; omega) growth m hm

#print axioms never

end M2383

namespace M2387

-- 1RB0RE_1RC---_0RD0LF_1LD0RA_1LC1RE_1LB0LE

def table : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 0,true => some (some ⟨false,true,4⟩)
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

def family (n : Nat) : Z0 := ⟨1,([false,true,false,false,true,true,false,false,true,true,false,false]) ++ (rep [true,true,false,false,true,true,false,false] (n)),[]⟩

theorem entry : run0 table 69 ⟨0,[],[]⟩ = some (family 0) := by rfl

theorem phase0 (n : Nat) : run0 table 10 ⟨1,([false,true,false,false,true,true,false,false,true,true,false,false]) ++ (rep [true,true,false,false,true,true,false,false] (n)),[]⟩ = some ⟨1,([false,true,false,false,true,true,false,false,true,true,false,false]) ++ (rep [true,true,false,false,true,true,false,false] (n)),([true,false,true])⟩ := by rfl

theorem local1 (L R : List Bool) : run0 table 36 ⟨1,([false,true,false,false,true,true,false,false,true,true,false,false]) ++ ([true,true,false,false,true,true,false,false]) ++ (L),([true]) ++ (R)⟩ = some ⟨1,([false,true,false,false,true,true,false,false,true,true,false,false]) ++ (L),([true]) ++ ([false,false,true,false,false,false,true,false]) ++ (R)⟩ := by rfl

theorem phase1 (n : Nat) : run0 table (36*n) ⟨1,([false,true,false,false,true,true,false,false,true,true,false,false]) ++ (rep [true,true,false,false,true,true,false,false] (n)),([true,false,true])⟩ = some ⟨1,([false,true,false,false,true,true,false,false,true,true,false,false]),([true]) ++ (rep [false,false,true,false,false,false,true,false] (n)) ++ ([false,true])⟩ := by
  simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using sweepL table 1 [false,true,false,false,true,true,false,false,true,true,false,false] [true] [true,true,false,false,true,true,false,false] [false,false,true,false,false,false,true,false] 36 local1 n ([]) (([false,true]))

theorem phase2 (n : Nat) : run0 table 48 ⟨1,([false,true,false,false,true,true,false,false,true,true,false,false]),([true]) ++ (rep [false,false,true,false,false,false,true,false] (n)) ++ ([false,true])⟩ = some ⟨3,([true,false]),([false,false,false,true,false,false,false,true,false,false,false,true,false]) ++ (rep [false,false,true,false,false,false,true,false] (n)) ++ ([false,true])⟩ := by rfl

theorem local3 (L R : List Bool) : run0 table 8 ⟨3,([true]) ++ (L),([false,false,false,true,false,false,false,true,false,false,false,true,false]) ++ ([false,false,true,false,false,false,true,false]) ++ (R)⟩ = some ⟨3,([true]) ++ ([false,true,true,false,false,true,true,false]) ++ (L),([false,false,false,true,false,false,false,true,false,false,false,true,false]) ++ (R)⟩ := by rfl

theorem phase3 (n : Nat) : run0 table (8*n) ⟨3,([true,false]),([false,false,false,true,false,false,false,true,false,false,false,true,false]) ++ (rep [false,false,true,false,false,false,true,false] (n)) ++ ([false,true])⟩ = some ⟨3,([true]) ++ (rep [false,true,true,false,false,true,true,false] (n)) ++ ([false]),([false,false,false,true,false,false,false,true,false,false,false,true,false,false,true])⟩ := by
  simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using sweepR table 3 [true] [false,false,false,true,false,false,false,true,false,false,false,true,false] [false,false,true,false,false,false,true,false] [false,true,true,false,false,true,true,false] 8 local3 n (([false])) (([false,true]))

theorem phase4 (n : Nat) : run0 table 11 ⟨3,([true]) ++ (rep [false,true,true,false,false,true,true,false] (n)) ++ ([false]),([false,false,false,true,false,false,false,true,false,false,false,true,false,false,true])⟩ = some ⟨2,([false,true,true,false,false,true,true,false,false,true,true,false]) ++ (rep [false,true,true,false,false,true,true,false] (n)) ++ ([false]),([true,false,false,true])⟩ := by rfl

theorem local5 (L R : List Bool) : run0 table 36 ⟨2,([false,true,true,false,false,true,true,false,false,true,true,false]) ++ ([false,true,true,false,false,true,true,false]) ++ (L),([true,false,false,true]) ++ (R)⟩ = some ⟨2,([false,true,true,false,false,true,true,false,false,true,true,false]) ++ (L),([true,false,false,true]) ++ ([false,false,true,false,false,false,true,false]) ++ (R)⟩ := by rfl

theorem phase5 (n : Nat) : run0 table (36*n) ⟨2,([false,true,true,false,false,true,true,false,false,true,true,false]) ++ (rep [false,true,true,false,false,true,true,false] (n)) ++ ([false]),([true,false,false,true])⟩ = some ⟨2,([false,true,true,false,false,true,true,false,false,true,true,false,false]),([true,false,false,true]) ++ (rep [false,false,true,false,false,false,true,false] (n))⟩ := by
  simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using sweepL table 2 [false,true,true,false,false,true,true,false,false,true,true,false] [true,false,false,true] [false,true,true,false,false,true,true,false] [false,false,true,false,false,false,true,false] 36 local5 n (([false])) ([])

theorem phase6 (n : Nat) : run0 table 69 ⟨2,([false,true,true,false,false,true,true,false,false,true,true,false,false]),([true,false,false,true]) ++ (rep [false,false,true,false,false,false,true,false] (n))⟩ = some ⟨3,([true,false]),([false,false,false,true,false,false,false,true,false,false,false,true,false,false,false,true,false]) ++ (rep [false,false,true,false,false,false,true,false] (n))⟩ := by rfl

theorem local7 (L R : List Bool) : run0 table 8 ⟨3,([true]) ++ (L),([false,false,false,true,false,false,false,true,false,false,false,true,false,false,false,true,false]) ++ ([false,false,true,false,false,false,true,false]) ++ (R)⟩ = some ⟨3,([true]) ++ ([false,true,true,false,false,true,true,false]) ++ (L),([false,false,false,true,false,false,false,true,false,false,false,true,false,false,false,true,false]) ++ (R)⟩ := by rfl

theorem phase7 (n : Nat) : run0 table (8*n) ⟨3,([true,false]),([false,false,false,true,false,false,false,true,false,false,false,true,false,false,false,true,false]) ++ (rep [false,false,true,false,false,false,true,false] (n))⟩ = some ⟨3,([true]) ++ (rep [false,true,true,false,false,true,true,false] (n)) ++ ([false]),([false,false,false,true,false,false,false,true,false,false,false,true,false,false,false,true,false])⟩ := by
  simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using sweepR table 3 [true] [false,false,false,true,false,false,false,true,false,false,false,true,false,false,false,true,false] [false,false,true,false,false,false,true,false] [false,true,true,false,false,true,true,false] 8 local7 n (([false])) ([])

theorem phase8 (n : Nat) : run0 table 18 ⟨3,([true]) ++ (rep [false,true,true,false,false,true,true,false] (n)) ++ ([false]),([false,false,false,true,false,false,false,true,false,false,false,true,false,false,false,true,false])⟩ = some ⟨1,([false,true,false,false,true,true,false,false,true,true,false,false,true,true,false,false,true,true,false]) ++ (rep [false,true,true,false,false,true,true,false] (n)) ++ ([false]),[]⟩ := by rfl

theorem finalL (n : Nat) : ([false,true,false,false,true,true,false,false,true,true,false,false,true,true,false,false,true,true,false]) ++ (rep [false,true,true,false,false,true,true,false] (n)) ++ ([false]) = ([false,true,false,false,true,true,false,false,true,true,false,false,true,true,false,false,true,true,false,false]) ++ (rep [true,true,false,false,true,true,false,false] (n)) := by
  calc
    _ = ([false,true,false,false,true,true,false,false,true,true,false,false,true,true,false,false,true,true,false,false]) ++ (rep [true,true,false,false,true,true,false,false] (n)) := by symm; simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using moveCut (([false,true,false,false,true,true,false,false,true,true,false,false,true,true,false,false,true,true,false])) ([]) [true,true,false,false,true,true,false] false n

theorem finalR (n : Nat) : ([] : List Bool) = [] := by
  rfl

theorem growth (n : Nat) : run0 table (156+88*n) (family n) = some (family (n+1)) := by
  have H := (join0 (join0 (join0 (join0 (join0 (join0 (join0 (join0 (phase0 n) (phase1 n)) (phase2 n)) (phase3 n)) (phase4 n)) (phase5 n)) (phase6 n)) (phase7 n)) (phase8 n))
  rw [finalL n] at H
  rw [show 10+36*n+48+8*n+11+36*n+69+8*n+18=156+88*n by omega] at H
  simpa only [family,rep,List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using H

theorem never (m : Machine) (hm : compatible table m) : NeverHalts m :=
  never_of_growth table family 69 (fun n => 156+88*n) entry (by intro n; omega) growth m hm

#print axioms never

end M2387

namespace M2434

-- 1RB0RE_1RC---_0RD1RC_1LD0RA_1LF1RE_0LF1LC

def table : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 0,true => some (some ⟨false,true,4⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 2,false => some (some ⟨false,true,3⟩)
  | 2,true => some (some ⟨true,true,2⟩)
  | 3,false => some (some ⟨true,false,3⟩)
  | 3,true => some (some ⟨false,true,0⟩)
  | 4,false => some (some ⟨true,false,5⟩)
  | 4,true => some (some ⟨true,true,4⟩)
  | 5,false => some (some ⟨false,false,5⟩)
  | 5,true => some (some ⟨true,false,2⟩)
  | _,_ => none

def family (n : Nat) : Z0 := ⟨2,([false,true,true,true]) ++ (rep [true] (n)) ++ ([false,false,true,false,false]) ++ (rep [false,true,false,false] (n)),[]⟩

theorem entry : run0 table 35 ⟨0,[],[]⟩ = some (family 0) := by rfl

theorem phase0 (n : Nat) : run0 table 11 ⟨2,([false,true,true,true]) ++ (rep [true] (n)) ++ ([false,false,true,false,false]) ++ (rep [false,true,false,false] (n)),[]⟩ = some ⟨4,([false,false,false,false,false,true,true]) ++ (rep [true] (n)) ++ ([false,false,true,false,false]) ++ (rep [false,true,false,false] (n)),[]⟩ := by rfl

theorem local1 (L R : List Bool) : run0 table 19 ⟨4,([false,false,false,false,false,true,true]) ++ ([true]) ++ (L),(R)⟩ = some ⟨4,([false,false,false,false,false,true,true]) ++ (L),([true]) ++ (R)⟩ := by rfl

theorem phase1 (n : Nat) : run0 table (19*n) ⟨4,([false,false,false,false,false,true,true]) ++ (rep [true] (n)) ++ ([false,false,true,false,false]) ++ (rep [false,true,false,false] (n)),[]⟩ = some ⟨4,([false,false,false,false,false,true,true,false,false,true,false,false]) ++ (rep [false,true,false,false] (n)),(rep [true] (n))⟩ := by
  simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using sweepL table 4 [false,false,false,false,false,true,true] [] [true] [true] 19 local1 n (([false,false,true,false,false]) ++ (rep [false,true,false,false] (n))) ([])

theorem phase2 (n : Nat) : run0 table 34 ⟨4,([false,false,false,false,false,true,true,false,false,true,false,false]) ++ (rep [false,true,false,false] (n)),(rep [true] (n))⟩ = some ⟨4,([true,false,false,true,false,false,false,true,false,false]) ++ (rep [false,true,false,false] (n)),([true,true]) ++ (rep [true] (n))⟩ := by rfl

theorem local3 (L R : List Bool) : run0 table 1 ⟨4,([true]) ++ (L),([true,true]) ++ ([true]) ++ (R)⟩ = some ⟨4,([true]) ++ ([true]) ++ (L),([true,true]) ++ (R)⟩ := by rfl

theorem phase3 (n : Nat) : run0 table (1*n) ⟨4,([true,false,false,true,false,false,false,true,false,false]) ++ (rep [false,true,false,false] (n)),([true,true]) ++ (rep [true] (n))⟩ = some ⟨4,([true]) ++ (rep [true] (n)) ++ ([false,false,true,false,false,false,true,false,false]) ++ (rep [false,true,false,false] (n)),([true,true])⟩ := by
  simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using sweepR table 4 [true] [true,true] [true] [true] 1 local3 n (([false,false,true,false,false,false,true,false,false]) ++ (rep [false,true,false,false] (n))) ([])

theorem phase4 (n : Nat) : run0 table 8 ⟨4,([true]) ++ (rep [true] (n)) ++ ([false,false,true,false,false,false,true,false,false]) ++ (rep [false,true,false,false] (n)),([true,true])⟩ = some ⟨2,([false,true,true,true,true]) ++ (rep [true] (n)) ++ ([false,false,true,false,false,false,true,false,false]) ++ (rep [false,true,false,false] (n)),[]⟩ := by rfl

theorem finalL (n : Nat) : ([false,true,true,true,true]) ++ (rep [true] (n)) ++ ([false,false,true,false,false,false,true,false,false]) ++ (rep [false,true,false,false] (n)) = ([false,true,true,true,true]) ++ (rep [true] (n)) ++ ([false,false,true,false,false,false,true,false,false]) ++ (rep [false,true,false,false] (n)) := by
  rfl

theorem finalR (n : Nat) : ([] : List Bool) = [] := by
  rfl

theorem growth (n : Nat) : run0 table (53+20*n) (family n) = some (family (n+1)) := by
  have H := (join0 (join0 (join0 (join0 (phase0 n) (phase1 n)) (phase2 n)) (phase3 n)) (phase4 n))
  rw [show 11+19*n+34+1*n+8=53+20*n by omega] at H
  simpa only [family,rep,List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using H

theorem never (m : Machine) (hm : compatible table m) : NeverHalts m :=
  never_of_growth table family 35 (fun n => 53+20*n) entry (by intro n; omega) growth m hm

#print axioms never

end M2434

namespace M2556

-- 1RB0RE_1RC0LE_0RD1LD_1LD0RA_1LF1RF_0LB---

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
  | 4,false => some (some ⟨true,false,5⟩)
  | 4,true => some (some ⟨true,true,5⟩)
  | 5,false => some (some ⟨false,false,1⟩)
  | _,_ => none

def family (n : Nat) : Z0 := ⟨3,([false,false,true,true,false,false,true,true,false,false,true]) ++ (rep [true,false,false,true,true,false,false,true] (n)),[]⟩

theorem entry : run0 table 31 ⟨0,[],[]⟩ = some (family 0) := by rfl

theorem phase0 (n : Nat) : run0 table 8 ⟨3,([false,false,true,true,false,false,true,true,false,false,true]) ++ (rep [true,false,false,true,true,false,false,true] (n)),[]⟩ = some ⟨5,([false,true,false,false,true,true,false,false,true]) ++ (rep [true,false,false,true,true,false,false,true] (n)),([true,false,false])⟩ := by rfl

theorem local1 (L R : List Bool) : run0 table 12 ⟨5,([false,true,false,false,true,true,false,false,true]) ++ ([true,false,false,true,true,false,false,true]) ++ (L),(R)⟩ = some ⟨5,([false,true,false,false,true,true,false,false,true]) ++ (L),([false,true,false,false,false,true,false,false]) ++ (R)⟩ := by rfl

theorem phase1 (n : Nat) : run0 table (12*n) ⟨5,([false,true,false,false,true,true,false,false,true]) ++ (rep [true,false,false,true,true,false,false,true] (n)),([true,false,false])⟩ = some ⟨5,([false,true,false,false,true,true,false,false,true]),(rep [false,true,false,false,false,true,false,false] (n)) ++ ([true,false,false])⟩ := by
  simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using sweepL table 5 [false,true,false,false,true,true,false,false,true] [] [true,false,false,true,true,false,false,true] [false,true,false,false,false,true,false,false] 12 local1 n ([]) (([true,false,false]))

theorem phase2 (n : Nat) : run0 table 14 ⟨5,([false,true,false,false,true,true,false,false,true]),(rep [false,true,false,false,false,true,false,false] (n)) ++ ([true,false,false])⟩ = some ⟨2,([false,true]),([true,false,false,true,false,false,false,true,false,false]) ++ (rep [false,true,false,false,false,true,false,false] (n)) ++ ([true,false,false])⟩ := by rfl

theorem local3 (L R : List Bool) : run0 table 20 ⟨2,([false]) ++ (L),([true,false,false,true,false,false,false,true,false,false]) ++ ([false,true,false,false,false,true,false,false]) ++ (R)⟩ = some ⟨2,([false]) ++ ([true,true,false,false,true,true,false,false]) ++ (L),([true,false,false,true,false,false,false,true,false,false]) ++ (R)⟩ := by rfl

theorem phase3 (n : Nat) : run0 table (20*n) ⟨2,([false,true]),([true,false,false,true,false,false,false,true,false,false]) ++ (rep [false,true,false,false,false,true,false,false] (n)) ++ ([true,false,false])⟩ = some ⟨2,([false]) ++ (rep [true,true,false,false,true,true,false,false] (n)) ++ ([true]),([true,false,false,true,false,false,false,true,false,false,true,false,false])⟩ := by
  simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using sweepR table 2 [false] [true,false,false,true,false,false,false,true,false,false] [false,true,false,false,false,true,false,false] [true,true,false,false,true,true,false,false] 20 local3 n (([true])) (([true,false,false]))

theorem phase4 (n : Nat) : run0 table 23 ⟨2,([false]) ++ (rep [true,true,false,false,true,true,false,false] (n)) ++ ([true]),([true,false,false,true,false,false,false,true,false,false,true,false,false])⟩ = some ⟨1,([true,true,false,false,true,true,false,false,true,true,false,false]) ++ (rep [true,true,false,false,true,true,false,false] (n)) ++ ([true]),([false,false])⟩ := by rfl

theorem local5 (L R : List Bool) : run0 table 12 ⟨1,([true,true,false,false,true,true,false,false,true,true,false,false]) ++ ([true,true,false,false,true,true,false,false]) ++ (L),(R)⟩ = some ⟨1,([true,true,false,false,true,true,false,false,true,true,false,false]) ++ (L),([false,true,false,false,false,true,false,false]) ++ (R)⟩ := by rfl

theorem phase5 (n : Nat) : run0 table (12*n) ⟨1,([true,true,false,false,true,true,false,false,true,true,false,false]) ++ (rep [true,true,false,false,true,true,false,false] (n)) ++ ([true]),([false,false])⟩ = some ⟨1,([true,true,false,false,true,true,false,false,true,true,false,false,true]),(rep [false,true,false,false,false,true,false,false] (n)) ++ ([false,false])⟩ := by
  simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using sweepL table 1 [true,true,false,false,true,true,false,false,true,true,false,false] [] [true,true,false,false,true,true,false,false] [false,true,false,false,false,true,false,false] 12 local5 n (([true])) (([false,false]))

theorem phase6 (n : Nat) : run0 table 22 ⟨1,([true,true,false,false,true,true,false,false,true,true,false,false,true]),(rep [false,true,false,false,false,true,false,false] (n)) ++ ([false,false])⟩ = some ⟨2,([false,true]),([true,false,false,true,false,false,false,true,false,false,false,true,false,false]) ++ (rep [false,true,false,false,false,true,false,false] (n)) ++ ([false,false])⟩ := by rfl

theorem local7 (L R : List Bool) : run0 table 20 ⟨2,([false]) ++ (L),([true,false,false,true,false,false,false,true,false,false,false,true,false,false]) ++ ([false,true,false,false,false,true,false,false]) ++ (R)⟩ = some ⟨2,([false]) ++ ([true,true,false,false,true,true,false,false]) ++ (L),([true,false,false,true,false,false,false,true,false,false,false,true,false,false]) ++ (R)⟩ := by rfl

theorem phase7 (n : Nat) : run0 table (20*n) ⟨2,([false,true]),([true,false,false,true,false,false,false,true,false,false,false,true,false,false]) ++ (rep [false,true,false,false,false,true,false,false] (n)) ++ ([false,false])⟩ = some ⟨2,([false]) ++ (rep [true,true,false,false,true,true,false,false] (n)) ++ ([true]),([true,false,false,true,false,false,false,true,false,false,false,true,false,false,false,false])⟩ := by
  simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using sweepR table 2 [false] [true,false,false,true,false,false,false,true,false,false,false,true,false,false] [false,true,false,false,false,true,false,false] [true,true,false,false,true,true,false,false] 20 local7 n (([true])) (([false,false]))

theorem phase8 (n : Nat) : run0 table 35 ⟨2,([false]) ++ (rep [true,true,false,false,true,true,false,false] (n)) ++ ([true]),([true,false,false,true,false,false,false,true,false,false,false,true,false,false,false,false])⟩ = some ⟨3,([false,false,true,true,false,false,true,true,false,false,true,true,false,false,true,true,false,false]) ++ (rep [true,true,false,false,true,true,false,false] (n)) ++ ([true]),[]⟩ := by rfl

theorem finalL (n : Nat) : ([false,false,true,true,false,false,true,true,false,false,true,true,false,false,true,true,false,false]) ++ (rep [true,true,false,false,true,true,false,false] (n)) ++ ([true]) = ([false,false,true,true,false,false,true,true,false,false,true,true,false,false,true,true,false,false,true]) ++ (rep [true,false,false,true,true,false,false,true] (n)) := by
  calc
    _ = ([false,false,true,true,false,false,true,true,false,false,true,true,false,false,true,true,false,false,true]) ++ (rep [true,false,false,true,true,false,false,true] (n)) := by symm; simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using moveCut (([false,false,true,true,false,false,true,true,false,false,true,true,false,false,true,true,false,false])) ([]) [true,false,false,true,true,false,false] true n

theorem finalR (n : Nat) : ([] : List Bool) = [] := by
  rfl

theorem growth (n : Nat) : run0 table (102+64*n) (family n) = some (family (n+1)) := by
  have H := (join0 (join0 (join0 (join0 (join0 (join0 (join0 (join0 (phase0 n) (phase1 n)) (phase2 n)) (phase3 n)) (phase4 n)) (phase5 n)) (phase6 n)) (phase7 n)) (phase8 n))
  rw [finalL n] at H
  rw [show 8+12*n+14+20*n+23+12*n+22+20*n+35=102+64*n by omega] at H
  simpa only [family,rep,List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using H

theorem never (m : Machine) (hm : compatible table m) : NeverHalts m :=
  never_of_growth table family 31 (fun n => 102+64*n) entry (by intro n; omega) growth m hm

#print axioms never

end M2556

namespace M2578

-- 1RB0RE_1RC1LE_0RD---_1LD0RA_1LF1RF_0LB0LB

def table : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 0,true => some (some ⟨false,true,4⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 1,true => some (some ⟨true,false,4⟩)
  | 2,false => some (some ⟨false,true,3⟩)
  | 3,false => some (some ⟨true,false,3⟩)
  | 3,true => some (some ⟨false,true,0⟩)
  | 4,false => some (some ⟨true,false,5⟩)
  | 4,true => some (some ⟨true,true,5⟩)
  | 5,false => some (some ⟨false,false,1⟩)
  | 5,true => some (some ⟨false,false,1⟩)
  | _,_ => none

def family (n : Nat) : Z0 := ⟨1,[],([false,true,true,false,true,true,false]) ++ (rep [true,true,false,true,true,false] (n))⟩

theorem entry : run0 table 15 ⟨0,[],[]⟩ = some (family 0) := by rfl

theorem phase0 (n : Nat) : run0 table 1 ⟨1,[],([false,true,true,false,true,true,false]) ++ (rep [true,true,false,true,true,false] (n))⟩ = some ⟨2,([false,true]),([true,true,false,true,true,false]) ++ (rep [true,true,false,true,true,false] (n))⟩ := by rfl

theorem local1 (L R : List Bool) : run0 table 30 ⟨2,([false]) ++ (L),([true,true,false,true,true,false]) ++ ([true,true,false,true,true,false]) ++ (R)⟩ = some ⟨2,([false]) ++ ([true,true,false,true,true,false]) ++ (L),([true,true,false,true,true,false]) ++ (R)⟩ := by rfl

theorem phase1 (n : Nat) : run0 table (30*n) ⟨2,([false,true]),([true,true,false,true,true,false]) ++ (rep [true,true,false,true,true,false] (n))⟩ = some ⟨2,([false]) ++ (rep [true,true,false,true,true,false] (n)) ++ ([true]),([true,true,false,true,true,false])⟩ := by
  simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using sweepR table 2 [false] [true,true,false,true,true,false] [true,true,false,true,true,false] [true,true,false,true,true,false] 30 local1 n (([true])) ([])

theorem phase2 (n : Nat) : run0 table 38 ⟨2,([false]) ++ (rep [true,true,false,true,true,false] (n)) ++ ([true]),([true,true,false,true,true,false])⟩ = some ⟨1,([true,false,true,true,false]) ++ (rep [true,true,false,true,true,false] (n)) ++ ([true]),([false,true,true,false,true,true,false])⟩ := by rfl

theorem local3 (L R : List Bool) : run0 table 6 ⟨1,([true,false,true,true,false]) ++ ([true,true,false,true,true,false]) ++ (L),(R)⟩ = some ⟨1,([true,false,true,true,false]) ++ (L),([false,true,true,false,true,true]) ++ (R)⟩ := by rfl

theorem phase3 (n : Nat) : run0 table (6*n) ⟨1,([true,false,true,true,false]) ++ (rep [true,true,false,true,true,false] (n)) ++ ([true]),([false,true,true,false,true,true,false])⟩ = some ⟨1,([true,false,true,true,false,true]),(rep [false,true,true,false,true,true] (n)) ++ ([false,true,true,false,true,true,false])⟩ := by
  simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using sweepL table 1 [true,false,true,true,false] [] [true,true,false,true,true,false] [false,true,true,false,true,true] 6 local3 n (([true])) (([false,true,true,false,true,true,false]))

theorem phase4 (n : Nat) : run0 table 6 ⟨1,([true,false,true,true,false,true]),(rep [false,true,true,false,true,true] (n)) ++ ([false,true,true,false,true,true,false])⟩ = some ⟨1,[],([false,true,true,false,true,true]) ++ (rep [false,true,true,false,true,true] (n)) ++ ([false,true,true,false,true,true,false])⟩ := by rfl

theorem finalL (n : Nat) : ([] : List Bool) = [] := by
  rfl

theorem finalR (n : Nat) : ([false,true,true,false,true,true]) ++ (rep [false,true,true,false,true,true] (n)) ++ ([false,true,true,false,true,true,false]) = ([false,true,true,false,true,true,false,true,true,false,true,true,false]) ++ (rep [true,true,false,true,true,false] (n)) := by
  calc
    _ = ([false,true,true,false,true,true,false]) ++ (rep [true,true,false,true,true,false] (n)) ++ ([true,true,false,true,true,false]) := by symm; simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using moveCut (([false,true,true,false,true,true])) (([true,true,false,true,true,false])) [true,true,false,true,true] false n
    _ = ([false,true,true,false,true,true,false,true]) ++ (rep [true,false,true,true,false,true] (n)) ++ ([true,false,true,true,false]) := by symm; simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using moveCut (([false,true,true,false,true,true,false])) (([true,false,true,true,false])) [true,false,true,true,false] true n
    _ = ([false,true,true,false,true,true,false,true,true]) ++ (rep [false,true,true,false,true,true] (n)) ++ ([false,true,true,false]) := by symm; simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using moveCut (([false,true,true,false,true,true,false,true])) (([false,true,true,false])) [false,true,true,false,true] true n
    _ = ([false,true,true,false,true,true,false,true,true,false]) ++ (rep [true,true,false,true,true,false] (n)) ++ ([true,true,false]) := by symm; simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using moveCut (([false,true,true,false,true,true,false,true,true])) (([true,true,false])) [true,true,false,true,true] false n
    _ = ([false,true,true,false,true,true,false,true,true,false,true]) ++ (rep [true,false,true,true,false,true] (n)) ++ ([true,false]) := by symm; simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using moveCut (([false,true,true,false,true,true,false,true,true,false])) (([true,false])) [true,false,true,true,false] true n
    _ = ([false,true,true,false,true,true,false,true,true,false,true,true]) ++ (rep [false,true,true,false,true,true] (n)) ++ ([false]) := by symm; simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using moveCut (([false,true,true,false,true,true,false,true,true,false,true])) (([false])) [false,true,true,false,true] true n
    _ = ([false,true,true,false,true,true,false,true,true,false,true,true,false]) ++ (rep [true,true,false,true,true,false] (n)) := by symm; simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using moveCut (([false,true,true,false,true,true,false,true,true,false,true,true])) ([]) [true,true,false,true,true] false n

theorem growth (n : Nat) : run0 table (45+36*n) (family n) = some (family (n+1)) := by
  have H := (join0 (join0 (join0 (join0 (phase0 n) (phase1 n)) (phase2 n)) (phase3 n)) (phase4 n))
  rw [finalR n] at H
  rw [show 1+30*n+38+6*n+6=45+36*n by omega] at H
  simpa only [family,rep,List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using H

theorem never (m : Machine) (hm : compatible table m) : NeverHalts m :=
  never_of_growth table family 15 (fun n => 45+36*n) entry (by intro n; omega) growth m hm

#print axioms never

end M2578

namespace M2579

-- 1RB0RE_1RC1LE_0RD---_1LD0RA_1LF1RF_0LB0LE

def table : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 0,true => some (some ⟨false,true,4⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 1,true => some (some ⟨true,false,4⟩)
  | 2,false => some (some ⟨false,true,3⟩)
  | 3,false => some (some ⟨true,false,3⟩)
  | 3,true => some (some ⟨false,true,0⟩)
  | 4,false => some (some ⟨true,false,5⟩)
  | 4,true => some (some ⟨true,true,5⟩)
  | 5,false => some (some ⟨false,false,1⟩)
  | 5,true => some (some ⟨false,false,4⟩)
  | _,_ => none

def family (n : Nat) : Z0 := ⟨0,([false,false,false,true,false,true]) ++ (rep [true,false,true,true,false,true,true,false,true] (n)) ++ (rep [false,true] (n)) ++ ([true,false,true]),[]⟩

theorem entry : run0 table 39 ⟨0,[],[]⟩ = some (family 0) := by rfl

theorem phase0 (n : Nat) : run0 table 14 ⟨0,([false,false,false,true,false,true]) ++ (rep [true,false,true,true,false,true,true,false,true] (n)) ++ (rep [false,true] (n)) ++ ([true,false,true]),[]⟩ = some ⟨5,([false,true,false,true]) ++ (rep [true,false,true,true,false,true,true,false,true] (n)) ++ (rep [false,true] (n)) ++ ([true,false,true]),([true,true,false,true,true,false])⟩ := by rfl

theorem local1 (L R : List Bool) : run0 table 15 ⟨5,([false,true,false,true]) ++ ([true,false,true,true,false,true,true,false,true]) ++ (L),(R)⟩ = some ⟨5,([false,true,false,true]) ++ (L),([true,true,false,true,true,false,true,true,false]) ++ (R)⟩ := by rfl

theorem phase1 (n : Nat) : run0 table (15*n) ⟨5,([false,true,false,true]) ++ (rep [true,false,true,true,false,true,true,false,true] (n)) ++ (rep [false,true] (n)) ++ ([true,false,true]),([true,true,false,true,true,false])⟩ = some ⟨5,([false,true,false,true]) ++ (rep [false,true] (n)) ++ ([true,false,true]),(rep [true,true,false,true,true,false,true,true,false] (n)) ++ ([true,true,false,true,true,false])⟩ := by
  simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using sweepL table 5 [false,true,false,true] [] [true,false,true,true,false,true,true,false,true] [true,true,false,true,true,false,true,true,false] 15 local1 n ((rep [false,true] (n)) ++ ([true,false,true])) (([true,true,false,true,true,false]))

theorem phase2 (n : Nat) : run0 table 2 ⟨5,([false,true,false,true]) ++ (rep [false,true] (n)) ++ ([true,false,true]),(rep [true,true,false,true,true,false,true,true,false] (n)) ++ ([true,true,false,true,true,false])⟩ = some ⟨4,([false,true]) ++ (rep [false,true] (n)) ++ ([true,false,true]),([true,false]) ++ (rep [true,true,false,true,true,false,true,true,false] (n)) ++ ([true,true,false,true,true,false])⟩ := by rfl

theorem local3 (L R : List Bool) : run0 table 2 ⟨4,([false,true]) ++ ([false,true]) ++ (L),(R)⟩ = some ⟨4,([false,true]) ++ (L),([false,true]) ++ (R)⟩ := by rfl

theorem phase3 (n : Nat) : run0 table (2*n) ⟨4,([false,true]) ++ (rep [false,true] (n)) ++ ([true,false,true]),([true,false]) ++ (rep [true,true,false,true,true,false,true,true,false] (n)) ++ ([true,true,false,true,true,false])⟩ = some ⟨4,([false,true,true,false,true]),(rep [false,true] (n)) ++ ([true,false]) ++ (rep [true,true,false,true,true,false,true,true,false] (n)) ++ ([true,true,false,true,true,false])⟩ := by
  simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using sweepL table 4 [false,true] [] [false,true] [false,true] 2 local3 n (([true,false,true])) (([true,false]) ++ (rep [true,true,false,true,true,false,true,true,false] (n)) ++ ([true,true,false,true,true,false]))

theorem phase4 (n : Nat) : run0 table 37 ⟨4,([false,true,true,false,true]),(rep [false,true] (n)) ++ ([true,false]) ++ (rep [true,true,false,true,true,false,true,true,false] (n)) ++ ([true,true,false,true,true,false])⟩ = some ⟨4,([false,false,false,true,false,true]),([true,false,true,false,true]) ++ (rep [false,true] (n)) ++ ([true,false]) ++ (rep [true,true,false,true,true,false,true,true,false] (n)) ++ ([true,true,false,true,true,false])⟩ := by rfl

theorem local5 (L R : List Bool) : run0 table 6 ⟨4,([false,false,false]) ++ (L),([true,false,true,false,true]) ++ ([false,true]) ++ (R)⟩ = some ⟨4,([false,false,false]) ++ ([false,true]) ++ (L),([true,false,true,false,true]) ++ (R)⟩ := by rfl

theorem phase5 (n : Nat) : run0 table (6*n) ⟨4,([false,false,false,true,false,true]),([true,false,true,false,true]) ++ (rep [false,true] (n)) ++ ([true,false]) ++ (rep [true,true,false,true,true,false,true,true,false] (n)) ++ ([true,true,false,true,true,false])⟩ = some ⟨4,([false,false,false]) ++ (rep [false,true] (n)) ++ ([true,false,true]),([true,false,true,false,true,true,false]) ++ (rep [true,true,false,true,true,false,true,true,false] (n)) ++ ([true,true,false,true,true,false])⟩ := by
  simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using sweepR table 4 [false,false,false] [true,false,true,false,true] [false,true] [false,true] 6 local5 n (([true,false,true])) (([true,false]) ++ (rep [true,true,false,true,true,false,true,true,false] (n)) ++ ([true,true,false,true,true,false]))

theorem phase6 (n : Nat) : run0 table 6 ⟨4,([false,false,false]) ++ (rep [false,true] (n)) ++ ([true,false,true]),([true,false,true,false,true,true,false]) ++ (rep [true,true,false,true,true,false,true,true,false] (n)) ++ ([true,true,false,true,true,false])⟩ = some ⟨4,([false,false,false,false,true]) ++ (rep [false,true] (n)) ++ ([true,false,true]),([true,false,true,true,false]) ++ (rep [true,true,false,true,true,false,true,true,false] (n)) ++ ([true,true,false,true,true,false])⟩ := by rfl

theorem local7 (L R : List Bool) : run0 table 45 ⟨4,([false,false,false]) ++ (L),([true,false,true,true,false]) ++ ([true,true,false,true,true,false,true,true,false]) ++ (R)⟩ = some ⟨4,([false,false,false]) ++ ([true,false,true,true,false,true,true,false,true]) ++ (L),([true,false,true,true,false]) ++ (R)⟩ := by rfl

theorem phase7 (n : Nat) : run0 table (45*n) ⟨4,([false,false,false,false,true]) ++ (rep [false,true] (n)) ++ ([true,false,true]),([true,false,true,true,false]) ++ (rep [true,true,false,true,true,false,true,true,false] (n)) ++ ([true,true,false,true,true,false])⟩ = some ⟨4,([false,false,false]) ++ (rep [true,false,true,true,false,true,true,false,true] (n)) ++ ([false,true]) ++ (rep [false,true] (n)) ++ ([true,false,true]),([true,false,true,true,false,true,true,false,true,true,false])⟩ := by
  simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using sweepR table 4 [false,false,false] [true,false,true,true,false] [true,true,false,true,true,false,true,true,false] [true,false,true,true,false,true,true,false,true] 45 local7 n (([false,true]) ++ (rep [false,true] (n)) ++ ([true,false,true])) (([true,true,false,true,true,false]))

theorem phase8 (n : Nat) : run0 table 56 ⟨4,([false,false,false]) ++ (rep [true,false,true,true,false,true,true,false,true] (n)) ++ ([false,true]) ++ (rep [false,true] (n)) ++ ([true,false,true]),([true,false,true,true,false,true,true,false,true,true,false])⟩ = some ⟨0,([false,false,false,true,false,true,true,false,true,true,false,true,true,false,true]) ++ (rep [true,false,true,true,false,true,true,false,true] (n)) ++ ([false,true]) ++ (rep [false,true] (n)) ++ ([true,false,true]),[]⟩ := by rfl

theorem finalL (n : Nat) : ([false,false,false,true,false,true,true,false,true,true,false,true,true,false,true]) ++ (rep [true,false,true,true,false,true,true,false,true] (n)) ++ ([false,true]) ++ (rep [false,true] (n)) ++ ([true,false,true]) = ([false,false,false,true,false,true,true,false,true,true,false,true,true,false,true]) ++ (rep [true,false,true,true,false,true,true,false,true] (n)) ++ ([false,true]) ++ (rep [false,true] (n)) ++ ([true,false,true]) := by
  rfl

theorem finalR (n : Nat) : ([] : List Bool) = [] := by
  rfl

theorem growth (n : Nat) : run0 table (115+68*n) (family n) = some (family (n+1)) := by
  have H := (join0 (join0 (join0 (join0 (join0 (join0 (join0 (join0 (phase0 n) (phase1 n)) (phase2 n)) (phase3 n)) (phase4 n)) (phase5 n)) (phase6 n)) (phase7 n)) (phase8 n))
  rw [show 14+15*n+2+2*n+37+6*n+6+45*n+56=115+68*n by omega] at H
  simpa only [family,rep,List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using H

theorem never (m : Machine) (hm : compatible table m) : NeverHalts m :=
  never_of_growth table family 39 (fun n => 115+68*n) entry (by intro n; omega) growth m hm

#print axioms never

end M2579

namespace M2687

-- 1RB0RE_1RC0LF_0RD1LA_1LD0RA_---1RF_1LC0LF

def table : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 0,true => some (some ⟨false,true,4⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 1,true => some (some ⟨false,false,5⟩)
  | 2,false => some (some ⟨false,true,3⟩)
  | 2,true => some (some ⟨true,false,0⟩)
  | 3,false => some (some ⟨true,false,3⟩)
  | 3,true => some (some ⟨false,true,0⟩)
  | 4,true => some (some ⟨true,true,5⟩)
  | 5,false => some (some ⟨true,false,2⟩)
  | 5,true => some (some ⟨false,false,5⟩)
  | _,_ => none

def family (n : Nat) : Z0 := ⟨2,([false,true,true,false,false,true]) ++ (rep [false,false,true,false,false,true] (n)) ++ ([true,false,false]),[]⟩

theorem entry : run0 table 47 ⟨0,[],[]⟩ = some (family 0) := by rfl

theorem phase0 (n : Nat) : run0 table 6 ⟨2,([false,true,true,false,false,true]) ++ (rep [false,false,true,false,false,true] (n)) ++ ([true,false,false]),[]⟩ = some ⟨5,([false,true,false,false,true,false,false,true]) ++ (rep [false,false,true,false,false,true] (n)) ++ ([true,false,false]),[]⟩ := by rfl

theorem local1 (L R : List Bool) : run0 table 10 ⟨5,([false,true,false,false,true,false,false,true]) ++ ([false,false,true,false,false,true]) ++ (L),(R)⟩ = some ⟨5,([false,true,false,false,true,false,false,true]) ++ (L),([false,false,true,false,false,true]) ++ (R)⟩ := by rfl

theorem phase1 (n : Nat) : run0 table (10*n) ⟨5,([false,true,false,false,true,false,false,true]) ++ (rep [false,false,true,false,false,true] (n)) ++ ([true,false,false]),[]⟩ = some ⟨5,([false,true,false,false,true,false,false,true,true,false,false]),(rep [false,false,true,false,false,true] (n))⟩ := by
  simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using sweepL table 5 [false,true,false,false,true,false,false,true] [] [false,false,true,false,false,true] [false,false,true,false,false,true] 10 local1 n (([true,false,false])) ([])

theorem phase2 (n : Nat) : run0 table 12 ⟨5,([false,true,false,false,true,false,false,true,true,false,false]),(rep [false,false,true,false,false,true] (n))⟩ = some ⟨0,([true,false,false]),([true,true,false,false,true,false,false,true]) ++ (rep [false,false,true,false,false,true] (n))⟩ := by rfl

theorem local3 (L R : List Bool) : run0 table 26 ⟨0,([true,false]) ++ (L),([true,true,false,false,true,false,false,true]) ++ ([false,false,true,false,false,true]) ++ (R)⟩ = some ⟨0,([true,false]) ++ ([true,false,false,true,false,false]) ++ (L),([true,true,false,false,true,false,false,true]) ++ (R)⟩ := by rfl

theorem phase3 (n : Nat) : run0 table (26*n) ⟨0,([true,false,false]),([true,true,false,false,true,false,false,true]) ++ (rep [false,false,true,false,false,true] (n))⟩ = some ⟨0,([true,false]) ++ (rep [true,false,false,true,false,false] (n)) ++ ([false]),([true,true,false,false,true,false,false,true])⟩ := by
  simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using sweepR table 0 [true,false] [true,true,false,false,true,false,false,true] [false,false,true,false,false,true] [true,false,false,true,false,false] 26 local3 n (([false])) ([])

theorem phase4 (n : Nat) : run0 table 41 ⟨0,([true,false]) ++ (rep [true,false,false,true,false,false] (n)) ++ ([false]),([true,true,false,false,true,false,false,true])⟩ = some ⟨5,([false,true,false,false,true,false,false,true,false,false,true,false,false]) ++ (rep [true,false,false,true,false,false] (n)) ++ ([false]),[]⟩ := by rfl

theorem local5 (L R : List Bool) : run0 table 10 ⟨5,([false,true,false,false,true,false,false,true,false,false,true,false,false]) ++ ([true,false,false,true,false,false]) ++ (L),(R)⟩ = some ⟨5,([false,true,false,false,true,false,false,true,false,false,true,false,false]) ++ (L),([false,false,true,false,false,true]) ++ (R)⟩ := by rfl

theorem phase5 (n : Nat) : run0 table (10*n) ⟨5,([false,true,false,false,true,false,false,true,false,false,true,false,false]) ++ (rep [true,false,false,true,false,false] (n)) ++ ([false]),[]⟩ = some ⟨5,([false,true,false,false,true,false,false,true,false,false,true,false,false,false]),(rep [false,false,true,false,false,true] (n))⟩ := by
  simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using sweepL table 5 [false,true,false,false,true,false,false,true,false,false,true,false,false] [] [true,false,false,true,false,false] [false,false,true,false,false,true] 10 local5 n (([false])) ([])

theorem phase6 (n : Nat) : run0 table 43 ⟨5,([false,true,false,false,true,false,false,true,false,false,true,false,false,false]),(rep [false,false,true,false,false,true] (n))⟩ = some ⟨5,([true,false,false,true,true,false,false]),([false,false,false,true,false,false,true]) ++ (rep [false,false,true,false,false,true] (n))⟩ := by rfl

theorem local7 (L R : List Bool) : run0 table 26 ⟨5,([true,false,false]) ++ (L),([false,false,false,true,false,false,true]) ++ ([false,false,true,false,false,true]) ++ (R)⟩ = some ⟨5,([true,false,false]) ++ ([true,false,false,true,false,false]) ++ (L),([false,false,false,true,false,false,true]) ++ (R)⟩ := by rfl

theorem phase7 (n : Nat) : run0 table (26*n) ⟨5,([true,false,false,true,true,false,false]),([false,false,false,true,false,false,true]) ++ (rep [false,false,true,false,false,true] (n))⟩ = some ⟨5,([true,false,false]) ++ (rep [true,false,false,true,false,false] (n)) ++ ([true,true,false,false]),([false,false,false,true,false,false,true])⟩ := by
  simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using sweepR table 5 [true,false,false] [false,false,false,true,false,false,true] [false,false,true,false,false,true] [true,false,false,true,false,false] 26 local7 n (([true,true,false,false])) ([])

theorem phase8 (n : Nat) : run0 table 32 ⟨5,([true,false,false]) ++ (rep [true,false,false,true,false,false] (n)) ++ ([true,true,false,false]),([false,false,false,true,false,false,true])⟩ = some ⟨2,([false,true,true,false,false,true,false,false,true,false,false]) ++ (rep [true,false,false,true,false,false] (n)) ++ ([true,true,false,false]),[]⟩ := by rfl

theorem finalL (n : Nat) : ([false,true,true,false,false,true,false,false,true,false,false]) ++ (rep [true,false,false,true,false,false] (n)) ++ ([true,true,false,false]) = ([false,true,true,false,false,true,false,false,true,false,false,true]) ++ (rep [false,false,true,false,false,true] (n)) ++ ([true,false,false]) := by
  calc
    _ = ([false,true,true,false,false,true,false,false,true,false,false,true]) ++ (rep [false,false,true,false,false,true] (n)) ++ ([true,false,false]) := by symm; simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using moveCut (([false,true,true,false,false,true,false,false,true,false,false])) (([true,false,false])) [false,false,true,false,false] true n

theorem finalR (n : Nat) : ([] : List Bool) = [] := by
  rfl

theorem growth (n : Nat) : run0 table (134+72*n) (family n) = some (family (n+1)) := by
  have H := (join0 (join0 (join0 (join0 (join0 (join0 (join0 (join0 (phase0 n) (phase1 n)) (phase2 n)) (phase3 n)) (phase4 n)) (phase5 n)) (phase6 n)) (phase7 n)) (phase8 n))
  rw [finalL n] at H
  rw [show 6+10*n+12+26*n+41+10*n+43+26*n+32=134+72*n by omega] at H
  simpa only [family,rep,List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using H

theorem never (m : Machine) (hm : compatible table m) : NeverHalts m :=
  never_of_growth table family 47 (fun n => 134+72*n) entry (by intro n; omega) growth m hm

#print axioms never

end M2687

namespace M2688

-- 1RB0RE_1RC1LE_0RD1LA_1LD0RA_---1RF_1LC0LF

def table : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 0,true => some (some ⟨false,true,4⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 1,true => some (some ⟨true,false,4⟩)
  | 2,false => some (some ⟨false,true,3⟩)
  | 2,true => some (some ⟨true,false,0⟩)
  | 3,false => some (some ⟨true,false,3⟩)
  | 3,true => some (some ⟨false,true,0⟩)
  | 4,true => some (some ⟨true,true,5⟩)
  | 5,false => some (some ⟨true,false,2⟩)
  | 5,true => some (some ⟨false,false,5⟩)
  | _,_ => none

def family (n : Nat) : Z0 := ⟨2,([false,true,true,false,false,true]) ++ (rep [false,false,true,false,false,true] (n)) ++ ([true,false,false]),[]⟩

theorem entry : run0 table 55 ⟨0,[],[]⟩ = some (family 0) := by rfl

theorem phase0 (n : Nat) : run0 table 6 ⟨2,([false,true,true,false,false,true]) ++ (rep [false,false,true,false,false,true] (n)) ++ ([true,false,false]),[]⟩ = some ⟨5,([false,true,false,false,true,false,false,true]) ++ (rep [false,false,true,false,false,true] (n)) ++ ([true,false,false]),[]⟩ := by rfl

theorem local1 (L R : List Bool) : run0 table 14 ⟨5,([false,true,false,false,true,false,false,true]) ++ ([false,false,true,false,false,true]) ++ (L),(R)⟩ = some ⟨5,([false,true,false,false,true,false,false,true]) ++ (L),([false,false,true,false,false,true]) ++ (R)⟩ := by rfl

theorem phase1 (n : Nat) : run0 table (14*n) ⟨5,([false,true,false,false,true,false,false,true]) ++ (rep [false,false,true,false,false,true] (n)) ++ ([true,false,false]),[]⟩ = some ⟨5,([false,true,false,false,true,false,false,true,true,false,false]),(rep [false,false,true,false,false,true] (n))⟩ := by
  simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using sweepL table 5 [false,true,false,false,true,false,false,true] [] [false,false,true,false,false,true] [false,false,true,false,false,true] 14 local1 n (([true,false,false])) ([])

theorem phase2 (n : Nat) : run0 table 16 ⟨5,([false,true,false,false,true,false,false,true,true,false,false]),(rep [false,false,true,false,false,true] (n))⟩ = some ⟨0,([true,false,false]),([true,true,false,false,true,false,false,true]) ++ (rep [false,false,true,false,false,true] (n))⟩ := by rfl

theorem local3 (L R : List Bool) : run0 table 26 ⟨0,([true,false]) ++ (L),([true,true,false,false,true,false,false,true]) ++ ([false,false,true,false,false,true]) ++ (R)⟩ = some ⟨0,([true,false]) ++ ([true,false,false,true,false,false]) ++ (L),([true,true,false,false,true,false,false,true]) ++ (R)⟩ := by rfl

theorem phase3 (n : Nat) : run0 table (26*n) ⟨0,([true,false,false]),([true,true,false,false,true,false,false,true]) ++ (rep [false,false,true,false,false,true] (n))⟩ = some ⟨0,([true,false]) ++ (rep [true,false,false,true,false,false] (n)) ++ ([false]),([true,true,false,false,true,false,false,true])⟩ := by
  simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using sweepR table 0 [true,false] [true,true,false,false,true,false,false,true] [false,false,true,false,false,true] [true,false,false,true,false,false] 26 local3 n (([false])) ([])

theorem phase4 (n : Nat) : run0 table 41 ⟨0,([true,false]) ++ (rep [true,false,false,true,false,false] (n)) ++ ([false]),([true,true,false,false,true,false,false,true])⟩ = some ⟨5,([false,true,false,false,true,false,false,true,false,false,true,false,false]) ++ (rep [true,false,false,true,false,false] (n)) ++ ([false]),[]⟩ := by rfl

theorem local5 (L R : List Bool) : run0 table 14 ⟨5,([false,true,false,false,true,false,false,true,false,false,true,false,false]) ++ ([true,false,false,true,false,false]) ++ (L),(R)⟩ = some ⟨5,([false,true,false,false,true,false,false,true,false,false,true,false,false]) ++ (L),([false,false,true,false,false,true]) ++ (R)⟩ := by rfl

theorem phase5 (n : Nat) : run0 table (14*n) ⟨5,([false,true,false,false,true,false,false,true,false,false,true,false,false]) ++ (rep [true,false,false,true,false,false] (n)) ++ ([false]),[]⟩ = some ⟨5,([false,true,false,false,true,false,false,true,false,false,true,false,false,false]),(rep [false,false,true,false,false,true] (n))⟩ := by
  simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using sweepL table 5 [false,true,false,false,true,false,false,true,false,false,true,false,false] [] [true,false,false,true,false,false] [false,false,true,false,false,true] 14 local5 n (([false])) ([])

theorem phase6 (n : Nat) : run0 table 53 ⟨5,([false,true,false,false,true,false,false,true,false,false,true,false,false,false]),(rep [false,false,true,false,false,true] (n))⟩ = some ⟨4,([true,false,false,true,true,false,false]),([true,false,false,true,false,false,true]) ++ (rep [false,false,true,false,false,true] (n))⟩ := by rfl

theorem local7 (L R : List Bool) : run0 table 26 ⟨4,([true,false,false]) ++ (L),([true,false,false,true,false,false,true]) ++ ([false,false,true,false,false,true]) ++ (R)⟩ = some ⟨4,([true,false,false]) ++ ([true,false,false,true,false,false]) ++ (L),([true,false,false,true,false,false,true]) ++ (R)⟩ := by rfl

theorem phase7 (n : Nat) : run0 table (26*n) ⟨4,([true,false,false,true,true,false,false]),([true,false,false,true,false,false,true]) ++ (rep [false,false,true,false,false,true] (n))⟩ = some ⟨4,([true,false,false]) ++ (rep [true,false,false,true,false,false] (n)) ++ ([true,true,false,false]),([true,false,false,true,false,false,true])⟩ := by
  simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using sweepR table 4 [true,false,false] [true,false,false,true,false,false,true] [false,false,true,false,false,true] [true,false,false,true,false,false] 26 local7 n (([true,true,false,false])) ([])

theorem phase8 (n : Nat) : run0 table 34 ⟨4,([true,false,false]) ++ (rep [true,false,false,true,false,false] (n)) ++ ([true,true,false,false]),([true,false,false,true,false,false,true])⟩ = some ⟨2,([false,true,true,false,false,true,false,false,true,false,false]) ++ (rep [true,false,false,true,false,false] (n)) ++ ([true,true,false,false]),[]⟩ := by rfl

theorem finalL (n : Nat) : ([false,true,true,false,false,true,false,false,true,false,false]) ++ (rep [true,false,false,true,false,false] (n)) ++ ([true,true,false,false]) = ([false,true,true,false,false,true,false,false,true,false,false,true]) ++ (rep [false,false,true,false,false,true] (n)) ++ ([true,false,false]) := by
  calc
    _ = ([false,true,true,false,false,true,false,false,true,false,false,true]) ++ (rep [false,false,true,false,false,true] (n)) ++ ([true,false,false]) := by symm; simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using moveCut (([false,true,true,false,false,true,false,false,true,false,false])) (([true,false,false])) [false,false,true,false,false] true n

theorem finalR (n : Nat) : ([] : List Bool) = [] := by
  rfl

theorem growth (n : Nat) : run0 table (150+80*n) (family n) = some (family (n+1)) := by
  have H := (join0 (join0 (join0 (join0 (join0 (join0 (join0 (join0 (phase0 n) (phase1 n)) (phase2 n)) (phase3 n)) (phase4 n)) (phase5 n)) (phase6 n)) (phase7 n)) (phase8 n))
  rw [finalL n] at H
  rw [show 6+14*n+16+26*n+41+14*n+53+26*n+34=150+80*n by omega] at H
  simpa only [family,rep,List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using H

theorem never (m : Machine) (hm : compatible table m) : NeverHalts m :=
  never_of_growth table family 55 (fun n => 150+80*n) entry (by intro n; omega) growth m hm

#print axioms never

end M2688

end BB6.Agent11Raw39B0REPumps
