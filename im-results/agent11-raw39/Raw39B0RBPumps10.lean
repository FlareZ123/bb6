import SweepPumping
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedVariables false
namespace BB6.Agent11Raw39B0RBPumps
open BB6Coverage BB6Coverage.Agent31Pump


namespace M1980

-- 1RB0RB_1RC1RE_0RD---_1LD0RA_1LF0RA_0LD1LE

def table : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 0,true => some (some ⟨false,true,1⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 1,true => some (some ⟨true,true,4⟩)
  | 2,false => some (some ⟨false,true,3⟩)
  | 3,false => some (some ⟨true,false,3⟩)
  | 3,true => some (some ⟨false,true,0⟩)
  | 4,false => some (some ⟨true,false,5⟩)
  | 4,true => some (some ⟨false,true,0⟩)
  | 5,false => some (some ⟨false,false,3⟩)
  | 5,true => some (some ⟨true,false,4⟩)
  | _,_ => none

def family (n : Nat) : Z0 := ⟨1,([false]) ++ (rep [false,false,true] (n)) ++ ([true]) ++ (rep [false] (n)),[]⟩

theorem entry : run0 table 1 ⟨0,[],[]⟩ = some (family 0) := by rfl

theorem phase0 (n : Nat) : run0 table 7 ⟨1,([false]) ++ (rep [false,false,true] (n)) ++ ([true]) ++ (rep [false] (n)),[]⟩ = some ⟨4,([false,true,false,false]) ++ (rep [false,false,true] (n)) ++ ([true]) ++ (rep [false] (n)),[]⟩ := by rfl

theorem local1 (L R : List Bool) : run0 table 9 ⟨4,([false,true,false,false]) ++ ([false,false,true]) ++ (L),(R)⟩ = some ⟨4,([false,true,false,false]) ++ (L),([true,true,true]) ++ (R)⟩ := by rfl

theorem phase1 (n : Nat) : run0 table (9*n) ⟨4,([false,true,false,false]) ++ (rep [false,false,true] (n)) ++ ([true]) ++ (rep [false] (n)),[]⟩ = some ⟨4,([false,true,false,false,true]) ++ (rep [false] (n)),(rep [true,true,true] (n))⟩ := by
  simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using sweepL table 4 [false,true,false,false] [] [false,false,true] [true,true,true] 9 local1 n (([true]) ++ (rep [false] (n))) ([])

theorem phase2 (n : Nat) : run0 table 6 ⟨4,([false,true,false,false,true]) ++ (rep [false] (n)),(rep [true,true,true] (n))⟩ = some ⟨1,([true,true,false]) ++ (rep [false] (n)),([true,true]) ++ (rep [true,true,true] (n))⟩ := by rfl

theorem local3 (L R : List Bool) : run0 table 3 ⟨1,([true]) ++ (L),([true,true]) ++ ([true,true,true]) ++ (R)⟩ = some ⟨1,([true]) ++ ([false,false,true]) ++ (L),([true,true]) ++ (R)⟩ := by rfl

theorem phase3 (n : Nat) : run0 table (3*n) ⟨1,([true,true,false]) ++ (rep [false] (n)),([true,true]) ++ (rep [true,true,true] (n))⟩ = some ⟨1,([true]) ++ (rep [false,false,true] (n)) ++ ([true,false]) ++ (rep [false] (n)),([true,true])⟩ := by
  simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using sweepR table 1 [true] [true,true] [true,true,true] [false,false,true] 3 local3 n (([true,false]) ++ (rep [false] (n))) ([])

theorem phase4 (n : Nat) : run0 table 3 ⟨1,([true]) ++ (rep [false,false,true] (n)) ++ ([true,false]) ++ (rep [false] (n)),([true,true])⟩ = some ⟨1,([false,false,false,true]) ++ (rep [false,false,true] (n)) ++ ([true,false]) ++ (rep [false] (n)),[]⟩ := by rfl

theorem finalL (n : Nat) : ([false,false,false,true]) ++ (rep [false,false,true] (n)) ++ ([true,false]) ++ (rep [false] (n)) = ([false,false,false,true]) ++ (rep [false,false,true] (n)) ++ ([true,false]) ++ (rep [false] (n)) := by
  rfl

theorem finalR (n : Nat) : ([] : List Bool) = [] := by
  rfl

theorem growth (n : Nat) : run0 table (16+12*n) (family n) = some (family (n+1)) := by
  have H := (join0 (join0 (join0 (join0 (phase0 n) (phase1 n)) (phase2 n)) (phase3 n)) (phase4 n))
  rw [show 7+9*n+6+3*n+3=16+12*n by omega] at H
  simpa only [family,rep,List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using H

theorem never (m : Machine) (hm : compatible table m) : NeverHalts m :=
  never_of_growth table family 1 (fun n => 16+12*n) entry (by intro n; omega) growth m hm

#print axioms never

end M1980

namespace M2039

-- 1RB0RB_1RC1RF_0RD1RD_1LD0RA_0LD1LF_0LE---

def table : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 0,true => some (some ⟨false,true,1⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 1,true => some (some ⟨true,true,5⟩)
  | 2,false => some (some ⟨false,true,3⟩)
  | 2,true => some (some ⟨true,true,3⟩)
  | 3,false => some (some ⟨true,false,3⟩)
  | 3,true => some (some ⟨false,true,0⟩)
  | 4,false => some (some ⟨false,false,3⟩)
  | 4,true => some (some ⟨true,false,5⟩)
  | 5,false => some (some ⟨false,false,4⟩)
  | _,_ => none

def family (n : Nat) : Z0 := ⟨1,([false]) ++ (rep [false,false,true] (n)) ++ ([true]) ++ (rep [false] (n)),[]⟩

theorem entry : run0 table 1 ⟨0,[],[]⟩ = some (family 0) := by rfl

theorem phase0 (n : Nat) : run0 table 7 ⟨1,([false]) ++ (rep [false,false,true] (n)) ++ ([true]) ++ (rep [false] (n)),[]⟩ = some ⟨5,([false,true,false,false]) ++ (rep [false,false,true] (n)) ++ ([true]) ++ (rep [false] (n)),[]⟩ := by rfl

theorem local1 (L R : List Bool) : run0 table 9 ⟨5,([false,true,false,false]) ++ ([false,false,true]) ++ (L),(R)⟩ = some ⟨5,([false,true,false,false]) ++ (L),([false,true,false]) ++ (R)⟩ := by rfl

theorem phase1 (n : Nat) : run0 table (9*n) ⟨5,([false,true,false,false]) ++ (rep [false,false,true] (n)) ++ ([true]) ++ (rep [false] (n)),[]⟩ = some ⟨5,([false,true,false,false,true]) ++ (rep [false] (n)),(rep [false,true,false] (n))⟩ := by
  simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using sweepL table 5 [false,true,false,false] [] [false,false,true] [false,true,false] 9 local1 n (([true]) ++ (rep [false] (n))) ([])

theorem phase2 (n : Nat) : run0 table 6 ⟨5,([false,true,false,false,true]) ++ (rep [false] (n)),(rep [false,true,false] (n))⟩ = some ⟨1,([false,true,false]) ++ (rep [false] (n)),([true,false]) ++ (rep [false,true,false] (n))⟩ := by rfl

theorem local3 (L R : List Bool) : run0 table 5 ⟨1,([false]) ++ (L),([true,false]) ++ ([false,true,false]) ++ (R)⟩ = some ⟨1,([false]) ++ ([false,false,true]) ++ (L),([true,false]) ++ (R)⟩ := by rfl

theorem phase3 (n : Nat) : run0 table (5*n) ⟨1,([false,true,false]) ++ (rep [false] (n)),([true,false]) ++ (rep [false,true,false] (n))⟩ = some ⟨1,([false]) ++ (rep [false,false,true] (n)) ++ ([true,false]) ++ (rep [false] (n)),([true,false])⟩ := by
  simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using sweepR table 1 [false] [true,false] [false,true,false] [false,false,true] 5 local3 n (([true,false]) ++ (rep [false] (n))) ([])

theorem phase4 (n : Nat) : run0 table 5 ⟨1,([false]) ++ (rep [false,false,true] (n)) ++ ([true,false]) ++ (rep [false] (n)),([true,false])⟩ = some ⟨1,([false,false,false,true]) ++ (rep [false,false,true] (n)) ++ ([true,false]) ++ (rep [false] (n)),[]⟩ := by rfl

theorem finalL (n : Nat) : ([false,false,false,true]) ++ (rep [false,false,true] (n)) ++ ([true,false]) ++ (rep [false] (n)) = ([false,false,false,true]) ++ (rep [false,false,true] (n)) ++ ([true,false]) ++ (rep [false] (n)) := by
  rfl

theorem finalR (n : Nat) : ([] : List Bool) = [] := by
  rfl

theorem growth (n : Nat) : run0 table (18+14*n) (family n) = some (family (n+1)) := by
  have H := (join0 (join0 (join0 (join0 (phase0 n) (phase1 n)) (phase2 n)) (phase3 n)) (phase4 n))
  rw [show 7+9*n+6+5*n+5=18+14*n by omega] at H
  simpa only [family,rep,List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using H

theorem never (m : Machine) (hm : compatible table m) : NeverHalts m :=
  never_of_growth table family 1 (fun n => 18+14*n) entry (by intro n; omega) growth m hm

#print axioms never

end M2039

namespace M2114

-- 1RB0RB_1RC1RF_0RD---_1LD0RA_0LB1LF_1LE0LD

def table : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 0,true => some (some ⟨false,true,1⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 1,true => some (some ⟨true,true,5⟩)
  | 2,false => some (some ⟨false,true,3⟩)
  | 3,false => some (some ⟨true,false,3⟩)
  | 3,true => some (some ⟨false,true,0⟩)
  | 4,false => some (some ⟨false,false,1⟩)
  | 4,true => some (some ⟨true,false,5⟩)
  | 5,false => some (some ⟨true,false,4⟩)
  | 5,true => some (some ⟨false,false,3⟩)
  | _,_ => none

def family (n : Nat) : Z0 := ⟨1,([false,true,false,true,false]) ++ (rep [true,false] (n)) ++ ([false,false,false,true]) ++ (rep [false,true] (n)),[]⟩

theorem entry : run0 table 29 ⟨0,[],[]⟩ = some (family 0) := by rfl

theorem phase0 (n : Nat) : run0 table 12 ⟨1,([false,true,false,true,false]) ++ (rep [true,false] (n)) ++ ([false,false,false,true]) ++ (rep [false,true] (n)),[]⟩ = some ⟨5,([false,true,false,true,false]) ++ (rep [true,false] (n)) ++ ([false,false,false,true]) ++ (rep [false,true] (n)),([true,true,true])⟩ := by rfl

theorem local1 (L R : List Bool) : run0 table 2 ⟨5,([false,true,false,true,false]) ++ ([true,false]) ++ (L),(R)⟩ = some ⟨5,([false,true,false,true,false]) ++ (L),([true,true]) ++ (R)⟩ := by rfl

theorem phase1 (n : Nat) : run0 table (2*n) ⟨5,([false,true,false,true,false]) ++ (rep [true,false] (n)) ++ ([false,false,false,true]) ++ (rep [false,true] (n)),([true,true,true])⟩ = some ⟨5,([false,true,false,true,false,false,false,false,true]) ++ (rep [false,true] (n)),(rep [true,true] (n)) ++ ([true,true,true])⟩ := by
  simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using sweepL table 5 [false,true,false,true,false] [] [true,false] [true,true] 2 local1 n (([false,false,false,true]) ++ (rep [false,true] (n))) (([true,true,true]))

theorem phase2 (n : Nat) : run0 table 10 ⟨5,([false,true,false,true,false,false,false,false,true]) ++ (rep [false,true] (n)),(rep [true,true] (n)) ++ ([true,true,true])⟩ = some ⟨1,([true,false,false,false,true,false,true]) ++ (rep [false,true] (n)),([true,true]) ++ (rep [true,true] (n)) ++ ([true,true,true])⟩ := by rfl

theorem local3 (L R : List Bool) : run0 table 4 ⟨1,([true]) ++ (L),([true,true]) ++ ([true,true]) ++ (R)⟩ = some ⟨1,([true]) ++ ([true,false]) ++ (L),([true,true]) ++ (R)⟩ := by rfl

theorem phase3 (n : Nat) : run0 table (4*n) ⟨1,([true,false,false,false,true,false,true]) ++ (rep [false,true] (n)),([true,true]) ++ (rep [true,true] (n)) ++ ([true,true,true])⟩ = some ⟨1,([true]) ++ (rep [true,false] (n)) ++ ([false,false,false,true,false,true]) ++ (rep [false,true] (n)),([true,true,true,true,true])⟩ := by
  simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using sweepR table 1 [true] [true,true] [true,true] [true,false] 4 local3 n (([false,false,false,true,false,true]) ++ (rep [false,true] (n))) (([true,true,true]))

theorem phase4 (n : Nat) : run0 table 12 ⟨1,([true]) ++ (rep [true,false] (n)) ++ ([false,false,false,true,false,true]) ++ (rep [false,true] (n)),([true,true,true,true,true])⟩ = some ⟨1,([false,true,false,true,false,true,false]) ++ (rep [true,false] (n)) ++ ([false,false,false,true,false,true]) ++ (rep [false,true] (n)),[]⟩ := by rfl

theorem finalL (n : Nat) : ([false,true,false,true,false,true,false]) ++ (rep [true,false] (n)) ++ ([false,false,false,true,false,true]) ++ (rep [false,true] (n)) = ([false,true,false,true,false,true,false]) ++ (rep [true,false] (n)) ++ ([false,false,false,true,false,true]) ++ (rep [false,true] (n)) := by
  rfl

theorem finalR (n : Nat) : ([] : List Bool) = [] := by
  rfl

theorem growth (n : Nat) : run0 table (34+6*n) (family n) = some (family (n+1)) := by
  have H := (join0 (join0 (join0 (join0 (phase0 n) (phase1 n)) (phase2 n)) (phase3 n)) (phase4 n))
  rw [show 12+2*n+10+4*n+12=34+6*n by omega] at H
  simpa only [family,rep,List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using H

theorem never (m : Machine) (hm : compatible table m) : NeverHalts m :=
  never_of_growth table family 29 (fun n => 34+6*n) entry (by intro n; omega) growth m hm

#print axioms never

end M2114

namespace M2115

-- 1RB0RB_1RC1RF_0RD---_1LD0RA_0LD1LF_1LE0RA

def table : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 0,true => some (some ⟨false,true,1⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 1,true => some (some ⟨true,true,5⟩)
  | 2,false => some (some ⟨false,true,3⟩)
  | 3,false => some (some ⟨true,false,3⟩)
  | 3,true => some (some ⟨false,true,0⟩)
  | 4,false => some (some ⟨false,false,3⟩)
  | 4,true => some (some ⟨true,false,5⟩)
  | 5,false => some (some ⟨true,false,4⟩)
  | 5,true => some (some ⟨false,true,0⟩)
  | _,_ => none

def family (n : Nat) : Z0 := ⟨1,([false]) ++ (rep [false,false,true] (n)) ++ ([true]) ++ (rep [false] (n)),[]⟩

theorem entry : run0 table 1 ⟨0,[],[]⟩ = some (family 0) := by rfl

theorem phase0 (n : Nat) : run0 table 7 ⟨1,([false]) ++ (rep [false,false,true] (n)) ++ ([true]) ++ (rep [false] (n)),[]⟩ = some ⟨5,([false,true,false,false]) ++ (rep [false,false,true] (n)) ++ ([true]) ++ (rep [false] (n)),[]⟩ := by rfl

theorem local1 (L R : List Bool) : run0 table 9 ⟨5,([false,true,false,false]) ++ ([false,false,true]) ++ (L),(R)⟩ = some ⟨5,([false,true,false,false]) ++ (L),([true,true,true]) ++ (R)⟩ := by rfl

theorem phase1 (n : Nat) : run0 table (9*n) ⟨5,([false,true,false,false]) ++ (rep [false,false,true] (n)) ++ ([true]) ++ (rep [false] (n)),[]⟩ = some ⟨5,([false,true,false,false,true]) ++ (rep [false] (n)),(rep [true,true,true] (n))⟩ := by
  simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using sweepL table 5 [false,true,false,false] [] [false,false,true] [true,true,true] 9 local1 n (([true]) ++ (rep [false] (n))) ([])

theorem phase2 (n : Nat) : run0 table 6 ⟨5,([false,true,false,false,true]) ++ (rep [false] (n)),(rep [true,true,true] (n))⟩ = some ⟨1,([true,true,false]) ++ (rep [false] (n)),([true,true]) ++ (rep [true,true,true] (n))⟩ := by rfl

theorem local3 (L R : List Bool) : run0 table 3 ⟨1,([true]) ++ (L),([true,true]) ++ ([true,true,true]) ++ (R)⟩ = some ⟨1,([true]) ++ ([false,false,true]) ++ (L),([true,true]) ++ (R)⟩ := by rfl

theorem phase3 (n : Nat) : run0 table (3*n) ⟨1,([true,true,false]) ++ (rep [false] (n)),([true,true]) ++ (rep [true,true,true] (n))⟩ = some ⟨1,([true]) ++ (rep [false,false,true] (n)) ++ ([true,false]) ++ (rep [false] (n)),([true,true])⟩ := by
  simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using sweepR table 1 [true] [true,true] [true,true,true] [false,false,true] 3 local3 n (([true,false]) ++ (rep [false] (n))) ([])

theorem phase4 (n : Nat) : run0 table 3 ⟨1,([true]) ++ (rep [false,false,true] (n)) ++ ([true,false]) ++ (rep [false] (n)),([true,true])⟩ = some ⟨1,([false,false,false,true]) ++ (rep [false,false,true] (n)) ++ ([true,false]) ++ (rep [false] (n)),[]⟩ := by rfl

theorem finalL (n : Nat) : ([false,false,false,true]) ++ (rep [false,false,true] (n)) ++ ([true,false]) ++ (rep [false] (n)) = ([false,false,false,true]) ++ (rep [false,false,true] (n)) ++ ([true,false]) ++ (rep [false] (n)) := by
  rfl

theorem finalR (n : Nat) : ([] : List Bool) = [] := by
  rfl

theorem growth (n : Nat) : run0 table (16+12*n) (family n) = some (family (n+1)) := by
  have H := (join0 (join0 (join0 (join0 (phase0 n) (phase1 n)) (phase2 n)) (phase3 n)) (phase4 n))
  rw [show 7+9*n+6+3*n+3=16+12*n by omega] at H
  simpa only [family,rep,List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using H

theorem never (m : Machine) (hm : compatible table m) : NeverHalts m :=
  never_of_growth table family 1 (fun n => 16+12*n) entry (by intro n; omega) growth m hm

#print axioms never

end M2115

end BB6.Agent11Raw39B0RBPumps
