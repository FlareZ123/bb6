import SweepPumping
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedVariables false
namespace BB6.Agent11Raw39B0RBPumps
open BB6Coverage BB6Coverage.Agent31Pump


namespace M312

-- 1RB0RB_1RC0LF_0RD0LA_1LD0RA_1LF---_1LE0LA

def table : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 0,true => some (some ⟨false,true,1⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 1,true => some (some ⟨false,false,5⟩)
  | 2,false => some (some ⟨false,true,3⟩)
  | 2,true => some (some ⟨false,false,0⟩)
  | 3,false => some (some ⟨true,false,3⟩)
  | 3,true => some (some ⟨false,true,0⟩)
  | 4,false => some (some ⟨true,false,5⟩)
  | 5,false => some (some ⟨true,false,4⟩)
  | 5,true => some (some ⟨false,false,0⟩)
  | _,_ => none

def family (n : Nat) : Z0 := ⟨3,([false,false,true]) ++ (rep [false,false] (n)) ++ ([true]),[]⟩

theorem entry : run0 table 3 ⟨0,[],[]⟩ = some (family 0) := by rfl

theorem phase0 (n : Nat) : run0 table 5 ⟨3,([false,false,true]) ++ (rep [false,false] (n)) ++ ([true]),[]⟩ = some ⟨5,([false,false]) ++ (rep [false,false] (n)) ++ ([true]),([false])⟩ := by rfl

theorem local1 (L R : List Bool) : run0 table 2 ⟨5,([false,false]) ++ ([false,false]) ++ (L),(R)⟩ = some ⟨5,([false,false]) ++ (L),([true,true]) ++ (R)⟩ := by rfl

theorem phase1 (n : Nat) : run0 table (2*n) ⟨5,([false,false]) ++ (rep [false,false] (n)) ++ ([true]),([false])⟩ = some ⟨5,([false,false,true]),(rep [true,true] (n)) ++ ([false])⟩ := by
  simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using sweepL table 5 [false,false] [] [false,false] [true,true] 2 local1 n (([true])) (([false]))

theorem phase2 (n : Nat) : run0 table 4 ⟨5,([false,false,true]),(rep [true,true] (n)) ++ ([false])⟩ = some ⟨1,([false,true]),([true,true]) ++ (rep [true,true] (n)) ++ ([false])⟩ := by rfl

theorem local3 (L R : List Bool) : run0 table 6 ⟨1,([false]) ++ (L),([true,true]) ++ ([true,true]) ++ (R)⟩ = some ⟨1,([false]) ++ ([false,false]) ++ (L),([true,true]) ++ (R)⟩ := by rfl

theorem phase3 (n : Nat) : run0 table (6*n) ⟨1,([false,true]),([true,true]) ++ (rep [true,true] (n)) ++ ([false])⟩ = some ⟨1,([false]) ++ (rep [false,false] (n)) ++ ([true]),([true,true,false])⟩ := by
  simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using sweepR table 1 [false] [true,true] [true,true] [false,false] 6 local3 n (([true])) (([false]))

theorem phase4 (n : Nat) : run0 table 8 ⟨1,([false]) ++ (rep [false,false] (n)) ++ ([true]),([true,true,false])⟩ = some ⟨3,([false,false,true,false,false]) ++ (rep [false,false] (n)) ++ ([true]),[]⟩ := by rfl

theorem finalL (n : Nat) : ([false,false,true,false,false]) ++ (rep [false,false] (n)) ++ ([true]) = ([false,false,true,false,false]) ++ (rep [false,false] (n)) ++ ([true]) := by
  rfl

theorem finalR (n : Nat) : ([] : List Bool) = [] := by
  rfl

theorem growth (n : Nat) : run0 table (17+8*n) (family n) = some (family (n+1)) := by
  have H := (join0 (join0 (join0 (join0 (phase0 n) (phase1 n)) (phase2 n)) (phase3 n)) (phase4 n))
  rw [show 5+2*n+4+6*n+8=17+8*n by omega] at H
  simpa only [family,rep,List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using H

theorem never (m : Machine) (hm : compatible table m) : NeverHalts m :=
  never_of_growth table family 3 (fun n => 17+8*n) entry (by intro n; omega) growth m hm

#print axioms never

end M312

namespace M323

-- 1RB0RB_1RC0LF_0RD0RE_1LD0RA_---0LD_1LF0LA

def table : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 0,true => some (some ⟨false,true,1⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 1,true => some (some ⟨false,false,5⟩)
  | 2,false => some (some ⟨false,true,3⟩)
  | 2,true => some (some ⟨false,true,4⟩)
  | 3,false => some (some ⟨true,false,3⟩)
  | 3,true => some (some ⟨false,true,0⟩)
  | 4,true => some (some ⟨false,false,3⟩)
  | 5,false => some (some ⟨true,false,5⟩)
  | 5,true => some (some ⟨false,false,0⟩)
  | _,_ => none

def family (n : Nat) : Z0 := ⟨3,([false,false,true]) ++ (rep [false,false] (n)) ++ ([true]),[]⟩

theorem entry : run0 table 3 ⟨0,[],[]⟩ = some (family 0) := by rfl

theorem phase0 (n : Nat) : run0 table 5 ⟨3,([false,false,true]) ++ (rep [false,false] (n)) ++ ([true]),[]⟩ = some ⟨5,([false,false]) ++ (rep [false,false] (n)) ++ ([true]),([false])⟩ := by rfl

theorem local1 (L R : List Bool) : run0 table 2 ⟨5,([false,false]) ++ ([false,false]) ++ (L),(R)⟩ = some ⟨5,([false,false]) ++ (L),([true,true]) ++ (R)⟩ := by rfl

theorem phase1 (n : Nat) : run0 table (2*n) ⟨5,([false,false]) ++ (rep [false,false] (n)) ++ ([true]),([false])⟩ = some ⟨5,([false,false,true]),(rep [true,true] (n)) ++ ([false])⟩ := by
  simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using sweepL table 5 [false,false] [] [false,false] [true,true] 2 local1 n (([true])) (([false]))

theorem phase2 (n : Nat) : run0 table 4 ⟨5,([false,false,true]),(rep [true,true] (n)) ++ ([false])⟩ = some ⟨1,([false,true]),([true,true]) ++ (rep [true,true] (n)) ++ ([false])⟩ := by rfl

theorem local3 (L R : List Bool) : run0 table 6 ⟨1,([false]) ++ (L),([true,true]) ++ ([true,true]) ++ (R)⟩ = some ⟨1,([false]) ++ ([false,false]) ++ (L),([true,true]) ++ (R)⟩ := by rfl

theorem phase3 (n : Nat) : run0 table (6*n) ⟨1,([false,true]),([true,true]) ++ (rep [true,true] (n)) ++ ([false])⟩ = some ⟨1,([false]) ++ (rep [false,false] (n)) ++ ([true]),([true,true,false])⟩ := by
  simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using sweepR table 1 [false] [true,true] [true,true] [false,false] 6 local3 n (([true])) (([false]))

theorem phase4 (n : Nat) : run0 table 8 ⟨1,([false]) ++ (rep [false,false] (n)) ++ ([true]),([true,true,false])⟩ = some ⟨3,([false,false,true,false,false]) ++ (rep [false,false] (n)) ++ ([true]),[]⟩ := by rfl

theorem finalL (n : Nat) : ([false,false,true,false,false]) ++ (rep [false,false] (n)) ++ ([true]) = ([false,false,true,false,false]) ++ (rep [false,false] (n)) ++ ([true]) := by
  rfl

theorem finalR (n : Nat) : ([] : List Bool) = [] := by
  rfl

theorem growth (n : Nat) : run0 table (17+8*n) (family n) = some (family (n+1)) := by
  have H := (join0 (join0 (join0 (join0 (phase0 n) (phase1 n)) (phase2 n)) (phase3 n)) (phase4 n))
  rw [show 5+2*n+4+6*n+8=17+8*n by omega] at H
  simpa only [family,rep,List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using H

theorem never (m : Machine) (hm : compatible table m) : NeverHalts m :=
  never_of_growth table family 3 (fun n => 17+8*n) entry (by intro n; omega) growth m hm

#print axioms never

end M323

namespace M592

-- 1RB0RB_1RC0RE_0RD0RF_1LD0RA_0RD0LA_---0LD

def table : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 0,true => some (some ⟨false,true,1⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 1,true => some (some ⟨false,true,4⟩)
  | 2,false => some (some ⟨false,true,3⟩)
  | 2,true => some (some ⟨false,true,5⟩)
  | 3,false => some (some ⟨true,false,3⟩)
  | 3,true => some (some ⟨false,true,0⟩)
  | 4,false => some (some ⟨false,true,3⟩)
  | 4,true => some (some ⟨false,false,0⟩)
  | 5,true => some (some ⟨false,false,3⟩)
  | _,_ => none

def family (n : Nat) : Z0 := ⟨2,([false,true]) ++ (rep [false,false] (n)) ++ ([true]) ++ (rep [false,false] (n)),[]⟩

theorem entry : run0 table 2 ⟨0,[],[]⟩ = some (family 0) := by rfl

theorem phase0 (n : Nat) : run0 table 7 ⟨2,([false,true]) ++ (rep [false,false] (n)) ++ ([true]) ++ (rep [false,false] (n)),[]⟩ = some ⟨3,([false,false,false,false,false]) ++ (rep [false,false] (n)) ++ ([true]) ++ (rep [false,false] (n)),[]⟩ := by rfl

theorem local1 (L R : List Bool) : run0 table 2 ⟨3,([false,false,false,false,false]) ++ ([false,false]) ++ (L),(R)⟩ = some ⟨3,([false,false,false,false,false]) ++ (L),([true,true]) ++ (R)⟩ := by rfl

theorem phase1 (n : Nat) : run0 table (2*n) ⟨3,([false,false,false,false,false]) ++ (rep [false,false] (n)) ++ ([true]) ++ (rep [false,false] (n)),[]⟩ = some ⟨3,([false,false,false,false,false,true]) ++ (rep [false,false] (n)),(rep [true,true] (n))⟩ := by
  simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using sweepL table 3 [false,false,false,false,false] [] [false,false] [true,true] 2 local1 n (([true]) ++ (rep [false,false] (n))) ([])

theorem phase2 (n : Nat) : run0 table 10 ⟨3,([false,false,false,false,false,true]) ++ (rep [false,false] (n)),(rep [true,true] (n))⟩ = some ⟨1,([false,true,false,false]) ++ (rep [false,false] (n)),([true,true]) ++ (rep [true,true] (n))⟩ := by rfl

theorem local3 (L R : List Bool) : run0 table 6 ⟨1,([false]) ++ (L),([true,true]) ++ ([true,true]) ++ (R)⟩ = some ⟨1,([false]) ++ ([false,false]) ++ (L),([true,true]) ++ (R)⟩ := by rfl

theorem phase3 (n : Nat) : run0 table (6*n) ⟨1,([false,true,false,false]) ++ (rep [false,false] (n)),([true,true]) ++ (rep [true,true] (n))⟩ = some ⟨1,([false]) ++ (rep [false,false] (n)) ++ ([true,false,false]) ++ (rep [false,false] (n)),([true,true])⟩ := by
  simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using sweepR table 1 [false] [true,true] [true,true] [false,false] 6 local3 n (([true,false,false]) ++ (rep [false,false] (n))) ([])

theorem phase4 (n : Nat) : run0 table 7 ⟨1,([false]) ++ (rep [false,false] (n)) ++ ([true,false,false]) ++ (rep [false,false] (n)),([true,true])⟩ = some ⟨2,([false,true,false,false]) ++ (rep [false,false] (n)) ++ ([true,false,false]) ++ (rep [false,false] (n)),[]⟩ := by rfl

theorem finalL (n : Nat) : ([false,true,false,false]) ++ (rep [false,false] (n)) ++ ([true,false,false]) ++ (rep [false,false] (n)) = ([false,true,false,false]) ++ (rep [false,false] (n)) ++ ([true,false,false]) ++ (rep [false,false] (n)) := by
  rfl

theorem finalR (n : Nat) : ([] : List Bool) = [] := by
  rfl

theorem growth (n : Nat) : run0 table (24+8*n) (family n) = some (family (n+1)) := by
  have H := (join0 (join0 (join0 (join0 (phase0 n) (phase1 n)) (phase2 n)) (phase3 n)) (phase4 n))
  rw [show 7+2*n+10+6*n+7=24+8*n by omega] at H
  simpa only [family,rep,List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using H

theorem never (m : Machine) (hm : compatible table m) : NeverHalts m :=
  never_of_growth table family 2 (fun n => 24+8*n) entry (by intro n; omega) growth m hm

#print axioms never

end M592

namespace M658

-- 1RB0RB_1RC0RE_0RD0RF_1LD0RA_1LE0LA_---0LD

def table : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 0,true => some (some ⟨false,true,1⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 1,true => some (some ⟨false,true,4⟩)
  | 2,false => some (some ⟨false,true,3⟩)
  | 2,true => some (some ⟨false,true,5⟩)
  | 3,false => some (some ⟨true,false,3⟩)
  | 3,true => some (some ⟨false,true,0⟩)
  | 4,false => some (some ⟨true,false,4⟩)
  | 4,true => some (some ⟨false,false,0⟩)
  | 5,true => some (some ⟨false,false,3⟩)
  | _,_ => none

def family (n : Nat) : Z0 := ⟨2,([false,true]) ++ (rep [false,false,false,false] (n)) ++ ([true]),[]⟩

theorem entry : run0 table 2 ⟨0,[],[]⟩ = some (family 0) := by rfl

theorem phase0 (n : Nat) : run0 table 6 ⟨2,([false,true]) ++ (rep [false,false,false,false] (n)) ++ ([true]),[]⟩ = some ⟨4,([false,false,false,false]) ++ (rep [false,false,false,false] (n)) ++ ([true]),[]⟩ := by rfl

theorem local1 (L R : List Bool) : run0 table 4 ⟨4,([false,false,false,false]) ++ ([false,false,false,false]) ++ (L),(R)⟩ = some ⟨4,([false,false,false,false]) ++ (L),([true,true,true,true]) ++ (R)⟩ := by rfl

theorem phase1 (n : Nat) : run0 table (4*n) ⟨4,([false,false,false,false]) ++ (rep [false,false,false,false] (n)) ++ ([true]),[]⟩ = some ⟨4,([false,false,false,false,true]),(rep [true,true,true,true] (n))⟩ := by
  simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using sweepL table 4 [false,false,false,false] [] [false,false,false,false] [true,true,true,true] 4 local1 n (([true])) ([])

theorem phase2 (n : Nat) : run0 table 6 ⟨4,([false,false,false,false,true]),(rep [true,true,true,true] (n))⟩ = some ⟨1,([false,true]),([true,true,true,true]) ++ (rep [true,true,true,true] (n))⟩ := by rfl

theorem local3 (L R : List Bool) : run0 table 12 ⟨1,([false]) ++ (L),([true,true,true,true]) ++ ([true,true,true,true]) ++ (R)⟩ = some ⟨1,([false]) ++ ([false,false,false,false]) ++ (L),([true,true,true,true]) ++ (R)⟩ := by rfl

theorem phase3 (n : Nat) : run0 table (12*n) ⟨1,([false,true]),([true,true,true,true]) ++ (rep [true,true,true,true] (n))⟩ = some ⟨1,([false]) ++ (rep [false,false,false,false] (n)) ++ ([true]),([true,true,true,true])⟩ := by
  simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using sweepR table 1 [false] [true,true,true,true] [true,true,true,true] [false,false,false,false] 12 local3 n (([true])) ([])

theorem phase4 (n : Nat) : run0 table 13 ⟨1,([false]) ++ (rep [false,false,false,false] (n)) ++ ([true]),([true,true,true,true])⟩ = some ⟨2,([false,true,false,false,false,false]) ++ (rep [false,false,false,false] (n)) ++ ([true]),[]⟩ := by rfl

theorem finalL (n : Nat) : ([false,true,false,false,false,false]) ++ (rep [false,false,false,false] (n)) ++ ([true]) = ([false,true,false,false,false,false]) ++ (rep [false,false,false,false] (n)) ++ ([true]) := by
  rfl

theorem finalR (n : Nat) : ([] : List Bool) = [] := by
  rfl

theorem growth (n : Nat) : run0 table (25+16*n) (family n) = some (family (n+1)) := by
  have H := (join0 (join0 (join0 (join0 (phase0 n) (phase1 n)) (phase2 n)) (phase3 n)) (phase4 n))
  rw [show 6+4*n+6+12*n+13=25+16*n by omega] at H
  simpa only [family,rep,List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using H

theorem never (m : Machine) (hm : compatible table m) : NeverHalts m :=
  never_of_growth table family 2 (fun n => 25+16*n) entry (by intro n; omega) growth m hm

#print axioms never

end M658

namespace M697

-- 1RB0RB_1RC0RE_0RD0LA_1LD0RA_1LF0LA_1LE---

def table : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 0,true => some (some ⟨false,true,1⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 1,true => some (some ⟨false,true,4⟩)
  | 2,false => some (some ⟨false,true,3⟩)
  | 2,true => some (some ⟨false,false,0⟩)
  | 3,false => some (some ⟨true,false,3⟩)
  | 3,true => some (some ⟨false,true,0⟩)
  | 4,false => some (some ⟨true,false,5⟩)
  | 4,true => some (some ⟨false,false,0⟩)
  | 5,false => some (some ⟨true,false,4⟩)
  | _,_ => none

def family (n : Nat) : Z0 := ⟨2,([false,true]) ++ (rep [false,false,false,false] (n)) ++ ([true]),[]⟩

theorem entry : run0 table 2 ⟨0,[],[]⟩ = some (family 0) := by rfl

theorem phase0 (n : Nat) : run0 table 6 ⟨2,([false,true]) ++ (rep [false,false,false,false] (n)) ++ ([true]),[]⟩ = some ⟨4,([false,false,false,false]) ++ (rep [false,false,false,false] (n)) ++ ([true]),[]⟩ := by rfl

theorem local1 (L R : List Bool) : run0 table 4 ⟨4,([false,false,false,false]) ++ ([false,false,false,false]) ++ (L),(R)⟩ = some ⟨4,([false,false,false,false]) ++ (L),([true,true,true,true]) ++ (R)⟩ := by rfl

theorem phase1 (n : Nat) : run0 table (4*n) ⟨4,([false,false,false,false]) ++ (rep [false,false,false,false] (n)) ++ ([true]),[]⟩ = some ⟨4,([false,false,false,false,true]),(rep [true,true,true,true] (n))⟩ := by
  simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using sweepL table 4 [false,false,false,false] [] [false,false,false,false] [true,true,true,true] 4 local1 n (([true])) ([])

theorem phase2 (n : Nat) : run0 table 6 ⟨4,([false,false,false,false,true]),(rep [true,true,true,true] (n))⟩ = some ⟨1,([false,true]),([true,true,true,true]) ++ (rep [true,true,true,true] (n))⟩ := by rfl

theorem local3 (L R : List Bool) : run0 table 12 ⟨1,([false]) ++ (L),([true,true,true,true]) ++ ([true,true,true,true]) ++ (R)⟩ = some ⟨1,([false]) ++ ([false,false,false,false]) ++ (L),([true,true,true,true]) ++ (R)⟩ := by rfl

theorem phase3 (n : Nat) : run0 table (12*n) ⟨1,([false,true]),([true,true,true,true]) ++ (rep [true,true,true,true] (n))⟩ = some ⟨1,([false]) ++ (rep [false,false,false,false] (n)) ++ ([true]),([true,true,true,true])⟩ := by
  simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using sweepR table 1 [false] [true,true,true,true] [true,true,true,true] [false,false,false,false] 12 local3 n (([true])) ([])

theorem phase4 (n : Nat) : run0 table 13 ⟨1,([false]) ++ (rep [false,false,false,false] (n)) ++ ([true]),([true,true,true,true])⟩ = some ⟨2,([false,true,false,false,false,false]) ++ (rep [false,false,false,false] (n)) ++ ([true]),[]⟩ := by rfl

theorem finalL (n : Nat) : ([false,true,false,false,false,false]) ++ (rep [false,false,false,false] (n)) ++ ([true]) = ([false,true,false,false,false,false]) ++ (rep [false,false,false,false] (n)) ++ ([true]) := by
  rfl

theorem finalR (n : Nat) : ([] : List Bool) = [] := by
  rfl

theorem growth (n : Nat) : run0 table (25+16*n) (family n) = some (family (n+1)) := by
  have H := (join0 (join0 (join0 (join0 (phase0 n) (phase1 n)) (phase2 n)) (phase3 n)) (phase4 n))
  rw [show 6+4*n+6+12*n+13=25+16*n by omega] at H
  simpa only [family,rep,List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using H

theorem never (m : Machine) (hm : compatible table m) : NeverHalts m :=
  never_of_growth table family 2 (fun n => 25+16*n) entry (by intro n; omega) growth m hm

#print axioms never

end M697

namespace M726

-- 1RB0RB_1RC0RE_0RD0LF_1LD0RA_1RF---_1LC1RF

def table : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 0,true => some (some ⟨false,true,1⟩)
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

def family (n : Nat) : Z0 := ⟨5,([false,true]) ++ (rep [true] (n)) ++ ([false,true,false,false,false,true]),[]⟩

theorem entry : run0 table 17 ⟨0,[],[]⟩ = some (family 0) := by rfl

theorem local0 (L R : List Bool) : run0 table 3 ⟨5,([false,true]) ++ ([true]) ++ (L),(R)⟩ = some ⟨5,([false,true]) ++ (L),([true]) ++ (R)⟩ := by rfl

theorem phase0 (n : Nat) : run0 table (3*n) ⟨5,([false,true]) ++ (rep [true] (n)) ++ ([false,true,false,false,false,true]),[]⟩ = some ⟨5,([false,true,false,true,false,false,false,true]),(rep [true] (n))⟩ := by
  simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using sweepL table 5 [false,true] [] [true] [true] 3 local0 n (([false,true,false,false,false,true])) ([])

theorem phase1 (n : Nat) : run0 table 10 ⟨5,([false,true,false,true,false,false,false,true]),(rep [true] (n))⟩ = some ⟨5,([true,true,false,true,false,false,false,true]),(rep [true] (n))⟩ := by rfl

theorem local2 (L R : List Bool) : run0 table 1 ⟨5,([true]) ++ (L),([true]) ++ (R)⟩ = some ⟨5,([true]) ++ ([true]) ++ (L),(R)⟩ := by rfl

theorem phase2 (n : Nat) : run0 table (1*n) ⟨5,([true,true,false,true,false,false,false,true]),(rep [true] (n))⟩ = some ⟨5,([true]) ++ (rep [true] (n)) ++ ([true,false,true,false,false,false,true]),[]⟩ := by
  simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using sweepR table 5 [true] [] [true] [true] 1 local2 n (([true,false,true,false,false,false,true])) ([])

theorem phase3 (n : Nat) : run0 table 1 ⟨5,([true]) ++ (rep [true] (n)) ++ ([true,false,true,false,false,false,true]),[]⟩ = some ⟨5,([false,true]) ++ (rep [true] (n)) ++ ([true,false,true,false,false,false,true]),[]⟩ := by rfl

theorem finalL (n : Nat) : ([false,true]) ++ (rep [true] (n)) ++ ([true,false,true,false,false,false,true]) = ([false,true,true]) ++ (rep [true] (n)) ++ ([false,true,false,false,false,true]) := by
  calc
    _ = ([false,true,true]) ++ (rep [true] (n)) ++ ([false,true,false,false,false,true]) := by symm; simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using moveCut (([false,true])) (([false,true,false,false,false,true])) [] true n

theorem finalR (n : Nat) : ([] : List Bool) = [] := by
  rfl

theorem growth (n : Nat) : run0 table (11+4*n) (family n) = some (family (n+1)) := by
  have H := (join0 (join0 (join0 (phase0 n) (phase1 n)) (phase2 n)) (phase3 n))
  rw [finalL n] at H
  rw [show 3*n+10+1*n+1=11+4*n by omega] at H
  simpa only [family,rep,List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using H

theorem never (m : Machine) (hm : compatible table m) : NeverHalts m :=
  never_of_growth table family 17 (fun n => 11+4*n) entry (by intro n; omega) growth m hm

#print axioms never

end M726

namespace M795

-- 1RB0RB_1RC0RF_0RD0RE_1LD0RA_---0LD_0RD0LA

def table : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 0,true => some (some ⟨false,true,1⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 1,true => some (some ⟨false,true,5⟩)
  | 2,false => some (some ⟨false,true,3⟩)
  | 2,true => some (some ⟨false,true,4⟩)
  | 3,false => some (some ⟨true,false,3⟩)
  | 3,true => some (some ⟨false,true,0⟩)
  | 4,true => some (some ⟨false,false,3⟩)
  | 5,false => some (some ⟨false,true,3⟩)
  | 5,true => some (some ⟨false,false,0⟩)
  | _,_ => none

def family (n : Nat) : Z0 := ⟨2,([false,true]) ++ (rep [false,false] (n)) ++ ([true]) ++ (rep [false,false] (n)),[]⟩

theorem entry : run0 table 2 ⟨0,[],[]⟩ = some (family 0) := by rfl

theorem phase0 (n : Nat) : run0 table 7 ⟨2,([false,true]) ++ (rep [false,false] (n)) ++ ([true]) ++ (rep [false,false] (n)),[]⟩ = some ⟨3,([false,false,false,false,false]) ++ (rep [false,false] (n)) ++ ([true]) ++ (rep [false,false] (n)),[]⟩ := by rfl

theorem local1 (L R : List Bool) : run0 table 2 ⟨3,([false,false,false,false,false]) ++ ([false,false]) ++ (L),(R)⟩ = some ⟨3,([false,false,false,false,false]) ++ (L),([true,true]) ++ (R)⟩ := by rfl

theorem phase1 (n : Nat) : run0 table (2*n) ⟨3,([false,false,false,false,false]) ++ (rep [false,false] (n)) ++ ([true]) ++ (rep [false,false] (n)),[]⟩ = some ⟨3,([false,false,false,false,false,true]) ++ (rep [false,false] (n)),(rep [true,true] (n))⟩ := by
  simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using sweepL table 3 [false,false,false,false,false] [] [false,false] [true,true] 2 local1 n (([true]) ++ (rep [false,false] (n))) ([])

theorem phase2 (n : Nat) : run0 table 10 ⟨3,([false,false,false,false,false,true]) ++ (rep [false,false] (n)),(rep [true,true] (n))⟩ = some ⟨1,([false,true,false,false]) ++ (rep [false,false] (n)),([true,true]) ++ (rep [true,true] (n))⟩ := by rfl

theorem local3 (L R : List Bool) : run0 table 6 ⟨1,([false]) ++ (L),([true,true]) ++ ([true,true]) ++ (R)⟩ = some ⟨1,([false]) ++ ([false,false]) ++ (L),([true,true]) ++ (R)⟩ := by rfl

theorem phase3 (n : Nat) : run0 table (6*n) ⟨1,([false,true,false,false]) ++ (rep [false,false] (n)),([true,true]) ++ (rep [true,true] (n))⟩ = some ⟨1,([false]) ++ (rep [false,false] (n)) ++ ([true,false,false]) ++ (rep [false,false] (n)),([true,true])⟩ := by
  simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using sweepR table 1 [false] [true,true] [true,true] [false,false] 6 local3 n (([true,false,false]) ++ (rep [false,false] (n))) ([])

theorem phase4 (n : Nat) : run0 table 7 ⟨1,([false]) ++ (rep [false,false] (n)) ++ ([true,false,false]) ++ (rep [false,false] (n)),([true,true])⟩ = some ⟨2,([false,true,false,false]) ++ (rep [false,false] (n)) ++ ([true,false,false]) ++ (rep [false,false] (n)),[]⟩ := by rfl

theorem finalL (n : Nat) : ([false,true,false,false]) ++ (rep [false,false] (n)) ++ ([true,false,false]) ++ (rep [false,false] (n)) = ([false,true,false,false]) ++ (rep [false,false] (n)) ++ ([true,false,false]) ++ (rep [false,false] (n)) := by
  rfl

theorem finalR (n : Nat) : ([] : List Bool) = [] := by
  rfl

theorem growth (n : Nat) : run0 table (24+8*n) (family n) = some (family (n+1)) := by
  have H := (join0 (join0 (join0 (join0 (phase0 n) (phase1 n)) (phase2 n)) (phase3 n)) (phase4 n))
  rw [show 7+2*n+10+6*n+7=24+8*n by omega] at H
  simpa only [family,rep,List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using H

theorem never (m : Machine) (hm : compatible table m) : NeverHalts m :=
  never_of_growth table family 2 (fun n => 24+8*n) entry (by intro n; omega) growth m hm

#print axioms never

end M795

namespace M893

-- 1RB0RB_1RC0RF_0RD0LA_1LD0RA_1LF---_1LE0LA

def table : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 0,true => some (some ⟨false,true,1⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 1,true => some (some ⟨false,true,5⟩)
  | 2,false => some (some ⟨false,true,3⟩)
  | 2,true => some (some ⟨false,false,0⟩)
  | 3,false => some (some ⟨true,false,3⟩)
  | 3,true => some (some ⟨false,true,0⟩)
  | 4,false => some (some ⟨true,false,5⟩)
  | 5,false => some (some ⟨true,false,4⟩)
  | 5,true => some (some ⟨false,false,0⟩)
  | _,_ => none

def family (n : Nat) : Z0 := ⟨2,([false,true]) ++ (rep [false,false,false,false] (n)) ++ ([true]),[]⟩

theorem entry : run0 table 2 ⟨0,[],[]⟩ = some (family 0) := by rfl

theorem phase0 (n : Nat) : run0 table 6 ⟨2,([false,true]) ++ (rep [false,false,false,false] (n)) ++ ([true]),[]⟩ = some ⟨5,([false,false,false,false]) ++ (rep [false,false,false,false] (n)) ++ ([true]),[]⟩ := by rfl

theorem local1 (L R : List Bool) : run0 table 4 ⟨5,([false,false,false,false]) ++ ([false,false,false,false]) ++ (L),(R)⟩ = some ⟨5,([false,false,false,false]) ++ (L),([true,true,true,true]) ++ (R)⟩ := by rfl

theorem phase1 (n : Nat) : run0 table (4*n) ⟨5,([false,false,false,false]) ++ (rep [false,false,false,false] (n)) ++ ([true]),[]⟩ = some ⟨5,([false,false,false,false,true]),(rep [true,true,true,true] (n))⟩ := by
  simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using sweepL table 5 [false,false,false,false] [] [false,false,false,false] [true,true,true,true] 4 local1 n (([true])) ([])

theorem phase2 (n : Nat) : run0 table 6 ⟨5,([false,false,false,false,true]),(rep [true,true,true,true] (n))⟩ = some ⟨1,([false,true]),([true,true,true,true]) ++ (rep [true,true,true,true] (n))⟩ := by rfl

theorem local3 (L R : List Bool) : run0 table 12 ⟨1,([false]) ++ (L),([true,true,true,true]) ++ ([true,true,true,true]) ++ (R)⟩ = some ⟨1,([false]) ++ ([false,false,false,false]) ++ (L),([true,true,true,true]) ++ (R)⟩ := by rfl

theorem phase3 (n : Nat) : run0 table (12*n) ⟨1,([false,true]),([true,true,true,true]) ++ (rep [true,true,true,true] (n))⟩ = some ⟨1,([false]) ++ (rep [false,false,false,false] (n)) ++ ([true]),([true,true,true,true])⟩ := by
  simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using sweepR table 1 [false] [true,true,true,true] [true,true,true,true] [false,false,false,false] 12 local3 n (([true])) ([])

theorem phase4 (n : Nat) : run0 table 13 ⟨1,([false]) ++ (rep [false,false,false,false] (n)) ++ ([true]),([true,true,true,true])⟩ = some ⟨2,([false,true,false,false,false,false]) ++ (rep [false,false,false,false] (n)) ++ ([true]),[]⟩ := by rfl

theorem finalL (n : Nat) : ([false,true,false,false,false,false]) ++ (rep [false,false,false,false] (n)) ++ ([true]) = ([false,true,false,false,false,false]) ++ (rep [false,false,false,false] (n)) ++ ([true]) := by
  rfl

theorem finalR (n : Nat) : ([] : List Bool) = [] := by
  rfl

theorem growth (n : Nat) : run0 table (25+16*n) (family n) = some (family (n+1)) := by
  have H := (join0 (join0 (join0 (join0 (phase0 n) (phase1 n)) (phase2 n)) (phase3 n)) (phase4 n))
  rw [show 6+4*n+6+12*n+13=25+16*n by omega] at H
  simpa only [family,rep,List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using H

theorem never (m : Machine) (hm : compatible table m) : NeverHalts m :=
  never_of_growth table family 2 (fun n => 25+16*n) entry (by intro n; omega) growth m hm

#print axioms never

end M893

namespace M900

-- 1RB0RB_1RC0RF_0RD0RE_1LD0RA_---0LD_1LF0LA

def table : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 0,true => some (some ⟨false,true,1⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 1,true => some (some ⟨false,true,5⟩)
  | 2,false => some (some ⟨false,true,3⟩)
  | 2,true => some (some ⟨false,true,4⟩)
  | 3,false => some (some ⟨true,false,3⟩)
  | 3,true => some (some ⟨false,true,0⟩)
  | 4,true => some (some ⟨false,false,3⟩)
  | 5,false => some (some ⟨true,false,5⟩)
  | 5,true => some (some ⟨false,false,0⟩)
  | _,_ => none

def family (n : Nat) : Z0 := ⟨2,([false,true]) ++ (rep [false,false,false,false] (n)) ++ ([true]),[]⟩

theorem entry : run0 table 2 ⟨0,[],[]⟩ = some (family 0) := by rfl

theorem phase0 (n : Nat) : run0 table 6 ⟨2,([false,true]) ++ (rep [false,false,false,false] (n)) ++ ([true]),[]⟩ = some ⟨5,([false,false,false,false]) ++ (rep [false,false,false,false] (n)) ++ ([true]),[]⟩ := by rfl

theorem local1 (L R : List Bool) : run0 table 4 ⟨5,([false,false,false,false]) ++ ([false,false,false,false]) ++ (L),(R)⟩ = some ⟨5,([false,false,false,false]) ++ (L),([true,true,true,true]) ++ (R)⟩ := by rfl

theorem phase1 (n : Nat) : run0 table (4*n) ⟨5,([false,false,false,false]) ++ (rep [false,false,false,false] (n)) ++ ([true]),[]⟩ = some ⟨5,([false,false,false,false,true]),(rep [true,true,true,true] (n))⟩ := by
  simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using sweepL table 5 [false,false,false,false] [] [false,false,false,false] [true,true,true,true] 4 local1 n (([true])) ([])

theorem phase2 (n : Nat) : run0 table 6 ⟨5,([false,false,false,false,true]),(rep [true,true,true,true] (n))⟩ = some ⟨1,([false,true]),([true,true,true,true]) ++ (rep [true,true,true,true] (n))⟩ := by rfl

theorem local3 (L R : List Bool) : run0 table 12 ⟨1,([false]) ++ (L),([true,true,true,true]) ++ ([true,true,true,true]) ++ (R)⟩ = some ⟨1,([false]) ++ ([false,false,false,false]) ++ (L),([true,true,true,true]) ++ (R)⟩ := by rfl

theorem phase3 (n : Nat) : run0 table (12*n) ⟨1,([false,true]),([true,true,true,true]) ++ (rep [true,true,true,true] (n))⟩ = some ⟨1,([false]) ++ (rep [false,false,false,false] (n)) ++ ([true]),([true,true,true,true])⟩ := by
  simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using sweepR table 1 [false] [true,true,true,true] [true,true,true,true] [false,false,false,false] 12 local3 n (([true])) ([])

theorem phase4 (n : Nat) : run0 table 13 ⟨1,([false]) ++ (rep [false,false,false,false] (n)) ++ ([true]),([true,true,true,true])⟩ = some ⟨2,([false,true,false,false,false,false]) ++ (rep [false,false,false,false] (n)) ++ ([true]),[]⟩ := by rfl

theorem finalL (n : Nat) : ([false,true,false,false,false,false]) ++ (rep [false,false,false,false] (n)) ++ ([true]) = ([false,true,false,false,false,false]) ++ (rep [false,false,false,false] (n)) ++ ([true]) := by
  rfl

theorem finalR (n : Nat) : ([] : List Bool) = [] := by
  rfl

theorem growth (n : Nat) : run0 table (25+16*n) (family n) = some (family (n+1)) := by
  have H := (join0 (join0 (join0 (join0 (phase0 n) (phase1 n)) (phase2 n)) (phase3 n)) (phase4 n))
  rw [show 6+4*n+6+12*n+13=25+16*n by omega] at H
  simpa only [family,rep,List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using H

theorem never (m : Machine) (hm : compatible table m) : NeverHalts m :=
  never_of_growth table family 2 (fun n => 25+16*n) entry (by intro n; omega) growth m hm

#print axioms never

end M900

namespace M929

-- 1RB0RB_1RC0RF_0RD0LE_1LD0RA_1LC1RE_1RE---

def table : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 0,true => some (some ⟨false,true,1⟩)
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

def family (n : Nat) : Z0 := ⟨4,([false,true]) ++ (rep [true] (n)) ++ ([false,true,false,false,false,true]),[]⟩

theorem entry : run0 table 17 ⟨0,[],[]⟩ = some (family 0) := by rfl

theorem local0 (L R : List Bool) : run0 table 3 ⟨4,([false,true]) ++ ([true]) ++ (L),(R)⟩ = some ⟨4,([false,true]) ++ (L),([true]) ++ (R)⟩ := by rfl

theorem phase0 (n : Nat) : run0 table (3*n) ⟨4,([false,true]) ++ (rep [true] (n)) ++ ([false,true,false,false,false,true]),[]⟩ = some ⟨4,([false,true,false,true,false,false,false,true]),(rep [true] (n))⟩ := by
  simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using sweepL table 4 [false,true] [] [true] [true] 3 local0 n (([false,true,false,false,false,true])) ([])

theorem phase1 (n : Nat) : run0 table 10 ⟨4,([false,true,false,true,false,false,false,true]),(rep [true] (n))⟩ = some ⟨4,([true,true,false,true,false,false,false,true]),(rep [true] (n))⟩ := by rfl

theorem local2 (L R : List Bool) : run0 table 1 ⟨4,([true]) ++ (L),([true]) ++ (R)⟩ = some ⟨4,([true]) ++ ([true]) ++ (L),(R)⟩ := by rfl

theorem phase2 (n : Nat) : run0 table (1*n) ⟨4,([true,true,false,true,false,false,false,true]),(rep [true] (n))⟩ = some ⟨4,([true]) ++ (rep [true] (n)) ++ ([true,false,true,false,false,false,true]),[]⟩ := by
  simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using sweepR table 4 [true] [] [true] [true] 1 local2 n (([true,false,true,false,false,false,true])) ([])

theorem phase3 (n : Nat) : run0 table 1 ⟨4,([true]) ++ (rep [true] (n)) ++ ([true,false,true,false,false,false,true]),[]⟩ = some ⟨4,([false,true]) ++ (rep [true] (n)) ++ ([true,false,true,false,false,false,true]),[]⟩ := by rfl

theorem finalL (n : Nat) : ([false,true]) ++ (rep [true] (n)) ++ ([true,false,true,false,false,false,true]) = ([false,true,true]) ++ (rep [true] (n)) ++ ([false,true,false,false,false,true]) := by
  calc
    _ = ([false,true,true]) ++ (rep [true] (n)) ++ ([false,true,false,false,false,true]) := by symm; simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using moveCut (([false,true])) (([false,true,false,false,false,true])) [] true n

theorem finalR (n : Nat) : ([] : List Bool) = [] := by
  rfl

theorem growth (n : Nat) : run0 table (11+4*n) (family n) = some (family (n+1)) := by
  have H := (join0 (join0 (join0 (phase0 n) (phase1 n)) (phase2 n)) (phase3 n))
  rw [finalL n] at H
  rw [show 3*n+10+1*n+1=11+4*n by omega] at H
  simpa only [family,rep,List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using H

theorem never (m : Machine) (hm : compatible table m) : NeverHalts m :=
  never_of_growth table family 17 (fun n => 11+4*n) entry (by intro n; omega) growth m hm

#print axioms never

end M929

end BB6.Agent11Raw39B0RBPumps
