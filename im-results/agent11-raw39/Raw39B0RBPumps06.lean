import SweepPumping
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedVariables false
namespace BB6.Agent11Raw39B0RBPumps
open BB6Coverage BB6Coverage.Agent31Pump


namespace M270

-- 1RB0RB_1RC0LF_0RD1RA_1LD0RA_0LB---_1LE0RD

def table : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 0,true => some (some ⟨false,true,1⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 1,true => some (some ⟨false,false,5⟩)
  | 2,false => some (some ⟨false,true,3⟩)
  | 2,true => some (some ⟨true,true,0⟩)
  | 3,false => some (some ⟨true,false,3⟩)
  | 3,true => some (some ⟨false,true,0⟩)
  | 4,false => some (some ⟨false,false,1⟩)
  | 5,false => some (some ⟨true,false,4⟩)
  | 5,true => some (some ⟨false,true,3⟩)
  | _,_ => none

def family (n : Nat) : Z0 := ⟨5,[],([false,false,true,false]) ++ (rep [false,true,false,false,true,false] (n))⟩

theorem entry : run0 table 11 ⟨0,[],[]⟩ = some (family 0) := by rfl

theorem phase0 (n : Nat) : run0 table 5 ⟨5,[],([false,false,true,false]) ++ (rep [false,true,false,false,true,false] (n))⟩ = some ⟨0,([false,false,false,true]),([false,true,false]) ++ (rep [false,true,false,false,true,false] (n))⟩ := by rfl

theorem local1 (L R : List Bool) : run0 table 6 ⟨0,([false]) ++ (L),([false,true,false]) ++ ([false,true,false,false,true,false]) ++ (R)⟩ = some ⟨0,([false]) ++ ([true,true,true,true,true,true]) ++ (L),([false,true,false]) ++ (R)⟩ := by rfl

theorem phase1 (n : Nat) : run0 table (6*n) ⟨0,([false,false,false,true]),([false,true,false]) ++ (rep [false,true,false,false,true,false] (n))⟩ = some ⟨0,([false]) ++ (rep [true,true,true,true,true,true] (n)) ++ ([false,false,true]),([false,true,false])⟩ := by
  simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using sweepR table 0 [false] [false,true,false] [false,true,false,false,true,false] [true,true,true,true,true,true] 6 local1 n (([false,false,true])) ([])

theorem phase2 (n : Nat) : run0 table 6 ⟨0,([false]) ++ (rep [true,true,true,true,true,true] (n)) ++ ([false,false,true]),([false,true,false])⟩ = some ⟨3,([false,false,true,true,true,true,true]) ++ (rep [true,true,true,true,true,true] (n)) ++ ([false,false,true]),[]⟩ := by rfl

theorem local3 (L R : List Bool) : run0 table 18 ⟨3,([false,false,true,true,true,true,true]) ++ ([true,true,true,true,true,true]) ++ (L),(R)⟩ = some ⟨3,([false,false,true,true,true,true,true]) ++ (L),([false,true,false,false,true,false]) ++ (R)⟩ := by rfl

theorem phase3 (n : Nat) : run0 table (18*n) ⟨3,([false,false,true,true,true,true,true]) ++ (rep [true,true,true,true,true,true] (n)) ++ ([false,false,true]),[]⟩ = some ⟨3,([false,false,true,true,true,true,true,false,false,true]),(rep [false,true,false,false,true,false] (n))⟩ := by
  simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using sweepL table 3 [false,false,true,true,true,true,true] [] [true,true,true,true,true,true] [false,true,false,false,true,false] 18 local3 n (([false,false,true])) ([])

theorem phase4 (n : Nat) : run0 table 20 ⟨3,([false,false,true,true,true,true,true,false,false,true]),(rep [false,true,false,false,true,false] (n))⟩ = some ⟨5,[],([false,false,true,false,false,true,false,false,true,false]) ++ (rep [false,true,false,false,true,false] (n))⟩ := by rfl

theorem finalL (n : Nat) : ([] : List Bool) = [] := by
  rfl

theorem finalR (n : Nat) : ([false,false,true,false,false,true,false,false,true,false]) ++ (rep [false,true,false,false,true,false] (n)) = ([false,false,true,false,false,true,false,false,true,false]) ++ (rep [false,true,false,false,true,false] (n)) := by
  rfl

theorem growth (n : Nat) : run0 table (31+24*n) (family n) = some (family (n+1)) := by
  have H := (join0 (join0 (join0 (join0 (phase0 n) (phase1 n)) (phase2 n)) (phase3 n)) (phase4 n))
  rw [show 5+6*n+6+18*n+20=31+24*n by omega] at H
  simpa only [family,rep,List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using H

theorem never (m : Machine) (hm : compatible table m) : NeverHalts m :=
  never_of_growth table family 11 (fun n => 31+24*n) entry (by intro n; omega) growth m hm

#print axioms never

end M270

namespace M271

-- 1RB0RB_1RC0LF_0RD1RC_1LD0RA_0LB---_1LE0RB

def table : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 0,true => some (some ⟨false,true,1⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 1,true => some (some ⟨false,false,5⟩)
  | 2,false => some (some ⟨false,true,3⟩)
  | 2,true => some (some ⟨true,true,2⟩)
  | 3,false => some (some ⟨true,false,3⟩)
  | 3,true => some (some ⟨false,true,0⟩)
  | 4,false => some (some ⟨false,false,1⟩)
  | 5,false => some (some ⟨true,false,4⟩)
  | 5,true => some (some ⟨false,true,1⟩)
  | _,_ => none

def family (n : Nat) : Z0 := ⟨1,([false,true,false,false,true,false,false]) ++ (rep [true,false,false] (n)) ++ ([false,true]) ++ (rep [true] (n)),[]⟩

theorem entry : run0 table 33 ⟨0,[],[]⟩ = some (family 0) := by rfl

theorem phase0 (n : Nat) : run0 table 6 ⟨1,([false,true,false,false,true,false,false]) ++ (rep [true,false,false] (n)) ++ ([false,true]) ++ (rep [true] (n)),[]⟩ = some ⟨1,([true,false,false,true,false,false,true,false,false]) ++ (rep [true,false,false] (n)) ++ ([false,true]) ++ (rep [true] (n)),[]⟩ := by rfl

theorem local1 (L R : List Bool) : run0 table 3 ⟨1,([true,false,false,true,false,false,true,false,false]) ++ ([true,false,false]) ++ (L),(R)⟩ = some ⟨1,([true,false,false,true,false,false,true,false,false]) ++ (L),([false,true,false]) ++ (R)⟩ := by rfl

theorem phase1 (n : Nat) : run0 table (3*n) ⟨1,([true,false,false,true,false,false,true,false,false]) ++ (rep [true,false,false] (n)) ++ ([false,true]) ++ (rep [true] (n)),[]⟩ = some ⟨1,([true,false,false,true,false,false,true,false,false,false,true]) ++ (rep [true] (n)),(rep [false,true,false] (n))⟩ := by
  simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using sweepL table 1 [true,false,false,true,false,false,true,false,false] [] [true,false,false] [false,true,false] 3 local1 n (([false,true]) ++ (rep [true] (n))) ([])

theorem phase2 (n : Nat) : run0 table 25 ⟨1,([true,false,false,true,false,false,true,false,false,false,true]) ++ (rep [true] (n)),(rep [false,true,false] (n))⟩ = some ⟨1,([false,false,false,false,true,true]) ++ (rep [true] (n)),([false,true,false,true,false]) ++ (rep [false,true,false] (n))⟩ := by rfl

theorem local3 (L R : List Bool) : run0 table 15 ⟨1,([false]) ++ (L),([false,true,false,true,false]) ++ ([false,true,false]) ++ (R)⟩ = some ⟨1,([false]) ++ ([false,false,true]) ++ (L),([false,true,false,true,false]) ++ (R)⟩ := by rfl

theorem phase3 (n : Nat) : run0 table (15*n) ⟨1,([false,false,false,false,true,true]) ++ (rep [true] (n)),([false,true,false,true,false]) ++ (rep [false,true,false] (n))⟩ = some ⟨1,([false]) ++ (rep [false,false,true] (n)) ++ ([false,false,false,true,true]) ++ (rep [true] (n)),([false,true,false,true,false])⟩ := by
  simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using sweepR table 1 [false] [false,true,false,true,false] [false,true,false] [false,false,true] 15 local3 n (([false,false,false,true,true]) ++ (rep [true] (n))) ([])

theorem phase4 (n : Nat) : run0 table 19 ⟨1,([false]) ++ (rep [false,false,true] (n)) ++ ([false,false,false,true,true]) ++ (rep [true] (n)),([false,true,false,true,false])⟩ = some ⟨1,([false,true,false,false,true,false,false,true]) ++ (rep [false,false,true] (n)) ++ ([false,false,false,true,true]) ++ (rep [true] (n)),[]⟩ := by rfl

theorem finalL (n : Nat) : ([false,true,false,false,true,false,false,true]) ++ (rep [false,false,true] (n)) ++ ([false,false,false,true,true]) ++ (rep [true] (n)) = ([false,true,false,false,true,false,false,true,false,false]) ++ (rep [true,false,false] (n)) ++ ([false,true,true]) ++ (rep [true] (n)) := by
  calc
    _ = ([false,true,false,false,true,false,false,true,false]) ++ (rep [false,true,false] (n)) ++ ([false,false,true,true]) ++ (rep [true] (n)) := by symm; simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using moveCut (([false,true,false,false,true,false,false,true])) (([false,false,true,true]) ++ (rep [true] (n))) [false,true] false n
    _ = ([false,true,false,false,true,false,false,true,false,false]) ++ (rep [true,false,false] (n)) ++ ([false,true,true]) ++ (rep [true] (n)) := by symm; simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using moveCut (([false,true,false,false,true,false,false,true,false])) (([false,true,true]) ++ (rep [true] (n))) [true,false] false n

theorem finalR (n : Nat) : ([] : List Bool) = [] := by
  rfl

theorem growth (n : Nat) : run0 table (50+18*n) (family n) = some (family (n+1)) := by
  have H := (join0 (join0 (join0 (join0 (phase0 n) (phase1 n)) (phase2 n)) (phase3 n)) (phase4 n))
  rw [finalL n] at H
  rw [show 6+3*n+25+15*n+19=50+18*n by omega] at H
  simpa only [family,rep,List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using H

theorem never (m : Machine) (hm : compatible table m) : NeverHalts m :=
  never_of_growth table family 33 (fun n => 50+18*n) entry (by intro n; omega) growth m hm

#print axioms never

end M271

namespace M273

-- 1RB0RB_1RC0LF_0RD1RE_1LD0RA_0LB---_1LE0LA

def table : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 0,true => some (some ⟨false,true,1⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 1,true => some (some ⟨false,false,5⟩)
  | 2,false => some (some ⟨false,true,3⟩)
  | 2,true => some (some ⟨true,true,4⟩)
  | 3,false => some (some ⟨true,false,3⟩)
  | 3,true => some (some ⟨false,true,0⟩)
  | 4,false => some (some ⟨false,false,1⟩)
  | 5,false => some (some ⟨true,false,4⟩)
  | 5,true => some (some ⟨false,false,0⟩)
  | _,_ => none

def family (n : Nat) : Z0 := ⟨1,([false,true]) ++ (rep [false,false,true,false,false,true] (n)),[]⟩

theorem entry : run0 table 1 ⟨0,[],[]⟩ = some (family 0) := by rfl

theorem phase0 (n : Nat) : run0 table 6 ⟨1,([false,true]) ++ (rep [false,false,true,false,false,true] (n)),[]⟩ = some ⟨1,([true,false,false,true]) ++ (rep [false,false,true,false,false,true] (n)),[]⟩ := by rfl

theorem local1 (L R : List Bool) : run0 table 6 ⟨1,([true,false,false,true]) ++ ([false,false,true,false,false,true]) ++ (L),(R)⟩ = some ⟨1,([true,false,false,true]) ++ (L),([false,true,false,false,true,false]) ++ (R)⟩ := by rfl

theorem phase1 (n : Nat) : run0 table (6*n) ⟨1,([true,false,false,true]) ++ (rep [false,false,true,false,false,true] (n)),[]⟩ = some ⟨1,([true,false,false,true]),(rep [false,true,false,false,true,false] (n))⟩ := by
  simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using sweepL table 1 [true,false,false,true] [] [false,false,true,false,false,true] [false,true,false,false,true,false] 6 local1 n ([]) ([])

theorem phase2 (n : Nat) : run0 table 7 ⟨1,([true,false,false,true]),(rep [false,true,false,false,true,false] (n))⟩ = some ⟨2,([false,true]),([true,false,false,true,false]) ++ (rep [false,true,false,false,true,false] (n))⟩ := by rfl

theorem local3 (L R : List Bool) : run0 table 38 ⟨2,([false]) ++ (L),([true,false,false,true,false]) ++ ([false,true,false,false,true,false]) ++ (R)⟩ = some ⟨2,([false]) ++ ([true,false,false,true,false,false]) ++ (L),([true,false,false,true,false]) ++ (R)⟩ := by rfl

theorem phase3 (n : Nat) : run0 table (38*n) ⟨2,([false,true]),([true,false,false,true,false]) ++ (rep [false,true,false,false,true,false] (n))⟩ = some ⟨2,([false]) ++ (rep [true,false,false,true,false,false] (n)) ++ ([true]),([true,false,false,true,false])⟩ := by
  simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using sweepR table 2 [false] [true,false,false,true,false] [false,true,false,false,true,false] [true,false,false,true,false,false] 38 local3 n (([true])) ([])

theorem phase4 (n : Nat) : run0 table 22 ⟨2,([false]) ++ (rep [true,false,false,true,false,false] (n)) ++ ([true]),([true,false,false,true,false])⟩ = some ⟨1,([false,true,false,false,true,false,false]) ++ (rep [true,false,false,true,false,false] (n)) ++ ([true]),[]⟩ := by rfl

theorem finalL (n : Nat) : ([false,true,false,false,true,false,false]) ++ (rep [true,false,false,true,false,false] (n)) ++ ([true]) = ([false,true,false,false,true,false,false,true]) ++ (rep [false,false,true,false,false,true] (n)) := by
  calc
    _ = ([false,true,false,false,true,false,false,true]) ++ (rep [false,false,true,false,false,true] (n)) := by symm; simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using moveCut (([false,true,false,false,true,false,false])) ([]) [false,false,true,false,false] true n

theorem finalR (n : Nat) : ([] : List Bool) = [] := by
  rfl

theorem growth (n : Nat) : run0 table (35+44*n) (family n) = some (family (n+1)) := by
  have H := (join0 (join0 (join0 (join0 (phase0 n) (phase1 n)) (phase2 n)) (phase3 n)) (phase4 n))
  rw [finalL n] at H
  rw [show 6+6*n+7+38*n+22=35+44*n by omega] at H
  simpa only [family,rep,List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using H

theorem never (m : Machine) (hm : compatible table m) : NeverHalts m :=
  never_of_growth table family 1 (fun n => 35+44*n) entry (by intro n; omega) growth m hm

#print axioms never

end M273

namespace M285

-- 1RB0RB_1RC0LF_0RD0LD_1LD0RA_1LB---_1LE0RA

def table : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 0,true => some (some ⟨false,true,1⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 1,true => some (some ⟨false,false,5⟩)
  | 2,false => some (some ⟨false,true,3⟩)
  | 2,true => some (some ⟨false,false,3⟩)
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

theorem phase2 (n : Nat) : run0 table 19 ⟨2,([true,true]) ++ (rep [true,false,false] (n)),([true,false,true,true,false])⟩ = some ⟨1,([true,false,false,true,false,false,true,false,false]) ++ (rep [true,false,false] (n)),[]⟩ := by rfl

theorem local3 (L R : List Bool) : run0 table 3 ⟨1,([true,false,false,true,false,false,true,false,false]) ++ ([true,false,false]) ++ (L),(R)⟩ = some ⟨1,([true,false,false,true,false,false,true,false,false]) ++ (L),([true,true,false]) ++ (R)⟩ := by rfl

theorem phase3 (n : Nat) : run0 table (3*n) ⟨1,([true,false,false,true,false,false,true,false,false]) ++ (rep [true,false,false] (n)),[]⟩ = some ⟨1,([true,false,false,true,false,false,true,false,false]),(rep [true,true,false] (n))⟩ := by
  simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using sweepL table 1 [true,false,false,true,false,false,true,false,false] [] [true,false,false] [true,true,false] 3 local3 n ([]) ([])

theorem phase4 (n : Nat) : run0 table 9 ⟨1,([true,false,false,true,false,false,true,false,false]),(rep [true,true,false] (n))⟩ = some ⟨1,[],([true,true,false,true,true,false,true,true,false]) ++ (rep [true,true,false] (n))⟩ := by rfl

theorem finalL (n : Nat) : ([] : List Bool) = [] := by
  rfl

theorem finalR (n : Nat) : ([true,true,false,true,true,false,true,true,false]) ++ (rep [true,true,false] (n)) = ([true,true,false,true,true,false,true,true,false]) ++ (rep [true,true,false] (n)) := by
  rfl

theorem growth (n : Nat) : run0 table (29+10*n) (family n) = some (family (n+1)) := by
  have H := (join0 (join0 (join0 (join0 (phase0 n) (phase1 n)) (phase2 n)) (phase3 n)) (phase4 n))
  rw [show 1+7*n+19+3*n+9=29+10*n by omega] at H
  simpa only [family,rep,List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using H

theorem never (m : Machine) (hm : compatible table m) : NeverHalts m :=
  never_of_growth table family 13 (fun n => 29+10*n) entry (by intro n; omega) growth m hm

#print axioms never

end M285

namespace M286

-- 1RB0RB_1RC0LF_0RD0LD_1LD0RA_1LB---_1LE0RE

def table : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 0,true => some (some ⟨false,true,1⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 1,true => some (some ⟨false,false,5⟩)
  | 2,false => some (some ⟨false,true,3⟩)
  | 2,true => some (some ⟨false,false,3⟩)
  | 3,false => some (some ⟨true,false,3⟩)
  | 3,true => some (some ⟨false,true,0⟩)
  | 4,false => some (some ⟨true,false,1⟩)
  | 5,false => some (some ⟨true,false,4⟩)
  | 5,true => some (some ⟨false,true,4⟩)
  | _,_ => none

def family (n : Nat) : Z0 := ⟨1,[],([true,true,false,true,true,false]) ++ (rep [true,true,false] (n))⟩

theorem entry : run0 table 13 ⟨0,[],[]⟩ = some (family 0) := by rfl

theorem phase0 (n : Nat) : run0 table 1 ⟨1,[],([true,true,false,true,true,false]) ++ (rep [true,true,false] (n))⟩ = some ⟨2,([true,true]),([true,false,true,true,false]) ++ (rep [true,true,false] (n))⟩ := by rfl

theorem local1 (L R : List Bool) : run0 table 11 ⟨2,([true,true]) ++ (L),([true,false,true,true,false]) ++ ([true,true,false]) ++ (R)⟩ = some ⟨2,([true,true]) ++ ([true,false,false]) ++ (L),([true,false,true,true,false]) ++ (R)⟩ := by rfl

theorem phase1 (n : Nat) : run0 table (11*n) ⟨2,([true,true]),([true,false,true,true,false]) ++ (rep [true,true,false] (n))⟩ = some ⟨2,([true,true]) ++ (rep [true,false,false] (n)),([true,false,true,true,false])⟩ := by
  simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using sweepR table 2 [true,true] [true,false,true,true,false] [true,true,false] [true,false,false] 11 local1 n ([]) ([])

theorem phase2 (n : Nat) : run0 table 27 ⟨2,([true,true]) ++ (rep [true,false,false] (n)),([true,false,true,true,false])⟩ = some ⟨1,([true,false,false,true,false,false,true,false,false]) ++ (rep [true,false,false] (n)),[]⟩ := by rfl

theorem local3 (L R : List Bool) : run0 table 3 ⟨1,([true,false,false,true,false,false,true,false,false]) ++ ([true,false,false]) ++ (L),(R)⟩ = some ⟨1,([true,false,false,true,false,false,true,false,false]) ++ (L),([true,true,false]) ++ (R)⟩ := by rfl

theorem phase3 (n : Nat) : run0 table (3*n) ⟨1,([true,false,false,true,false,false,true,false,false]) ++ (rep [true,false,false] (n)),[]⟩ = some ⟨1,([true,false,false,true,false,false,true,false,false]),(rep [true,true,false] (n))⟩ := by
  simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using sweepL table 1 [true,false,false,true,false,false,true,false,false] [] [true,false,false] [true,true,false] 3 local3 n ([]) ([])

theorem phase4 (n : Nat) : run0 table 9 ⟨1,([true,false,false,true,false,false,true,false,false]),(rep [true,true,false] (n))⟩ = some ⟨1,[],([true,true,false,true,true,false,true,true,false]) ++ (rep [true,true,false] (n))⟩ := by rfl

theorem finalL (n : Nat) : ([] : List Bool) = [] := by
  rfl

theorem finalR (n : Nat) : ([true,true,false,true,true,false,true,true,false]) ++ (rep [true,true,false] (n)) = ([true,true,false,true,true,false,true,true,false]) ++ (rep [true,true,false] (n)) := by
  rfl

theorem growth (n : Nat) : run0 table (37+14*n) (family n) = some (family (n+1)) := by
  have H := (join0 (join0 (join0 (join0 (phase0 n) (phase1 n)) (phase2 n)) (phase3 n)) (phase4 n))
  rw [show 1+11*n+27+3*n+9=37+14*n by omega] at H
  simpa only [family,rep,List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using H

theorem never (m : Machine) (hm : compatible table m) : NeverHalts m :=
  never_of_growth table family 13 (fun n => 37+14*n) entry (by intro n; omega) growth m hm

#print axioms never

end M286

namespace M287

-- 1RB0RB_1RC0LF_0RD0LD_1LD0RA_1LB---_1LE1LC

def table : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 0,true => some (some ⟨false,true,1⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 1,true => some (some ⟨false,false,5⟩)
  | 2,false => some (some ⟨false,true,3⟩)
  | 2,true => some (some ⟨false,false,3⟩)
  | 3,false => some (some ⟨true,false,3⟩)
  | 3,true => some (some ⟨false,true,0⟩)
  | 4,false => some (some ⟨true,false,1⟩)
  | 5,false => some (some ⟨true,false,4⟩)
  | 5,true => some (some ⟨true,false,2⟩)
  | _,_ => none

def family (n : Nat) : Z0 := ⟨1,[],([true,true,false,true,true,false]) ++ (rep [true,true,false] (n))⟩

theorem entry : run0 table 13 ⟨0,[],[]⟩ = some (family 0) := by rfl

theorem phase0 (n : Nat) : run0 table 1 ⟨1,[],([true,true,false,true,true,false]) ++ (rep [true,true,false] (n))⟩ = some ⟨2,([true,true]),([true,false,true,true,false]) ++ (rep [true,true,false] (n))⟩ := by rfl

theorem local1 (L R : List Bool) : run0 table 9 ⟨2,([true,true]) ++ (L),([true,false,true,true,false]) ++ ([true,true,false]) ++ (R)⟩ = some ⟨2,([true,true]) ++ ([true,false,false]) ++ (L),([true,false,true,true,false]) ++ (R)⟩ := by rfl

theorem phase1 (n : Nat) : run0 table (9*n) ⟨2,([true,true]),([true,false,true,true,false]) ++ (rep [true,true,false] (n))⟩ = some ⟨2,([true,true]) ++ (rep [true,false,false] (n)),([true,false,true,true,false])⟩ := by
  simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using sweepR table 2 [true,true] [true,false,true,true,false] [true,true,false] [true,false,false] 9 local1 n ([]) ([])

theorem phase2 (n : Nat) : run0 table 23 ⟨2,([true,true]) ++ (rep [true,false,false] (n)),([true,false,true,true,false])⟩ = some ⟨1,([true,false,false,true,false,false,true,false,false]) ++ (rep [true,false,false] (n)),[]⟩ := by rfl

theorem local3 (L R : List Bool) : run0 table 3 ⟨1,([true,false,false,true,false,false,true,false,false]) ++ ([true,false,false]) ++ (L),(R)⟩ = some ⟨1,([true,false,false,true,false,false,true,false,false]) ++ (L),([true,true,false]) ++ (R)⟩ := by rfl

theorem phase3 (n : Nat) : run0 table (3*n) ⟨1,([true,false,false,true,false,false,true,false,false]) ++ (rep [true,false,false] (n)),[]⟩ = some ⟨1,([true,false,false,true,false,false,true,false,false]),(rep [true,true,false] (n))⟩ := by
  simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using sweepL table 1 [true,false,false,true,false,false,true,false,false] [] [true,false,false] [true,true,false] 3 local3 n ([]) ([])

theorem phase4 (n : Nat) : run0 table 9 ⟨1,([true,false,false,true,false,false,true,false,false]),(rep [true,true,false] (n))⟩ = some ⟨1,[],([true,true,false,true,true,false,true,true,false]) ++ (rep [true,true,false] (n))⟩ := by rfl

theorem finalL (n : Nat) : ([] : List Bool) = [] := by
  rfl

theorem finalR (n : Nat) : ([true,true,false,true,true,false,true,true,false]) ++ (rep [true,true,false] (n)) = ([true,true,false,true,true,false,true,true,false]) ++ (rep [true,true,false] (n)) := by
  rfl

theorem growth (n : Nat) : run0 table (33+12*n) (family n) = some (family (n+1)) := by
  have H := (join0 (join0 (join0 (join0 (phase0 n) (phase1 n)) (phase2 n)) (phase3 n)) (phase4 n))
  rw [show 1+9*n+23+3*n+9=33+12*n by omega] at H
  simpa only [family,rep,List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using H

theorem never (m : Machine) (hm : compatible table m) : NeverHalts m :=
  never_of_growth table family 13 (fun n => 33+12*n) entry (by intro n; omega) growth m hm

#print axioms never

end M287

namespace M288

-- 1RB0RB_1RC0LF_0RD0LF_1LD0RA_1LB---_1LE0RA

def table : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 0,true => some (some ⟨false,true,1⟩)
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

theorem phase2 (n : Nat) : run0 table 19 ⟨2,([true,true]) ++ (rep [true,false,false] (n)),([true,false,true,true,false])⟩ = some ⟨1,([true,false,false,true,false,false,true,false,false]) ++ (rep [true,false,false] (n)),[]⟩ := by rfl

theorem local3 (L R : List Bool) : run0 table 3 ⟨1,([true,false,false,true,false,false,true,false,false]) ++ ([true,false,false]) ++ (L),(R)⟩ = some ⟨1,([true,false,false,true,false,false,true,false,false]) ++ (L),([true,true,false]) ++ (R)⟩ := by rfl

theorem phase3 (n : Nat) : run0 table (3*n) ⟨1,([true,false,false,true,false,false,true,false,false]) ++ (rep [true,false,false] (n)),[]⟩ = some ⟨1,([true,false,false,true,false,false,true,false,false]),(rep [true,true,false] (n))⟩ := by
  simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using sweepL table 1 [true,false,false,true,false,false,true,false,false] [] [true,false,false] [true,true,false] 3 local3 n ([]) ([])

theorem phase4 (n : Nat) : run0 table 9 ⟨1,([true,false,false,true,false,false,true,false,false]),(rep [true,true,false] (n))⟩ = some ⟨1,[],([true,true,false,true,true,false,true,true,false]) ++ (rep [true,true,false] (n))⟩ := by rfl

theorem finalL (n : Nat) : ([] : List Bool) = [] := by
  rfl

theorem finalR (n : Nat) : ([true,true,false,true,true,false,true,true,false]) ++ (rep [true,true,false] (n)) = ([true,true,false,true,true,false,true,true,false]) ++ (rep [true,true,false] (n)) := by
  rfl

theorem growth (n : Nat) : run0 table (29+10*n) (family n) = some (family (n+1)) := by
  have H := (join0 (join0 (join0 (join0 (phase0 n) (phase1 n)) (phase2 n)) (phase3 n)) (phase4 n))
  rw [show 1+7*n+19+3*n+9=29+10*n by omega] at H
  simpa only [family,rep,List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using H

theorem never (m : Machine) (hm : compatible table m) : NeverHalts m :=
  never_of_growth table family 13 (fun n => 29+10*n) entry (by intro n; omega) growth m hm

#print axioms never

end M288

namespace M291

-- 1RB0RB_1RC0LF_0RD0RD_1LD0RA_1LB---_1LE0RB

def table : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 0,true => some (some ⟨false,true,1⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 1,true => some (some ⟨false,false,5⟩)
  | 2,false => some (some ⟨false,true,3⟩)
  | 2,true => some (some ⟨false,true,3⟩)
  | 3,false => some (some ⟨true,false,3⟩)
  | 3,true => some (some ⟨false,true,0⟩)
  | 4,false => some (some ⟨true,false,1⟩)
  | 5,false => some (some ⟨true,false,4⟩)
  | 5,true => some (some ⟨false,true,1⟩)
  | _,_ => none

def family (n : Nat) : Z0 := ⟨1,([false,true]) ++ (rep [false,false,true,false,false,true] (n)),[]⟩

theorem entry : run0 table 1 ⟨0,[],[]⟩ = some (family 0) := by rfl

theorem phase0 (n : Nat) : run0 table 6 ⟨1,([false,true]) ++ (rep [false,false,true,false,false,true] (n)),[]⟩ = some ⟨1,([true,false,false,true]) ++ (rep [false,false,true,false,false,true] (n)),[]⟩ := by rfl

theorem local1 (L R : List Bool) : run0 table 6 ⟨1,([true,false,false,true]) ++ ([false,false,true,false,false,true]) ++ (L),(R)⟩ = some ⟨1,([true,false,false,true]) ++ (L),([true,true,false,true,true,false]) ++ (R)⟩ := by rfl

theorem phase1 (n : Nat) : run0 table (6*n) ⟨1,([true,false,false,true]) ++ (rep [false,false,true,false,false,true] (n)),[]⟩ = some ⟨1,([true,false,false,true]),(rep [true,true,false,true,true,false] (n))⟩ := by
  simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using sweepL table 1 [true,false,false,true] [] [false,false,true,false,false,true] [true,true,false,true,true,false] 6 local1 n ([]) ([])

theorem phase2 (n : Nat) : run0 table 7 ⟨1,([true,false,false,true]),(rep [true,true,false,true,true,false] (n))⟩ = some ⟨2,([true,true]),([true,false,true,true,false]) ++ (rep [true,true,false,true,true,false] (n))⟩ := by rfl

theorem local3 (L R : List Bool) : run0 table 30 ⟨2,([true]) ++ (L),([true,false,true,true,false]) ++ ([true,true,false,true,true,false]) ++ (R)⟩ = some ⟨2,([true]) ++ ([true,false,false,true,false,false]) ++ (L),([true,false,true,true,false]) ++ (R)⟩ := by rfl

theorem phase3 (n : Nat) : run0 table (30*n) ⟨2,([true,true]),([true,false,true,true,false]) ++ (rep [true,true,false,true,true,false] (n))⟩ = some ⟨2,([true]) ++ (rep [true,false,false,true,false,false] (n)) ++ ([true]),([true,false,true,true,false])⟩ := by
  simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using sweepR table 2 [true] [true,false,true,true,false] [true,true,false,true,true,false] [true,false,false,true,false,false] 30 local3 n (([true])) ([])

theorem phase4 (n : Nat) : run0 table 18 ⟨2,([true]) ++ (rep [true,false,false,true,false,false] (n)) ++ ([true]),([true,false,true,true,false])⟩ = some ⟨1,([false,true,false,false,true,false,false]) ++ (rep [true,false,false,true,false,false] (n)) ++ ([true]),[]⟩ := by rfl

theorem finalL (n : Nat) : ([false,true,false,false,true,false,false]) ++ (rep [true,false,false,true,false,false] (n)) ++ ([true]) = ([false,true,false,false,true,false,false,true]) ++ (rep [false,false,true,false,false,true] (n)) := by
  calc
    _ = ([false,true,false,false,true,false,false,true]) ++ (rep [false,false,true,false,false,true] (n)) := by symm; simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using moveCut (([false,true,false,false,true,false,false])) ([]) [false,false,true,false,false] true n

theorem finalR (n : Nat) : ([] : List Bool) = [] := by
  rfl

theorem growth (n : Nat) : run0 table (31+36*n) (family n) = some (family (n+1)) := by
  have H := (join0 (join0 (join0 (join0 (phase0 n) (phase1 n)) (phase2 n)) (phase3 n)) (phase4 n))
  rw [finalL n] at H
  rw [show 6+6*n+7+30*n+18=31+36*n by omega] at H
  simpa only [family,rep,List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using H

theorem never (m : Machine) (hm : compatible table m) : NeverHalts m :=
  never_of_growth table family 1 (fun n => 31+36*n) entry (by intro n; omega) growth m hm

#print axioms never

end M291

namespace M292

-- 1RB0RB_1RC0LF_0RD0RD_1LD0RA_1LB---_1LE0RE

def table : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 0,true => some (some ⟨false,true,1⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 1,true => some (some ⟨false,false,5⟩)
  | 2,false => some (some ⟨false,true,3⟩)
  | 2,true => some (some ⟨false,true,3⟩)
  | 3,false => some (some ⟨true,false,3⟩)
  | 3,true => some (some ⟨false,true,0⟩)
  | 4,false => some (some ⟨true,false,1⟩)
  | 5,false => some (some ⟨true,false,4⟩)
  | 5,true => some (some ⟨false,true,4⟩)
  | _,_ => none

def family (n : Nat) : Z0 := ⟨1,([false,true]) ++ (rep [false,false,true,false,false,true] (n)),[]⟩

theorem entry : run0 table 1 ⟨0,[],[]⟩ = some (family 0) := by rfl

theorem phase0 (n : Nat) : run0 table 6 ⟨1,([false,true]) ++ (rep [false,false,true,false,false,true] (n)),[]⟩ = some ⟨1,([true,false,false,true]) ++ (rep [false,false,true,false,false,true] (n)),[]⟩ := by rfl

theorem local1 (L R : List Bool) : run0 table 6 ⟨1,([true,false,false,true]) ++ ([false,false,true,false,false,true]) ++ (L),(R)⟩ = some ⟨1,([true,false,false,true]) ++ (L),([true,true,false,true,true,false]) ++ (R)⟩ := by rfl

theorem phase1 (n : Nat) : run0 table (6*n) ⟨1,([true,false,false,true]) ++ (rep [false,false,true,false,false,true] (n)),[]⟩ = some ⟨1,([true,false,false,true]),(rep [true,true,false,true,true,false] (n))⟩ := by
  simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using sweepL table 1 [true,false,false,true] [] [false,false,true,false,false,true] [true,true,false,true,true,false] 6 local1 n ([]) ([])

theorem phase2 (n : Nat) : run0 table 7 ⟨1,([true,false,false,true]),(rep [true,true,false,true,true,false] (n))⟩ = some ⟨2,([true,true]),([true,false,true,true,false]) ++ (rep [true,true,false,true,true,false] (n))⟩ := by rfl

theorem local3 (L R : List Bool) : run0 table 14 ⟨2,([true]) ++ (L),([true,false,true,true,false]) ++ ([true,true,false,true,true,false]) ++ (R)⟩ = some ⟨2,([true]) ++ ([true,false,false,true,false,false]) ++ (L),([true,false,true,true,false]) ++ (R)⟩ := by rfl

theorem phase3 (n : Nat) : run0 table (14*n) ⟨2,([true,true]),([true,false,true,true,false]) ++ (rep [true,true,false,true,true,false] (n))⟩ = some ⟨2,([true]) ++ (rep [true,false,false,true,false,false] (n)) ++ ([true]),([true,false,true,true,false])⟩ := by
  simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using sweepR table 2 [true] [true,false,true,true,false] [true,true,false,true,true,false] [true,false,false,true,false,false] 14 local3 n (([true])) ([])

theorem phase4 (n : Nat) : run0 table 10 ⟨2,([true]) ++ (rep [true,false,false,true,false,false] (n)) ++ ([true]),([true,false,true,true,false])⟩ = some ⟨1,([false,true,false,false,true,false,false]) ++ (rep [true,false,false,true,false,false] (n)) ++ ([true]),[]⟩ := by rfl

theorem finalL (n : Nat) : ([false,true,false,false,true,false,false]) ++ (rep [true,false,false,true,false,false] (n)) ++ ([true]) = ([false,true,false,false,true,false,false,true]) ++ (rep [false,false,true,false,false,true] (n)) := by
  calc
    _ = ([false,true,false,false,true,false,false,true]) ++ (rep [false,false,true,false,false,true] (n)) := by symm; simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using moveCut (([false,true,false,false,true,false,false])) ([]) [false,false,true,false,false] true n

theorem finalR (n : Nat) : ([] : List Bool) = [] := by
  rfl

theorem growth (n : Nat) : run0 table (23+20*n) (family n) = some (family (n+1)) := by
  have H := (join0 (join0 (join0 (join0 (phase0 n) (phase1 n)) (phase2 n)) (phase3 n)) (phase4 n))
  rw [finalL n] at H
  rw [show 6+6*n+7+14*n+10=23+20*n by omega] at H
  simpa only [family,rep,List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using H

theorem never (m : Machine) (hm : compatible table m) : NeverHalts m :=
  never_of_growth table family 1 (fun n => 23+20*n) entry (by intro n; omega) growth m hm

#print axioms never

end M292

namespace M295

-- 1RB0RB_1RC0LF_0RD1RC_1LD0RA_1LB---_1LE0RF

def table : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 0,true => some (some ⟨false,true,1⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 1,true => some (some ⟨false,false,5⟩)
  | 2,false => some (some ⟨false,true,3⟩)
  | 2,true => some (some ⟨true,true,2⟩)
  | 3,false => some (some ⟨true,false,3⟩)
  | 3,true => some (some ⟨false,true,0⟩)
  | 4,false => some (some ⟨true,false,1⟩)
  | 5,false => some (some ⟨true,false,4⟩)
  | 5,true => some (some ⟨false,true,5⟩)
  | _,_ => none

def family (n : Nat) : Z0 := ⟨5,[],([false,true,true,true,true,true,true,true,true,true,true]) ++ (rep [true,true,true,true,true,true,true,true,true,true,true,true] (n)) ++ ([false])⟩

theorem entry : run0 table 96 ⟨0,[],[]⟩ = some (family 0) := by rfl

theorem phase0 (n : Nat) : run0 table 3 ⟨5,[],([false,true,true,true,true,true,true,true,true,true,true]) ++ (rep [true,true,true,true,true,true,true,true,true,true,true,true] (n)) ++ ([false])⟩ = some ⟨2,([true,true]),([true,false,true,true,true,true,true,true,true,true,true,true]) ++ (rep [true,true,true,true,true,true,true,true,true,true,true,true] (n)) ++ ([false])⟩ := by rfl

theorem local1 (L R : List Bool) : run0 table 36 ⟨2,([true]) ++ (L),([true,false,true,true,true,true,true,true,true,true,true,true]) ++ ([true,true,true,true,true,true,true,true,true,true,true,true]) ++ (R)⟩ = some ⟨2,([true]) ++ ([true,true,true,true,true,true,true,true,true,true,true,true]) ++ (L),([true,false,true,true,true,true,true,true,true,true,true,true]) ++ (R)⟩ := by rfl

theorem phase1 (n : Nat) : run0 table (36*n) ⟨2,([true,true]),([true,false,true,true,true,true,true,true,true,true,true,true]) ++ (rep [true,true,true,true,true,true,true,true,true,true,true,true] (n)) ++ ([false])⟩ = some ⟨2,([true]) ++ (rep [true,true,true,true,true,true,true,true,true,true,true,true] (n)) ++ ([true]),([true,false,true,true,true,true,true,true,true,true,true,true,false])⟩ := by
  simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using sweepR table 2 [true] [true,false,true,true,true,true,true,true,true,true,true,true] [true,true,true,true,true,true,true,true,true,true,true,true] [true,true,true,true,true,true,true,true,true,true,true,true] 36 local1 n (([true])) (([false]))

theorem phase2 (n : Nat) : run0 table 42 ⟨2,([true]) ++ (rep [true,true,true,true,true,true,true,true,true,true,true,true] (n)) ++ ([true]),([true,false,true,true,true,true,true,true,true,true,true,true,false])⟩ = some ⟨5,([false,false,true,true,true,true,true,true,true,true,true,true,true]) ++ (rep [true,true,true,true,true,true,true,true,true,true,true,true] (n)) ++ ([true]),([false,true,true,false])⟩ := by rfl

theorem local3 (L R : List Bool) : run0 table 24 ⟨5,([false,false,true,true,true,true,true,true,true,true,true,true,true]) ++ ([true,true,true,true,true,true,true,true,true,true,true,true]) ++ (L),(R)⟩ = some ⟨5,([false,false,true,true,true,true,true,true,true,true,true,true,true]) ++ (L),([true,true,true,true,true,true,true,true,true,true,true,true]) ++ (R)⟩ := by rfl

theorem phase3 (n : Nat) : run0 table (24*n) ⟨5,([false,false,true,true,true,true,true,true,true,true,true,true,true]) ++ (rep [true,true,true,true,true,true,true,true,true,true,true,true] (n)) ++ ([true]),([false,true,true,false])⟩ = some ⟨5,([false,false,true,true,true,true,true,true,true,true,true,true,true,true]),(rep [true,true,true,true,true,true,true,true,true,true,true,true] (n)) ++ ([false,true,true,false])⟩ := by
  simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using sweepL table 5 [false,false,true,true,true,true,true,true,true,true,true,true,true] [] [true,true,true,true,true,true,true,true,true,true,true,true] [true,true,true,true,true,true,true,true,true,true,true,true] 24 local3 n (([true])) (([false,true,true,false]))

theorem phase4 (n : Nat) : run0 table 27 ⟨5,([false,false,true,true,true,true,true,true,true,true,true,true,true,true]),(rep [true,true,true,true,true,true,true,true,true,true,true,true] (n)) ++ ([false,true,true,false])⟩ = some ⟨2,([true,true]),([true,true,true,true,true,true,true,true,true,true,true,true,true]) ++ (rep [true,true,true,true,true,true,true,true,true,true,true,true] (n)) ++ ([false,true,true,false])⟩ := by rfl

theorem local5 (L R : List Bool) : run0 table 12 ⟨2,([true]) ++ (L),([true,true,true,true,true,true,true,true,true,true,true,true,true]) ++ ([true,true,true,true,true,true,true,true,true,true,true,true]) ++ (R)⟩ = some ⟨2,([true]) ++ ([true,true,true,true,true,true,true,true,true,true,true,true]) ++ (L),([true,true,true,true,true,true,true,true,true,true,true,true,true]) ++ (R)⟩ := by rfl

theorem phase5 (n : Nat) : run0 table (12*n) ⟨2,([true,true]),([true,true,true,true,true,true,true,true,true,true,true,true,true]) ++ (rep [true,true,true,true,true,true,true,true,true,true,true,true] (n)) ++ ([false,true,true,false])⟩ = some ⟨2,([true]) ++ (rep [true,true,true,true,true,true,true,true,true,true,true,true] (n)) ++ ([true]),([true,true,true,true,true,true,true,true,true,true,true,true,true,false,true,true,false])⟩ := by
  simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using sweepR table 2 [true] [true,true,true,true,true,true,true,true,true,true,true,true,true] [true,true,true,true,true,true,true,true,true,true,true,true] [true,true,true,true,true,true,true,true,true,true,true,true] 12 local5 n (([true])) (([false,true,true,false]))

theorem phase6 (n : Nat) : run0 table 75 ⟨2,([true]) ++ (rep [true,true,true,true,true,true,true,true,true,true,true,true] (n)) ++ ([true]),([true,true,true,true,true,true,true,true,true,true,true,true,true,false,true,true,false])⟩ = some ⟨5,([false,false,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true]) ++ (rep [true,true,true,true,true,true,true,true,true,true,true,true] (n)) ++ ([true]),([false])⟩ := by rfl

theorem local7 (L R : List Bool) : run0 table 24 ⟨5,([false,false,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true]) ++ ([true,true,true,true,true,true,true,true,true,true,true,true]) ++ (L),(R)⟩ = some ⟨5,([false,false,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true]) ++ (L),([true,true,true,true,true,true,true,true,true,true,true,true]) ++ (R)⟩ := by rfl

theorem phase7 (n : Nat) : run0 table (24*n) ⟨5,([false,false,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true]) ++ (rep [true,true,true,true,true,true,true,true,true,true,true,true] (n)) ++ ([true]),([false])⟩ = some ⟨5,([false,false,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true]),(rep [true,true,true,true,true,true,true,true,true,true,true,true] (n)) ++ ([false])⟩ := by
  simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using sweepL table 5 [false,false,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true] [] [true,true,true,true,true,true,true,true,true,true,true,true] [true,true,true,true,true,true,true,true,true,true,true,true] 24 local7 n (([true])) (([false]))

theorem phase8 (n : Nat) : run0 table 43 ⟨5,([false,false,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true]),(rep [true,true,true,true,true,true,true,true,true,true,true,true] (n)) ++ ([false])⟩ = some ⟨5,[],([false,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true]) ++ (rep [true,true,true,true,true,true,true,true,true,true,true,true] (n)) ++ ([false])⟩ := by rfl

theorem finalL (n : Nat) : ([] : List Bool) = [] := by
  rfl

theorem finalR (n : Nat) : ([false,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true]) ++ (rep [true,true,true,true,true,true,true,true,true,true,true,true] (n)) ++ ([false]) = ([false,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true]) ++ (rep [true,true,true,true,true,true,true,true,true,true,true,true] (n)) ++ ([false]) := by
  rfl

theorem growth (n : Nat) : run0 table (190+96*n) (family n) = some (family (n+1)) := by
  have H := (join0 (join0 (join0 (join0 (join0 (join0 (join0 (join0 (phase0 n) (phase1 n)) (phase2 n)) (phase3 n)) (phase4 n)) (phase5 n)) (phase6 n)) (phase7 n)) (phase8 n))
  rw [show 3+36*n+42+24*n+27+12*n+75+24*n+43=190+96*n by omega] at H
  simpa only [family,rep,List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using H

theorem never (m : Machine) (hm : compatible table m) : NeverHalts m :=
  never_of_growth table family 96 (fun n => 190+96*n) entry (by intro n; omega) growth m hm

#print axioms never

end M295

end BB6.Agent11Raw39B0RBPumps
