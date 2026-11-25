import SweepPumping
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedVariables false
namespace BB6.Agent11Raw39B1RCPumps
open BB6Coverage BB6Coverage.Agent31Pump


namespace M293

-- 1RB1RC_1RC1LF_0RD0LF_1LD0RA_0LB---_0LE1LE

def table : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 0,true => some (some ⟨true,true,2⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 1,true => some (some ⟨true,false,5⟩)
  | 2,false => some (some ⟨false,true,3⟩)
  | 2,true => some (some ⟨false,false,5⟩)
  | 3,false => some (some ⟨true,false,3⟩)
  | 3,true => some (some ⟨false,true,0⟩)
  | 4,false => some (some ⟨false,false,1⟩)
  | 5,false => some (some ⟨false,false,4⟩)
  | 5,true => some (some ⟨true,false,4⟩)
  | _,_ => none

def family (n : Nat) : Z0 := ⟨5,[],([true,false,true]) ++ (rep [true,false,true,true,false,false,true,false,false,true,false,true] (n)) ++ ([false])⟩

theorem entry : run0 table 11 ⟨0,[],[]⟩ = some (family 0) := by rfl

theorem phase0 (n : Nat) : run0 table 12 ⟨5,[],([true,false,true]) ++ (rep [true,false,true,true,false,false,true,false,false,true,false,true] (n)) ++ ([false])⟩ = some ⟨2,([false,true]),([true,false,true,false,true]) ++ (rep [true,false,true,true,false,false,true,false,false,true,false,true] (n)) ++ ([false])⟩ := by rfl

theorem local1 (L R : List Bool) : run0 table 44 ⟨2,([false]) ++ (L),([true,false,true,false,true]) ++ ([true,false,true,true,false,false,true,false,false,true,false,true]) ++ (R)⟩ = some ⟨2,([false]) ++ ([true,false,true,true,false,true,false,false,true,false,false,true]) ++ (L),([true,false,true,false,true]) ++ (R)⟩ := by rfl

theorem phase1 (n : Nat) : run0 table (44*n) ⟨2,([false,true]),([true,false,true,false,true]) ++ (rep [true,false,true,true,false,false,true,false,false,true,false,true] (n)) ++ ([false])⟩ = some ⟨2,([false]) ++ (rep [true,false,true,true,false,true,false,false,true,false,false,true] (n)) ++ ([true]),([true,false,true,false,true,false])⟩ := by
  simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using sweepR table 2 [false] [true,false,true,false,true] [true,false,true,true,false,false,true,false,false,true,false,true] [true,false,true,true,false,true,false,false,true,false,false,true] 44 local1 n (([true])) (([false]))

theorem phase2 (n : Nat) : run0 table 20 ⟨2,([false]) ++ (rep [true,false,true,true,false,true,false,false,true,false,false,true] (n)) ++ ([true]),([true,false,true,false,true,false])⟩ = some ⟨5,([true,false,true,false,false,true,false,false,true]) ++ (rep [true,false,true,true,false,true,false,false,true,false,false,true] (n)) ++ ([true]),([false])⟩ := by rfl

theorem local3 (L R : List Bool) : run0 table 12 ⟨5,([true,false,true,false,false,true,false,false,true]) ++ ([true,false,true,true,false,true,false,false,true,false,false,true]) ++ (L),(R)⟩ = some ⟨5,([true,false,true,false,false,true,false,false,true]) ++ (L),([true,false,true,true,false,false,true,false,false,true,false,true]) ++ (R)⟩ := by rfl

theorem phase3 (n : Nat) : run0 table (12*n) ⟨5,([true,false,true,false,false,true,false,false,true]) ++ (rep [true,false,true,true,false,true,false,false,true,false,false,true] (n)) ++ ([true]),([false])⟩ = some ⟨5,([true,false,true,false,false,true,false,false,true,true]),(rep [true,false,true,true,false,false,true,false,false,true,false,true] (n)) ++ ([false])⟩ := by
  simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using sweepL table 5 [true,false,true,false,false,true,false,false,true] [] [true,false,true,true,false,true,false,false,true,false,false,true] [true,false,true,true,false,false,true,false,false,true,false,true] 12 local3 n (([true])) (([false]))

theorem phase4 (n : Nat) : run0 table 12 ⟨5,([true,false,true,false,false,true,false,false,true,true]),(rep [true,false,true,true,false,false,true,false,false,true,false,true] (n)) ++ ([false])⟩ = some ⟨2,([false,true]),([true,true,false,false,true,false,false,true,false,true]) ++ (rep [true,false,true,true,false,false,true,false,false,true,false,true] (n)) ++ ([false])⟩ := by rfl

theorem local5 (L R : List Bool) : run0 table 44 ⟨2,([false]) ++ (L),([true,true,false,false,true,false,false,true,false,true]) ++ ([true,false,true,true,false,false,true,false,false,true,false,true]) ++ (R)⟩ = some ⟨2,([false]) ++ ([true,false,false,true,false,false,true,true,false,true,true,false]) ++ (L),([true,true,false,false,true,false,false,true,false,true]) ++ (R)⟩ := by rfl

theorem phase5 (n : Nat) : run0 table (44*n) ⟨2,([false,true]),([true,true,false,false,true,false,false,true,false,true]) ++ (rep [true,false,true,true,false,false,true,false,false,true,false,true] (n)) ++ ([false])⟩ = some ⟨2,([false]) ++ (rep [true,false,false,true,false,false,true,true,false,true,true,false] (n)) ++ ([true]),([true,true,false,false,true,false,false,true,false,true,false])⟩ := by
  simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using sweepR table 2 [false] [true,true,false,false,true,false,false,true,false,true] [true,false,true,true,false,false,true,false,false,true,false,true] [true,false,false,true,false,false,true,true,false,true,true,false] 44 local5 n (([true])) (([false]))

theorem phase6 (n : Nat) : run0 table 51 ⟨2,([false]) ++ (rep [true,false,false,true,false,false,true,true,false,true,true,false] (n)) ++ ([true]),([true,true,false,false,true,false,false,true,false,true,false])⟩ = some ⟨5,([true,false,true,false,false,true,false,false,true,true,false,true,true,false]) ++ (rep [true,false,false,true,false,false,true,true,false,true,true,false] (n)) ++ ([true]),([false])⟩ := by rfl

theorem local7 (L R : List Bool) : run0 table 12 ⟨5,([true,false,true,false,false,true,false,false,true,true,false,true,true,false]) ++ ([true,false,false,true,false,false,true,true,false,true,true,false]) ++ (L),(R)⟩ = some ⟨5,([true,false,true,false,false,true,false,false,true,true,false,true,true,false]) ++ (L),([true,false,true,true,false,false,true,false,false,true,false,true]) ++ (R)⟩ := by rfl

theorem phase7 (n : Nat) : run0 table (12*n) ⟨5,([true,false,true,false,false,true,false,false,true,true,false,true,true,false]) ++ (rep [true,false,false,true,false,false,true,true,false,true,true,false] (n)) ++ ([true]),([false])⟩ = some ⟨5,([true,false,true,false,false,true,false,false,true,true,false,true,true,false,true]),(rep [true,false,true,true,false,false,true,false,false,true,false,true] (n)) ++ ([false])⟩ := by
  simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using sweepL table 5 [true,false,true,false,false,true,false,false,true,true,false,true,true,false] [] [true,false,false,true,false,false,true,true,false,true,true,false] [true,false,true,true,false,false,true,false,false,true,false,true] 12 local7 n (([true])) (([false]))

theorem phase8 (n : Nat) : run0 table 15 ⟨5,([true,false,true,false,false,true,false,false,true,true,false,true,true,false,true]),(rep [true,false,true,true,false,false,true,false,false,true,false,true] (n)) ++ ([false])⟩ = some ⟨5,[],([true,false,true,true,false,true,true,false,false,true,false,false,true,false,true]) ++ (rep [true,false,true,true,false,false,true,false,false,true,false,true] (n)) ++ ([false])⟩ := by rfl

theorem finalL (n : Nat) : ([] : List Bool) = [] := by
  rfl

theorem finalR (n : Nat) : ([true,false,true,true,false,true,true,false,false,true,false,false,true,false,true]) ++ (rep [true,false,true,true,false,false,true,false,false,true,false,true] (n)) ++ ([false]) = ([true,false,true,true,false,true,true,false,false,true,false,false,true,false,true]) ++ (rep [true,false,true,true,false,false,true,false,false,true,false,true] (n)) ++ ([false]) := by
  rfl

theorem growth (n : Nat) : run0 table (110+112*n) (family n) = some (family (n+1)) := by
  have H := (join0 (join0 (join0 (join0 (join0 (join0 (join0 (join0 (phase0 n) (phase1 n)) (phase2 n)) (phase3 n)) (phase4 n)) (phase5 n)) (phase6 n)) (phase7 n)) (phase8 n))
  rw [show 12+44*n+20+12*n+12+44*n+51+12*n+15=110+112*n by omega] at H
  simpa only [family,rep,List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using H

theorem never (m : Machine) (hm : compatible table m) : NeverHalts m :=
  never_of_growth table family 11 (fun n => 110+112*n) entry (by intro n; omega) growth m hm

#print axioms never

end M293

namespace M295

-- 1RB1RC_1RC1LF_0RD0LF_1LD0RA_0LB---_1RB1LE

def table : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 0,true => some (some ⟨true,true,2⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 1,true => some (some ⟨true,false,5⟩)
  | 2,false => some (some ⟨false,true,3⟩)
  | 2,true => some (some ⟨false,false,5⟩)
  | 3,false => some (some ⟨true,false,3⟩)
  | 3,true => some (some ⟨false,true,0⟩)
  | 4,false => some (some ⟨false,false,1⟩)
  | 5,false => some (some ⟨true,true,1⟩)
  | 5,true => some (some ⟨true,false,4⟩)
  | _,_ => none

def family (n : Nat) : Z0 := ⟨1,([false,true]) ++ (rep [false,false,true,false,false,true] (n)),[]⟩

theorem entry : run0 table 1 ⟨0,[],[]⟩ = some (family 0) := by rfl

theorem phase0 (n : Nat) : run0 table 7 ⟨1,([false,true]) ++ (rep [false,false,true,false,false,true] (n)),[]⟩ = some ⟨5,([true,false,true]) ++ (rep [false,false,true,false,false,true] (n)),([false])⟩ := by rfl

theorem local1 (L R : List Bool) : run0 table 10 ⟨5,([true,false,true]) ++ ([false,false,true,false,false,true]) ++ (L),(R)⟩ = some ⟨5,([true,false,true]) ++ (L),([true,false,true,true,false,true]) ++ (R)⟩ := by rfl

theorem phase1 (n : Nat) : run0 table (10*n) ⟨5,([true,false,true]) ++ (rep [false,false,true,false,false,true] (n)),([false])⟩ = some ⟨5,([true,false,true]),(rep [true,false,true,true,false,true] (n)) ++ ([false])⟩ := by
  simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using sweepL table 5 [true,false,true] [] [false,false,true,false,false,true] [true,false,true,true,false,true] 10 local1 n ([]) (([false]))

theorem phase2 (n : Nat) : run0 table 8 ⟨5,([true,false,true]),(rep [true,false,true,true,false,true] (n)) ++ ([false])⟩ = some ⟨2,([false,true]),([true,true,false,true]) ++ (rep [true,false,true,true,false,true] (n)) ++ ([false])⟩ := by rfl

theorem local3 (L R : List Bool) : run0 table 6 ⟨2,([false]) ++ (L),([true,true,false,true]) ++ ([true,false,true,true,false,true]) ++ (R)⟩ = some ⟨2,([false]) ++ ([true,false,false,true,false,false]) ++ (L),([true,true,false,true]) ++ (R)⟩ := by rfl

theorem phase3 (n : Nat) : run0 table (6*n) ⟨2,([false,true]),([true,true,false,true]) ++ (rep [true,false,true,true,false,true] (n)) ++ ([false])⟩ = some ⟨2,([false]) ++ (rep [true,false,false,true,false,false] (n)) ++ ([true]),([true,true,false,true,false])⟩ := by
  simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using sweepR table 2 [false] [true,true,false,true] [true,false,true,true,false,true] [true,false,false,true,false,false] 6 local3 n (([true])) (([false]))

theorem phase4 (n : Nat) : run0 table 6 ⟨2,([false]) ++ (rep [true,false,false,true,false,false] (n)) ++ ([true]),([true,true,false,true,false])⟩ = some ⟨1,([false,true,false,false,true,false,false]) ++ (rep [true,false,false,true,false,false] (n)) ++ ([true]),[]⟩ := by rfl

theorem finalL (n : Nat) : ([false,true,false,false,true,false,false]) ++ (rep [true,false,false,true,false,false] (n)) ++ ([true]) = ([false,true,false,false,true,false,false,true]) ++ (rep [false,false,true,false,false,true] (n)) := by
  calc
    _ = ([false,true,false,false,true,false,false,true]) ++ (rep [false,false,true,false,false,true] (n)) := by symm; simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using moveCut (([false,true,false,false,true,false,false])) ([]) [false,false,true,false,false] true n

theorem finalR (n : Nat) : ([] : List Bool) = [] := by
  rfl

theorem growth (n : Nat) : run0 table (21+16*n) (family n) = some (family (n+1)) := by
  have H := (join0 (join0 (join0 (join0 (phase0 n) (phase1 n)) (phase2 n)) (phase3 n)) (phase4 n))
  rw [finalL n] at H
  rw [show 7+10*n+8+6*n+6=21+16*n by omega] at H
  simpa only [family,rep,List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using H

theorem never (m : Machine) (hm : compatible table m) : NeverHalts m :=
  never_of_growth table family 1 (fun n => 21+16*n) entry (by intro n; omega) growth m hm

#print axioms never

end M295

namespace M296

-- 1RB1RC_1RC0RA_0RD0LF_1LD0RA_0LF---_0LA1LE

def table : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 0,true => some (some ⟨true,true,2⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 1,true => some (some ⟨false,true,0⟩)
  | 2,false => some (some ⟨false,true,3⟩)
  | 2,true => some (some ⟨false,false,5⟩)
  | 3,false => some (some ⟨true,false,3⟩)
  | 3,true => some (some ⟨false,true,0⟩)
  | 4,false => some (some ⟨false,false,5⟩)
  | 5,false => some (some ⟨false,false,0⟩)
  | 5,true => some (some ⟨true,false,4⟩)
  | _,_ => none

def family (n : Nat) : Z0 := ⟨4,[],([true,false,true,false]) ++ (rep [true,false,true,false,true,false] (n))⟩

theorem entry : run0 table 11 ⟨0,[],[]⟩ = some (family 0) := by rfl

theorem phase0 (n : Nat) : run0 table 6 ⟨4,[],([true,false,true,false]) ++ (rep [true,false,true,false,true,false] (n))⟩ = some ⟨0,([false,false,false,true,true]),([true,false]) ++ (rep [true,false,true,false,true,false] (n))⟩ := by rfl

theorem local1 (L R : List Bool) : run0 table 6 ⟨0,([false]) ++ (L),([true,false]) ++ ([true,false,true,false,true,false]) ++ (R)⟩ = some ⟨0,([false]) ++ ([false,true,false,true,false,true]) ++ (L),([true,false]) ++ (R)⟩ := by rfl

theorem phase1 (n : Nat) : run0 table (6*n) ⟨0,([false,false,false,true,true]),([true,false]) ++ (rep [true,false,true,false,true,false] (n))⟩ = some ⟨0,([false]) ++ (rep [false,true,false,true,false,true] (n)) ++ ([false,false,true,true]),([true,false])⟩ := by
  simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using sweepR table 0 [false] [true,false] [true,false,true,false,true,false] [false,true,false,true,false,true] 6 local1 n (([false,false,true,true])) ([])

theorem phase2 (n : Nat) : run0 table 10 ⟨0,([false]) ++ (rep [false,true,false,true,false,true] (n)) ++ ([false,false,true,true]),([true,false])⟩ = some ⟨5,([true,false,true,false,true]) ++ (rep [false,true,false,true,false,true] (n)) ++ ([false,false,true,true]),([false])⟩ := by rfl

theorem local3 (L R : List Bool) : run0 table 6 ⟨5,([true,false,true,false,true]) ++ ([false,true,false,true,false,true]) ++ (L),(R)⟩ = some ⟨5,([true,false,true,false,true]) ++ (L),([false,true,false,true,false,true]) ++ (R)⟩ := by rfl

theorem phase3 (n : Nat) : run0 table (6*n) ⟨5,([true,false,true,false,true]) ++ (rep [false,true,false,true,false,true] (n)) ++ ([false,false,true,true]),([false])⟩ = some ⟨5,([true,false,true,false,true,false,false,true,true]),(rep [false,true,false,true,false,true] (n)) ++ ([false])⟩ := by
  simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using sweepL table 5 [true,false,true,false,true] [] [false,true,false,true,false,true] [false,true,false,true,false,true] 6 local3 n (([false,false,true,true])) (([false]))

theorem phase4 (n : Nat) : run0 table 17 ⟨5,([true,false,true,false,true,false,false,true,true]),(rep [false,true,false,true,false,true] (n)) ++ ([false])⟩ = some ⟨4,[],([true,false,true,false,true,false,true,false,true]) ++ (rep [false,true,false,true,false,true] (n)) ++ ([false])⟩ := by rfl

theorem finalL (n : Nat) : ([] : List Bool) = [] := by
  rfl

theorem finalR (n : Nat) : ([true,false,true,false,true,false,true,false,true]) ++ (rep [false,true,false,true,false,true] (n)) ++ ([false]) = ([true,false,true,false,true,false,true,false,true,false]) ++ (rep [true,false,true,false,true,false] (n)) := by
  calc
    _ = ([true,false,true,false,true,false,true,false,true,false]) ++ (rep [true,false,true,false,true,false] (n)) := by symm; simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using moveCut (([true,false,true,false,true,false,true,false,true])) ([]) [true,false,true,false,true] false n

theorem growth (n : Nat) : run0 table (33+12*n) (family n) = some (family (n+1)) := by
  have H := (join0 (join0 (join0 (join0 (phase0 n) (phase1 n)) (phase2 n)) (phase3 n)) (phase4 n))
  rw [finalR n] at H
  rw [show 6+6*n+10+6*n+17=33+12*n by omega] at H
  simpa only [family,rep,List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using H

theorem never (m : Machine) (hm : compatible table m) : NeverHalts m :=
  never_of_growth table family 11 (fun n => 33+12*n) entry (by intro n; omega) growth m hm

#print axioms never

end M296

namespace M297

-- 1RB1RC_1RC1RC_0RD0LF_1LD0RA_0LF---_0LA1LE

def table : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 0,true => some (some ⟨true,true,2⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 1,true => some (some ⟨true,true,2⟩)
  | 2,false => some (some ⟨false,true,3⟩)
  | 2,true => some (some ⟨false,false,5⟩)
  | 3,false => some (some ⟨true,false,3⟩)
  | 3,true => some (some ⟨false,true,0⟩)
  | 4,false => some (some ⟨false,false,5⟩)
  | 5,false => some (some ⟨false,false,0⟩)
  | 5,true => some (some ⟨true,false,4⟩)
  | _,_ => none

def family (n : Nat) : Z0 := ⟨3,([false,false,true,true]) ++ (rep [false,false,true,true] (n)),[]⟩

theorem entry : run0 table 3 ⟨0,[],[]⟩ = some (family 0) := by rfl

theorem local0 (L R : List Bool) : run0 table 12 ⟨3,([false,false,true,true]) ++ ([false,false,true,true]) ++ (L),(R)⟩ = some ⟨3,([false,false,true,true]) ++ (L),([true,false,true,false]) ++ (R)⟩ := by rfl

theorem phase0 (n : Nat) : run0 table (12*n) ⟨3,([false,false,true,true]) ++ (rep [false,false,true,true] (n)),[]⟩ = some ⟨3,([false,false,true,true]),(rep [true,false,true,false] (n))⟩ := by
  simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using sweepL table 3 [false,false,true,true] [] [false,false,true,true] [true,false,true,false] 12 local0 n ([]) ([])

theorem phase1 (n : Nat) : run0 table 12 ⟨3,([false,false,true,true]),(rep [true,false,true,false] (n))⟩ = some ⟨2,([false,true,true]),([true,false,true,false]) ++ (rep [true,false,true,false] (n))⟩ := by rfl

theorem local2 (L R : List Bool) : run0 table 4 ⟨2,([false]) ++ (L),([true,false,true,false]) ++ ([true,false,true,false]) ++ (R)⟩ = some ⟨2,([false]) ++ ([true,true,false,false]) ++ (L),([true,false,true,false]) ++ (R)⟩ := by rfl

theorem phase2 (n : Nat) : run0 table (4*n) ⟨2,([false,true,true]),([true,false,true,false]) ++ (rep [true,false,true,false] (n))⟩ = some ⟨2,([false]) ++ (rep [true,true,false,false] (n)) ++ ([true,true]),([true,false,true,false])⟩ := by
  simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using sweepR table 2 [false] [true,false,true,false] [true,false,true,false] [true,true,false,false] 4 local2 n (([true,true])) ([])

theorem phase3 (n : Nat) : run0 table 5 ⟨2,([false]) ++ (rep [true,true,false,false] (n)) ++ ([true,true]),([true,false,true,false])⟩ = some ⟨3,([false,false,true,true,false,false]) ++ (rep [true,true,false,false] (n)) ++ ([true,true]),[]⟩ := by rfl

theorem finalL (n : Nat) : ([false,false,true,true,false,false]) ++ (rep [true,true,false,false] (n)) ++ ([true,true]) = ([false,false,true,true,false,false,true,true]) ++ (rep [false,false,true,true] (n)) := by
  calc
    _ = ([false,false,true,true,false,false,true]) ++ (rep [true,false,false,true] (n)) ++ ([true]) := by symm; simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using moveCut (([false,false,true,true,false,false])) (([true])) [true,false,false] true n
    _ = ([false,false,true,true,false,false,true,true]) ++ (rep [false,false,true,true] (n)) := by symm; simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using moveCut (([false,false,true,true,false,false,true])) ([]) [false,false,true] true n

theorem finalR (n : Nat) : ([] : List Bool) = [] := by
  rfl

theorem growth (n : Nat) : run0 table (17+16*n) (family n) = some (family (n+1)) := by
  have H := (join0 (join0 (join0 (phase0 n) (phase1 n)) (phase2 n)) (phase3 n))
  rw [finalL n] at H
  rw [show 12*n+12+4*n+5=17+16*n by omega] at H
  simpa only [family,rep,List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using H

theorem never (m : Machine) (hm : compatible table m) : NeverHalts m :=
  never_of_growth table family 3 (fun n => 17+16*n) entry (by intro n; omega) growth m hm

#print axioms never

end M297

namespace M298

-- 1RB1RC_1RC1RF_0RD0LF_1LD0RA_0LF---_0LA1LE

def table : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 0,true => some (some ⟨true,true,2⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 1,true => some (some ⟨true,true,5⟩)
  | 2,false => some (some ⟨false,true,3⟩)
  | 2,true => some (some ⟨false,false,5⟩)
  | 3,false => some (some ⟨true,false,3⟩)
  | 3,true => some (some ⟨false,true,0⟩)
  | 4,false => some (some ⟨false,false,5⟩)
  | 5,false => some (some ⟨false,false,0⟩)
  | 5,true => some (some ⟨true,false,4⟩)
  | _,_ => none

def family (n : Nat) : Z0 := ⟨3,([false,false,true,true]) ++ (rep [false,false,true,true] (n)),[]⟩

theorem entry : run0 table 3 ⟨0,[],[]⟩ = some (family 0) := by rfl

theorem local0 (L R : List Bool) : run0 table 12 ⟨3,([false,false,true,true]) ++ ([false,false,true,true]) ++ (L),(R)⟩ = some ⟨3,([false,false,true,true]) ++ (L),([true,false,true,false]) ++ (R)⟩ := by rfl

theorem phase0 (n : Nat) : run0 table (12*n) ⟨3,([false,false,true,true]) ++ (rep [false,false,true,true] (n)),[]⟩ = some ⟨3,([false,false,true,true]),(rep [true,false,true,false] (n))⟩ := by
  simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using sweepL table 3 [false,false,true,true] [] [false,false,true,true] [true,false,true,false] 12 local0 n ([]) ([])

theorem phase1 (n : Nat) : run0 table 12 ⟨3,([false,false,true,true]),(rep [true,false,true,false] (n))⟩ = some ⟨2,([false,true,true]),([true,false,true,false]) ++ (rep [true,false,true,false] (n))⟩ := by rfl

theorem local2 (L R : List Bool) : run0 table 6 ⟨2,([false]) ++ (L),([true,false,true,false]) ++ ([true,false,true,false]) ++ (R)⟩ = some ⟨2,([false]) ++ ([true,true,false,false]) ++ (L),([true,false,true,false]) ++ (R)⟩ := by rfl

theorem phase2 (n : Nat) : run0 table (6*n) ⟨2,([false,true,true]),([true,false,true,false]) ++ (rep [true,false,true,false] (n))⟩ = some ⟨2,([false]) ++ (rep [true,true,false,false] (n)) ++ ([true,true]),([true,false,true,false])⟩ := by
  simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using sweepR table 2 [false] [true,false,true,false] [true,false,true,false] [true,true,false,false] 6 local2 n (([true,true])) ([])

theorem phase3 (n : Nat) : run0 table 7 ⟨2,([false]) ++ (rep [true,true,false,false] (n)) ++ ([true,true]),([true,false,true,false])⟩ = some ⟨3,([false,false,true,true,false,false]) ++ (rep [true,true,false,false] (n)) ++ ([true,true]),[]⟩ := by rfl

theorem finalL (n : Nat) : ([false,false,true,true,false,false]) ++ (rep [true,true,false,false] (n)) ++ ([true,true]) = ([false,false,true,true,false,false,true,true]) ++ (rep [false,false,true,true] (n)) := by
  calc
    _ = ([false,false,true,true,false,false,true]) ++ (rep [true,false,false,true] (n)) ++ ([true]) := by symm; simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using moveCut (([false,false,true,true,false,false])) (([true])) [true,false,false] true n
    _ = ([false,false,true,true,false,false,true,true]) ++ (rep [false,false,true,true] (n)) := by symm; simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using moveCut (([false,false,true,true,false,false,true])) ([]) [false,false,true] true n

theorem finalR (n : Nat) : ([] : List Bool) = [] := by
  rfl

theorem growth (n : Nat) : run0 table (19+18*n) (family n) = some (family (n+1)) := by
  have H := (join0 (join0 (join0 (phase0 n) (phase1 n)) (phase2 n)) (phase3 n))
  rw [finalL n] at H
  rw [show 12*n+12+6*n+7=19+18*n by omega] at H
  simpa only [family,rep,List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using H

theorem never (m : Machine) (hm : compatible table m) : NeverHalts m :=
  never_of_growth table family 3 (fun n => 19+18*n) entry (by intro n; omega) growth m hm

#print axioms never

end M298

namespace M303

-- 1RB1RC_1RC0LC_0RD0LF_1LD0RA_0LF---_1LC1LE

def table : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 0,true => some (some ⟨true,true,2⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 1,true => some (some ⟨false,false,2⟩)
  | 2,false => some (some ⟨false,true,3⟩)
  | 2,true => some (some ⟨false,false,5⟩)
  | 3,false => some (some ⟨true,false,3⟩)
  | 3,true => some (some ⟨false,true,0⟩)
  | 4,false => some (some ⟨false,false,5⟩)
  | 5,false => some (some ⟨true,false,2⟩)
  | 5,true => some (some ⟨true,false,4⟩)
  | _,_ => none

def family (n : Nat) : Z0 := ⟨2,[],([true,false,true,false,true,false]) ++ (rep [true,false,true,false] (n))⟩

theorem entry : run0 table 13 ⟨0,[],[]⟩ = some (family 0) := by rfl

theorem phase0 (n : Nat) : run0 table 1 ⟨2,[],([true,false,true,false,true,false]) ++ (rep [true,false,true,false] (n))⟩ = some ⟨3,([true,false]),([false,true,false,true,false]) ++ (rep [true,false,true,false] (n))⟩ := by rfl

theorem local1 (L R : List Bool) : run0 table 10 ⟨3,([true,false]) ++ (L),([false,true,false,true,false]) ++ ([true,false,true,false]) ++ (R)⟩ = some ⟨3,([true,false]) ++ ([true,true,false,false]) ++ (L),([false,true,false,true,false]) ++ (R)⟩ := by rfl

theorem phase1 (n : Nat) : run0 table (10*n) ⟨3,([true,false]),([false,true,false,true,false]) ++ (rep [true,false,true,false] (n))⟩ = some ⟨3,([true,false]) ++ (rep [true,true,false,false] (n)),([false,true,false,true,false])⟩ := by
  simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using sweepR table 3 [true,false] [false,true,false,true,false] [true,false,true,false] [true,true,false,false] 10 local1 n ([]) ([])

theorem phase2 (n : Nat) : run0 table 21 ⟨3,([true,false]) ++ (rep [true,true,false,false] (n)),([false,true,false,true,false])⟩ = some ⟨5,([true,false,false,true,true,false,false]) ++ (rep [true,true,false,false] (n)),([false,true,false])⟩ := by rfl

theorem local3 (L R : List Bool) : run0 table 4 ⟨5,([true,false,false,true,true,false,false]) ++ ([true,true,false,false]) ++ (L),(R)⟩ = some ⟨5,([true,false,false,true,true,false,false]) ++ (L),([false,true,false,true]) ++ (R)⟩ := by rfl

theorem phase3 (n : Nat) : run0 table (4*n) ⟨5,([true,false,false,true,true,false,false]) ++ (rep [true,true,false,false] (n)),([false,true,false])⟩ = some ⟨5,([true,false,false,true,true,false,false]),(rep [false,true,false,true] (n)) ++ ([false,true,false])⟩ := by
  simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using sweepL table 5 [true,false,false,true,true,false,false] [] [true,true,false,false] [false,true,false,true] 4 local3 n ([]) (([false,true,false]))

theorem phase4 (n : Nat) : run0 table 7 ⟨5,([true,false,false,true,true,false,false]),(rep [false,true,false,true] (n)) ++ ([false,true,false])⟩ = some ⟨2,[],([true,false,true,false,true,false,true]) ++ (rep [false,true,false,true] (n)) ++ ([false,true,false])⟩ := by rfl

theorem finalL (n : Nat) : ([] : List Bool) = [] := by
  rfl

theorem finalR (n : Nat) : ([true,false,true,false,true,false,true]) ++ (rep [false,true,false,true] (n)) ++ ([false,true,false]) = ([true,false,true,false,true,false,true,false,true,false]) ++ (rep [true,false,true,false] (n)) := by
  calc
    _ = ([true,false,true,false,true,false,true,false]) ++ (rep [true,false,true,false] (n)) ++ ([true,false]) := by symm; simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using moveCut (([true,false,true,false,true,false,true])) (([true,false])) [true,false,true] false n
    _ = ([true,false,true,false,true,false,true,false,true]) ++ (rep [false,true,false,true] (n)) ++ ([false]) := by symm; simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using moveCut (([true,false,true,false,true,false,true,false])) (([false])) [false,true,false] true n
    _ = ([true,false,true,false,true,false,true,false,true,false]) ++ (rep [true,false,true,false] (n)) := by symm; simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using moveCut (([true,false,true,false,true,false,true,false,true])) ([]) [true,false,true] false n

theorem growth (n : Nat) : run0 table (29+14*n) (family n) = some (family (n+1)) := by
  have H := (join0 (join0 (join0 (join0 (phase0 n) (phase1 n)) (phase2 n)) (phase3 n)) (phase4 n))
  rw [finalR n] at H
  rw [show 1+10*n+21+4*n+7=29+14*n by omega] at H
  simpa only [family,rep,List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using H

theorem never (m : Machine) (hm : compatible table m) : NeverHalts m :=
  never_of_growth table family 13 (fun n => 29+14*n) entry (by intro n; omega) growth m hm

#print axioms never

end M303

namespace M312

-- 1RB1RC_1RC1LC_0RD0LF_1LD0RA_1LA---_1RC1LE

def table : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 0,true => some (some ⟨true,true,2⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 1,true => some (some ⟨true,false,2⟩)
  | 2,false => some (some ⟨false,true,3⟩)
  | 2,true => some (some ⟨false,false,5⟩)
  | 3,false => some (some ⟨true,false,3⟩)
  | 3,true => some (some ⟨false,true,0⟩)
  | 4,false => some (some ⟨true,false,0⟩)
  | 5,false => some (some ⟨true,true,2⟩)
  | 5,true => some (some ⟨true,false,4⟩)
  | _,_ => none

def family (n : Nat) : Z0 := ⟨1,([false,true]) ++ (rep [false,false,true,false,false,true] (n)),[]⟩

theorem entry : run0 table 1 ⟨0,[],[]⟩ = some (family 0) := by rfl

theorem phase0 (n : Nat) : run0 table 10 ⟨1,([false,true]) ++ (rep [false,false,true,false,false,true] (n)),[]⟩ = some ⟨2,([true,true]) ++ (rep [false,false,true,false,false,true] (n)),([true,false])⟩ := by rfl

theorem local1 (L R : List Bool) : run0 table 10 ⟨2,([true,true]) ++ ([false,false,true,false,false,true]) ++ (L),(R)⟩ = some ⟨2,([true,true]) ++ (L),([true,true,false,true,true,false]) ++ (R)⟩ := by rfl

theorem phase1 (n : Nat) : run0 table (10*n) ⟨2,([true,true]) ++ (rep [false,false,true,false,false,true] (n)),([true,false])⟩ = some ⟨2,([true,true]),(rep [true,true,false,true,true,false] (n)) ++ ([true,false])⟩ := by
  simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using sweepL table 2 [true,true] [] [false,false,true,false,false,true] [true,true,false,true,true,false] 10 local1 n ([]) (([true,false]))

theorem phase2 (n : Nat) : run0 table 7 ⟨2,([true,true]),(rep [true,true,false,true,true,false] (n)) ++ ([true,false])⟩ = some ⟨2,([false,true]),([true,true,false]) ++ (rep [true,true,false,true,true,false] (n)) ++ ([true,false])⟩ := by rfl

theorem local3 (L R : List Bool) : run0 table 6 ⟨2,([false]) ++ (L),([true,true,false]) ++ ([true,true,false,true,true,false]) ++ (R)⟩ = some ⟨2,([false]) ++ ([true,false,false,true,false,false]) ++ (L),([true,true,false]) ++ (R)⟩ := by rfl

theorem phase3 (n : Nat) : run0 table (6*n) ⟨2,([false,true]),([true,true,false]) ++ (rep [true,true,false,true,true,false] (n)) ++ ([true,false])⟩ = some ⟨2,([false]) ++ (rep [true,false,false,true,false,false] (n)) ++ ([true]),([true,true,false,true,false])⟩ := by
  simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using sweepR table 2 [false] [true,true,false] [true,true,false,true,true,false] [true,false,false,true,false,false] 6 local3 n (([true])) (([true,false]))

theorem phase4 (n : Nat) : run0 table 6 ⟨2,([false]) ++ (rep [true,false,false,true,false,false] (n)) ++ ([true]),([true,true,false,true,false])⟩ = some ⟨1,([false,true,false,false,true,false,false]) ++ (rep [true,false,false,true,false,false] (n)) ++ ([true]),[]⟩ := by rfl

theorem finalL (n : Nat) : ([false,true,false,false,true,false,false]) ++ (rep [true,false,false,true,false,false] (n)) ++ ([true]) = ([false,true,false,false,true,false,false,true]) ++ (rep [false,false,true,false,false,true] (n)) := by
  calc
    _ = ([false,true,false,false,true,false,false,true]) ++ (rep [false,false,true,false,false,true] (n)) := by symm; simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using moveCut (([false,true,false,false,true,false,false])) ([]) [false,false,true,false,false] true n

theorem finalR (n : Nat) : ([] : List Bool) = [] := by
  rfl

theorem growth (n : Nat) : run0 table (23+16*n) (family n) = some (family (n+1)) := by
  have H := (join0 (join0 (join0 (join0 (phase0 n) (phase1 n)) (phase2 n)) (phase3 n)) (phase4 n))
  rw [finalL n] at H
  rw [show 10+10*n+7+6*n+6=23+16*n by omega] at H
  simpa only [family,rep,List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using H

theorem never (m : Machine) (hm : compatible table m) : NeverHalts m :=
  never_of_growth table family 1 (fun n => 23+16*n) entry (by intro n; omega) growth m hm

#print axioms never

end M312

namespace M319

-- 1RB1RC_1RC---_0RD0LF_1LD0RA_1LC1LE_1RB1LE

def table : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 0,true => some (some ⟨true,true,2⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 2,false => some (some ⟨false,true,3⟩)
  | 2,true => some (some ⟨false,false,5⟩)
  | 3,false => some (some ⟨true,false,3⟩)
  | 3,true => some (some ⟨false,true,0⟩)
  | 4,false => some (some ⟨true,false,2⟩)
  | 4,true => some (some ⟨true,false,4⟩)
  | 5,false => some (some ⟨true,true,1⟩)
  | 5,true => some (some ⟨true,false,4⟩)
  | _,_ => none

def family (n : Nat) : Z0 := ⟨1,([false,true,false,false,true,false,false]) ++ (rep [true,false,false] (n)) ++ ([false]),[]⟩

theorem entry : run0 table 40 ⟨0,[],[]⟩ = some (family 0) := by rfl

theorem phase0 (n : Nat) : run0 table 8 ⟨1,([false,true,false,false,true,false,false]) ++ (rep [true,false,false] (n)) ++ ([false]),[]⟩ = some ⟨4,([false,true,false,false,true,false,false]) ++ (rep [true,false,false] (n)) ++ ([false]),([true,false])⟩ := by rfl

theorem local1 (L R : List Bool) : run0 table 7 ⟨4,([false,true,false,false,true,false,false]) ++ ([true,false,false]) ++ (L),(R)⟩ = some ⟨4,([false,true,false,false,true,false,false]) ++ (L),([true,true,false]) ++ (R)⟩ := by rfl

theorem phase1 (n : Nat) : run0 table (7*n) ⟨4,([false,true,false,false,true,false,false]) ++ (rep [true,false,false] (n)) ++ ([false]),([true,false])⟩ = some ⟨4,([false,true,false,false,true,false,false,false]),(rep [true,true,false] (n)) ++ ([true,false])⟩ := by
  simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using sweepL table 4 [false,true,false,false,true,false,false] [] [true,false,false] [true,true,false] 7 local1 n (([false])) (([true,false]))

theorem phase2 (n : Nat) : run0 table 32 ⟨4,([false,true,false,false,true,false,false,false]),(rep [true,true,false] (n)) ++ ([true,false])⟩ = some ⟨2,([false,false]),([true,true,false,true,true,false]) ++ (rep [true,true,false] (n)) ++ ([true,false])⟩ := by rfl

theorem local3 (L R : List Bool) : run0 table 3 ⟨2,([false]) ++ (L),([true,true,false,true,true,false]) ++ ([true,true,false]) ++ (R)⟩ = some ⟨2,([false]) ++ ([true,false,false]) ++ (L),([true,true,false,true,true,false]) ++ (R)⟩ := by rfl

theorem phase3 (n : Nat) : run0 table (3*n) ⟨2,([false,false]),([true,true,false,true,true,false]) ++ (rep [true,true,false] (n)) ++ ([true,false])⟩ = some ⟨2,([false]) ++ (rep [true,false,false] (n)) ++ ([false]),([true,true,false,true,true,false,true,false])⟩ := by
  simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using sweepR table 2 [false] [true,true,false,true,true,false] [true,true,false] [true,false,false] 3 local3 n (([false])) (([true,false]))

theorem phase4 (n : Nat) : run0 table 9 ⟨2,([false]) ++ (rep [true,false,false] (n)) ++ ([false]),([true,true,false,true,true,false,true,false])⟩ = some ⟨1,([false,true,false,false,true,false,false,true,false,false]) ++ (rep [true,false,false] (n)) ++ ([false]),[]⟩ := by rfl

theorem finalL (n : Nat) : ([false,true,false,false,true,false,false,true,false,false]) ++ (rep [true,false,false] (n)) ++ ([false]) = ([false,true,false,false,true,false,false,true,false,false]) ++ (rep [true,false,false] (n)) ++ ([false]) := by
  rfl

theorem finalR (n : Nat) : ([] : List Bool) = [] := by
  rfl

theorem growth (n : Nat) : run0 table (49+10*n) (family n) = some (family (n+1)) := by
  have H := (join0 (join0 (join0 (join0 (phase0 n) (phase1 n)) (phase2 n)) (phase3 n)) (phase4 n))
  rw [show 8+7*n+32+3*n+9=49+10*n by omega] at H
  simpa only [family,rep,List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using H

theorem never (m : Machine) (hm : compatible table m) : NeverHalts m :=
  never_of_growth table family 40 (fun n => 49+10*n) entry (by intro n; omega) growth m hm

#print axioms never

end M319

namespace M322

-- 1RB1RC_1RC0LB_0RD0LF_1LD0RA_1LF---_0LB1LE

def table : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 0,true => some (some ⟨true,true,2⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 1,true => some (some ⟨false,false,1⟩)
  | 2,false => some (some ⟨false,true,3⟩)
  | 2,true => some (some ⟨false,false,5⟩)
  | 3,false => some (some ⟨true,false,3⟩)
  | 3,true => some (some ⟨false,true,0⟩)
  | 4,false => some (some ⟨true,false,5⟩)
  | 5,false => some (some ⟨false,false,1⟩)
  | 5,true => some (some ⟨true,false,4⟩)
  | _,_ => none

def family (n : Nat) : Z0 := ⟨1,([false,true,false,false,true,false,false,true,false,false,true]) ++ (rep [false,false,true,false,false,true,false,false,true] (n)),[]⟩

theorem entry : run0 table 42 ⟨0,[],[]⟩ = some (family 0) := by rfl

theorem phase0 (n : Nat) : run0 table 9 ⟨1,([false,true,false,false,true,false,false,true,false,false,true]) ++ (rep [false,false,true,false,false,true,false,false,true] (n)),[]⟩ = some ⟨5,([true,false,false,true,false,false,true,false,false,true]) ++ (rep [false,false,true,false,false,true,false,false,true] (n)),([true,true,false])⟩ := by rfl

theorem local1 (L R : List Bool) : run0 table 33 ⟨5,([true,false,false,true,false,false,true,false,false,true]) ++ ([false,false,true,false,false,true,false,false,true]) ++ (L),(R)⟩ = some ⟨5,([true,false,false,true,false,false,true,false,false,true]) ++ (L),([false,true,true,false,true,true,false,true,true]) ++ (R)⟩ := by rfl

theorem phase1 (n : Nat) : run0 table (33*n) ⟨5,([true,false,false,true,false,false,true,false,false,true]) ++ (rep [false,false,true,false,false,true,false,false,true] (n)),([true,true,false])⟩ = some ⟨5,([true,false,false,true,false,false,true,false,false,true]),(rep [false,true,true,false,true,true,false,true,true] (n)) ++ ([true,true,false])⟩ := by
  simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using sweepL table 5 [true,false,false,true,false,false,true,false,false,true] [] [false,false,true,false,false,true,false,false,true] [false,true,true,false,true,true,false,true,true] 33 local1 n ([]) (([true,true,false]))

theorem phase2 (n : Nat) : run0 table 37 ⟨5,([true,false,false,true,false,false,true,false,false,true]),(rep [false,true,true,false,true,true,false,true,true] (n)) ++ ([true,true,false])⟩ = some ⟨2,([false,true]),([true,true,false,true,true,false,true,true,false,true,true]) ++ (rep [false,true,true,false,true,true,false,true,true] (n)) ++ ([true,true,false])⟩ := by rfl

theorem local3 (L R : List Bool) : run0 table 9 ⟨2,([false]) ++ (L),([true,true,false,true,true,false,true,true,false,true,true]) ++ ([false,true,true,false,true,true,false,true,true]) ++ (R)⟩ = some ⟨2,([false]) ++ ([true,false,false,true,false,false,true,false,false]) ++ (L),([true,true,false,true,true,false,true,true,false,true,true]) ++ (R)⟩ := by rfl

theorem phase3 (n : Nat) : run0 table (9*n) ⟨2,([false,true]),([true,true,false,true,true,false,true,true,false,true,true]) ++ (rep [false,true,true,false,true,true,false,true,true] (n)) ++ ([true,true,false])⟩ = some ⟨2,([false]) ++ (rep [true,false,false,true,false,false,true,false,false] (n)) ++ ([true]),([true,true,false,true,true,false,true,true,false,true,true,true,true,false])⟩ := by
  simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using sweepR table 2 [false] [true,true,false,true,true,false,true,true,false,true,true] [false,true,true,false,true,true,false,true,true] [true,false,false,true,false,false,true,false,false] 9 local3 n (([true])) (([true,true,false]))

theorem phase4 (n : Nat) : run0 table 10 ⟨2,([false]) ++ (rep [true,false,false,true,false,false,true,false,false] (n)) ++ ([true]),([true,true,false,true,true,false,true,true,false,true,true,true,true,false])⟩ = some ⟨3,([true,false,true,false,false,true,false,false,true,false,false]) ++ (rep [true,false,false,true,false,false,true,false,false] (n)) ++ ([true]),([true,true,true,false])⟩ := by rfl

theorem local5 (L R : List Bool) : run0 table 33 ⟨3,([true,false,true,false,false,true,false,false,true,false,false]) ++ ([true,false,false,true,false,false,true,false,false]) ++ (L),([true,true]) ++ (R)⟩ = some ⟨3,([true,false,true,false,false,true,false,false,true,false,false]) ++ (L),([true,true]) ++ ([true,true,false,true,true,false,true,true,false]) ++ (R)⟩ := by rfl

theorem phase5 (n : Nat) : run0 table (33*n) ⟨3,([true,false,true,false,false,true,false,false,true,false,false]) ++ (rep [true,false,false,true,false,false,true,false,false] (n)) ++ ([true]),([true,true,true,false])⟩ = some ⟨3,([true,false,true,false,false,true,false,false,true,false,false,true]),([true,true]) ++ (rep [true,true,false,true,true,false,true,true,false] (n)) ++ ([true,false])⟩ := by
  simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using sweepL table 3 [true,false,true,false,false,true,false,false,true,false,false] [true,true] [true,false,false,true,false,false,true,false,false] [true,true,false,true,true,false,true,true,false] 33 local5 n (([true])) (([true,false]))

theorem phase6 (n : Nat) : run0 table 51 ⟨3,([true,false,true,false,false,true,false,false,true,false,false,true]),([true,true]) ++ (rep [true,true,false,true,true,false,true,true,false] (n)) ++ ([true,false])⟩ = some ⟨2,([false,true]),([true,true,false,true,true,false,true,true,false,true,true,false,true,true,false]) ++ (rep [true,true,false,true,true,false,true,true,false] (n)) ++ ([true,false])⟩ := by rfl

theorem local7 (L R : List Bool) : run0 table 9 ⟨2,([false]) ++ (L),([true,true,false,true,true,false,true,true,false,true,true,false,true,true,false]) ++ ([true,true,false,true,true,false,true,true,false]) ++ (R)⟩ = some ⟨2,([false]) ++ ([true,false,false,true,false,false,true,false,false]) ++ (L),([true,true,false,true,true,false,true,true,false,true,true,false,true,true,false]) ++ (R)⟩ := by rfl

theorem phase7 (n : Nat) : run0 table (9*n) ⟨2,([false,true]),([true,true,false,true,true,false,true,true,false,true,true,false,true,true,false]) ++ (rep [true,true,false,true,true,false,true,true,false] (n)) ++ ([true,false])⟩ = some ⟨2,([false]) ++ (rep [true,false,false,true,false,false,true,false,false] (n)) ++ ([true]),([true,true,false,true,true,false,true,true,false,true,true,false,true,true,false,true,false])⟩ := by
  simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using sweepR table 2 [false] [true,true,false,true,true,false,true,true,false,true,true,false,true,true,false] [true,true,false,true,true,false,true,true,false] [true,false,false,true,false,false,true,false,false] 9 local7 n (([true])) (([true,false]))

theorem phase8 (n : Nat) : run0 table 18 ⟨2,([false]) ++ (rep [true,false,false,true,false,false,true,false,false] (n)) ++ ([true]),([true,true,false,true,true,false,true,true,false,true,true,false,true,true,false,true,false])⟩ = some ⟨1,([false,true,false,false,true,false,false,true,false,false,true,false,false,true,false,false,true,false,false]) ++ (rep [true,false,false,true,false,false,true,false,false] (n)) ++ ([true]),[]⟩ := by rfl

theorem finalL (n : Nat) : ([false,true,false,false,true,false,false,true,false,false,true,false,false,true,false,false,true,false,false]) ++ (rep [true,false,false,true,false,false,true,false,false] (n)) ++ ([true]) = ([false,true,false,false,true,false,false,true,false,false,true,false,false,true,false,false,true,false,false,true]) ++ (rep [false,false,true,false,false,true,false,false,true] (n)) := by
  calc
    _ = ([false,true,false,false,true,false,false,true,false,false,true,false,false,true,false,false,true,false,false,true]) ++ (rep [false,false,true,false,false,true,false,false,true] (n)) := by symm; simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using moveCut (([false,true,false,false,true,false,false,true,false,false,true,false,false,true,false,false,true,false,false])) ([]) [false,false,true,false,false,true,false,false] true n

theorem finalR (n : Nat) : ([] : List Bool) = [] := by
  rfl

theorem growth (n : Nat) : run0 table (125+84*n) (family n) = some (family (n+1)) := by
  have H := (join0 (join0 (join0 (join0 (join0 (join0 (join0 (join0 (phase0 n) (phase1 n)) (phase2 n)) (phase3 n)) (phase4 n)) (phase5 n)) (phase6 n)) (phase7 n)) (phase8 n))
  rw [finalL n] at H
  rw [show 9+33*n+37+9*n+10+33*n+51+9*n+18=125+84*n by omega] at H
  simpa only [family,rep,List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using H

theorem never (m : Machine) (hm : compatible table m) : NeverHalts m :=
  never_of_growth table family 42 (fun n => 125+84*n) entry (by intro n; omega) growth m hm

#print axioms never

end M322

namespace M323

-- 1RB1RC_1RC1LC_0RD0LF_1LD0RA_1LF---_0LB1LE

def table : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 0,true => some (some ⟨true,true,2⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 1,true => some (some ⟨true,false,2⟩)
  | 2,false => some (some ⟨false,true,3⟩)
  | 2,true => some (some ⟨false,false,5⟩)
  | 3,false => some (some ⟨true,false,3⟩)
  | 3,true => some (some ⟨false,true,0⟩)
  | 4,false => some (some ⟨true,false,5⟩)
  | 5,false => some (some ⟨false,false,1⟩)
  | 5,true => some (some ⟨true,false,4⟩)
  | _,_ => none

def family (n : Nat) : Z0 := ⟨1,([false,true,false,false,true,false,false,true,false,false,true]) ++ (rep [false,false,true,false,false,true,false,false,true] (n)),[]⟩

theorem entry : run0 table 48 ⟨0,[],[]⟩ = some (family 0) := by rfl

theorem phase0 (n : Nat) : run0 table 9 ⟨1,([false,true,false,false,true,false,false,true,false,false,true]) ++ (rep [false,false,true,false,false,true,false,false,true] (n)),[]⟩ = some ⟨5,([true,false,false,true,false,false,true,false,false,true]) ++ (rep [false,false,true,false,false,true,false,false,true] (n)),([true,true,false])⟩ := by rfl

theorem local1 (L R : List Bool) : run0 table 51 ⟨5,([true,false,false,true,false,false,true,false,false,true]) ++ ([false,false,true,false,false,true,false,false,true]) ++ (L),(R)⟩ = some ⟨5,([true,false,false,true,false,false,true,false,false,true]) ++ (L),([false,true,true,false,true,true,false,true,true]) ++ (R)⟩ := by rfl

theorem phase1 (n : Nat) : run0 table (51*n) ⟨5,([true,false,false,true,false,false,true,false,false,true]) ++ (rep [false,false,true,false,false,true,false,false,true] (n)),([true,true,false])⟩ = some ⟨5,([true,false,false,true,false,false,true,false,false,true]),(rep [false,true,true,false,true,true,false,true,true] (n)) ++ ([true,true,false])⟩ := by
  simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using sweepL table 5 [true,false,false,true,false,false,true,false,false,true] [] [false,false,true,false,false,true,false,false,true] [false,true,true,false,true,true,false,true,true] 51 local1 n ([]) (([true,true,false]))

theorem phase2 (n : Nat) : run0 table 55 ⟨5,([true,false,false,true,false,false,true,false,false,true]),(rep [false,true,true,false,true,true,false,true,true] (n)) ++ ([true,true,false])⟩ = some ⟨2,([false,true]),([true,true,false,true,true,false,true,true,false,true,true]) ++ (rep [false,true,true,false,true,true,false,true,true] (n)) ++ ([true,true,false])⟩ := by rfl

theorem local3 (L R : List Bool) : run0 table 9 ⟨2,([false]) ++ (L),([true,true,false,true,true,false,true,true,false,true,true]) ++ ([false,true,true,false,true,true,false,true,true]) ++ (R)⟩ = some ⟨2,([false]) ++ ([true,false,false,true,false,false,true,false,false]) ++ (L),([true,true,false,true,true,false,true,true,false,true,true]) ++ (R)⟩ := by rfl

theorem phase3 (n : Nat) : run0 table (9*n) ⟨2,([false,true]),([true,true,false,true,true,false,true,true,false,true,true]) ++ (rep [false,true,true,false,true,true,false,true,true] (n)) ++ ([true,true,false])⟩ = some ⟨2,([false]) ++ (rep [true,false,false,true,false,false,true,false,false] (n)) ++ ([true]),([true,true,false,true,true,false,true,true,false,true,true,true,true,false])⟩ := by
  simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using sweepR table 2 [false] [true,true,false,true,true,false,true,true,false,true,true] [false,true,true,false,true,true,false,true,true] [true,false,false,true,false,false,true,false,false] 9 local3 n (([true])) (([true,true,false]))

theorem phase4 (n : Nat) : run0 table 10 ⟨2,([false]) ++ (rep [true,false,false,true,false,false,true,false,false] (n)) ++ ([true]),([true,true,false,true,true,false,true,true,false,true,true,true,true,false])⟩ = some ⟨3,([true,false,true,false,false,true,false,false,true,false,false]) ++ (rep [true,false,false,true,false,false,true,false,false] (n)) ++ ([true]),([true,true,true,false])⟩ := by rfl

theorem local5 (L R : List Bool) : run0 table 51 ⟨3,([true,false,true,false,false,true,false,false,true,false,false]) ++ ([true,false,false,true,false,false,true,false,false]) ++ (L),([true,true]) ++ (R)⟩ = some ⟨3,([true,false,true,false,false,true,false,false,true,false,false]) ++ (L),([true,true]) ++ ([true,true,false,true,true,false,true,true,false]) ++ (R)⟩ := by rfl

theorem phase5 (n : Nat) : run0 table (51*n) ⟨3,([true,false,true,false,false,true,false,false,true,false,false]) ++ (rep [true,false,false,true,false,false,true,false,false] (n)) ++ ([true]),([true,true,true,false])⟩ = some ⟨3,([true,false,true,false,false,true,false,false,true,false,false,true]),([true,true]) ++ (rep [true,true,false,true,true,false,true,true,false] (n)) ++ ([true,false])⟩ := by
  simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using sweepL table 3 [true,false,true,false,false,true,false,false,true,false,false] [true,true] [true,false,false,true,false,false,true,false,false] [true,true,false,true,true,false,true,true,false] 51 local5 n (([true])) (([true,false]))

theorem phase6 (n : Nat) : run0 table 75 ⟨3,([true,false,true,false,false,true,false,false,true,false,false,true]),([true,true]) ++ (rep [true,true,false,true,true,false,true,true,false] (n)) ++ ([true,false])⟩ = some ⟨2,([false,true]),([true,true,false,true,true,false,true,true,false,true,true,false,true,true,false]) ++ (rep [true,true,false,true,true,false,true,true,false] (n)) ++ ([true,false])⟩ := by rfl

theorem local7 (L R : List Bool) : run0 table 9 ⟨2,([false]) ++ (L),([true,true,false,true,true,false,true,true,false,true,true,false,true,true,false]) ++ ([true,true,false,true,true,false,true,true,false]) ++ (R)⟩ = some ⟨2,([false]) ++ ([true,false,false,true,false,false,true,false,false]) ++ (L),([true,true,false,true,true,false,true,true,false,true,true,false,true,true,false]) ++ (R)⟩ := by rfl

theorem phase7 (n : Nat) : run0 table (9*n) ⟨2,([false,true]),([true,true,false,true,true,false,true,true,false,true,true,false,true,true,false]) ++ (rep [true,true,false,true,true,false,true,true,false] (n)) ++ ([true,false])⟩ = some ⟨2,([false]) ++ (rep [true,false,false,true,false,false,true,false,false] (n)) ++ ([true]),([true,true,false,true,true,false,true,true,false,true,true,false,true,true,false,true,false])⟩ := by
  simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using sweepR table 2 [false] [true,true,false,true,true,false,true,true,false,true,true,false,true,true,false] [true,true,false,true,true,false,true,true,false] [true,false,false,true,false,false,true,false,false] 9 local7 n (([true])) (([true,false]))

theorem phase8 (n : Nat) : run0 table 18 ⟨2,([false]) ++ (rep [true,false,false,true,false,false,true,false,false] (n)) ++ ([true]),([true,true,false,true,true,false,true,true,false,true,true,false,true,true,false,true,false])⟩ = some ⟨1,([false,true,false,false,true,false,false,true,false,false,true,false,false,true,false,false,true,false,false]) ++ (rep [true,false,false,true,false,false,true,false,false] (n)) ++ ([true]),[]⟩ := by rfl

theorem finalL (n : Nat) : ([false,true,false,false,true,false,false,true,false,false,true,false,false,true,false,false,true,false,false]) ++ (rep [true,false,false,true,false,false,true,false,false] (n)) ++ ([true]) = ([false,true,false,false,true,false,false,true,false,false,true,false,false,true,false,false,true,false,false,true]) ++ (rep [false,false,true,false,false,true,false,false,true] (n)) := by
  calc
    _ = ([false,true,false,false,true,false,false,true,false,false,true,false,false,true,false,false,true,false,false,true]) ++ (rep [false,false,true,false,false,true,false,false,true] (n)) := by symm; simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using moveCut (([false,true,false,false,true,false,false,true,false,false,true,false,false,true,false,false,true,false,false])) ([]) [false,false,true,false,false,true,false,false] true n

theorem finalR (n : Nat) : ([] : List Bool) = [] := by
  rfl

theorem growth (n : Nat) : run0 table (167+120*n) (family n) = some (family (n+1)) := by
  have H := (join0 (join0 (join0 (join0 (join0 (join0 (join0 (join0 (phase0 n) (phase1 n)) (phase2 n)) (phase3 n)) (phase4 n)) (phase5 n)) (phase6 n)) (phase7 n)) (phase8 n))
  rw [finalL n] at H
  rw [show 9+51*n+55+9*n+10+51*n+75+9*n+18=167+120*n by omega] at H
  simpa only [family,rep,List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using H

theorem never (m : Machine) (hm : compatible table m) : NeverHalts m :=
  never_of_growth table family 48 (fun n => 167+120*n) entry (by intro n; omega) growth m hm

#print axioms never

end M323

end BB6.Agent11Raw39B1RCPumps
