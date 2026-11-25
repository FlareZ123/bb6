import SweepPumping
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedVariables false
namespace BB6.Agent11Raw39B1RCPumps
open BB6Coverage BB6Coverage.Agent31Pump


namespace M1479

-- 1RB1RC_1RC1RF_0RD1LF_1LD0RA_1LF---_1LC0LE

def table : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 0,true => some (some ⟨true,true,2⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 1,true => some (some ⟨true,true,5⟩)
  | 2,false => some (some ⟨false,true,3⟩)
  | 2,true => some (some ⟨true,false,5⟩)
  | 3,false => some (some ⟨true,false,3⟩)
  | 3,true => some (some ⟨false,true,0⟩)
  | 4,false => some (some ⟨true,false,5⟩)
  | 5,false => some (some ⟨true,false,2⟩)
  | 5,true => some (some ⟨false,false,4⟩)
  | _,_ => none

def family (n : Nat) : Z0 := ⟨5,([false,true,true,false,false,true,false,false]) ++ (rep [true,false,false,true,false,false,true,false,false] (n)),[]⟩

theorem entry : run0 table 20 ⟨0,[],[]⟩ = some (family 0) := by rfl

theorem phase0 (n : Nat) : run0 table 1 ⟨5,([false,true,true,false,false,true,false,false]) ++ (rep [true,false,false,true,false,false,true,false,false] (n)),[]⟩ = some ⟨2,([true,true,false,false,true,false,false]) ++ (rep [true,false,false,true,false,false,true,false,false] (n)),([true])⟩ := by rfl

theorem local1 (L R : List Bool) : run0 table 27 ⟨2,([true,true,false,false,true,false,false]) ++ ([true,false,false,true,false,false,true,false,false]) ++ (L),(R)⟩ = some ⟨2,([true,true,false,false,true,false,false]) ++ (L),([true,false,true,true,false,true,true,false,true]) ++ (R)⟩ := by rfl

theorem phase1 (n : Nat) : run0 table (27*n) ⟨2,([true,true,false,false,true,false,false]) ++ (rep [true,false,false,true,false,false,true,false,false] (n)),([true])⟩ = some ⟨2,([true,true,false,false,true,false,false]),(rep [true,false,true,true,false,true,true,false,true] (n)) ++ ([true])⟩ := by
  simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using sweepL table 2 [true,true,false,false,true,false,false] [] [true,false,false,true,false,false,true,false,false] [true,false,true,true,false,true,true,false,true] 27 local1 n ([]) (([true]))

theorem phase2 (n : Nat) : run0 table 14 ⟨2,([true,true,false,false,true,false,false]),(rep [true,false,true,true,false,true,true,false,true] (n)) ++ ([true])⟩ = some ⟨3,([true,false]),([true,false,true,true,false,true]) ++ (rep [true,false,true,true,false,true,true,false,true] (n)) ++ ([true])⟩ := by rfl

theorem local3 (L R : List Bool) : run0 table 9 ⟨3,([true]) ++ (L),([true,false,true,true,false,true]) ++ ([true,false,true,true,false,true,true,false,true]) ++ (R)⟩ = some ⟨3,([true]) ++ ([false,true,false,false,true,false,false,true,false]) ++ (L),([true,false,true,true,false,true]) ++ (R)⟩ := by rfl

theorem phase3 (n : Nat) : run0 table (9*n) ⟨3,([true,false]),([true,false,true,true,false,true]) ++ (rep [true,false,true,true,false,true,true,false,true] (n)) ++ ([true])⟩ = some ⟨3,([true]) ++ (rep [false,true,false,false,true,false,false,true,false] (n)) ++ ([false]),([true,false,true,true,false,true,true])⟩ := by
  simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using sweepR table 3 [true] [true,false,true,true,false,true] [true,false,true,true,false,true,true,false,true] [false,true,false,false,true,false,false,true,false] 9 local3 n (([false])) (([true]))

theorem phase4 (n : Nat) : run0 table 32 ⟨3,([true]) ++ (rep [false,true,false,false,true,false,false,true,false] (n)) ++ ([false]),([true,false,true,true,false,true,true])⟩ = some ⟨5,([true,false,false,true,false,false,true,false,false,true,false]) ++ (rep [false,true,false,false,true,false,false,true,false] (n)) ++ ([false]),([true,false,true])⟩ := by rfl

theorem local5 (L R : List Bool) : run0 table 27 ⟨5,([true,false,false,true,false,false,true,false,false,true,false]) ++ ([false,true,false,false,true,false,false,true,false]) ++ (L),(R)⟩ = some ⟨5,([true,false,false,true,false,false,true,false,false,true,false]) ++ (L),([true,true,false,true,true,false,true,true,false]) ++ (R)⟩ := by rfl

theorem phase5 (n : Nat) : run0 table (27*n) ⟨5,([true,false,false,true,false,false,true,false,false,true,false]) ++ (rep [false,true,false,false,true,false,false,true,false] (n)) ++ ([false]),([true,false,true])⟩ = some ⟨5,([true,false,false,true,false,false,true,false,false,true,false,false]),(rep [true,true,false,true,true,false,true,true,false] (n)) ++ ([true,false,true])⟩ := by
  simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using sweepL table 5 [true,false,false,true,false,false,true,false,false,true,false] [] [false,true,false,false,true,false,false,true,false] [true,true,false,true,true,false,true,true,false] 27 local5 n (([false])) (([true,false,true]))

theorem phase6 (n : Nat) : run0 table 31 ⟨5,([true,false,false,true,false,false,true,false,false,true,false,false]),(rep [true,true,false,true,true,false,true,true,false] (n)) ++ ([true,false,true])⟩ = some ⟨3,([true,false]),([true,false,true,true,false,true,true,false,true,true,false]) ++ (rep [true,true,false,true,true,false,true,true,false] (n)) ++ ([true,false,true])⟩ := by rfl

theorem local7 (L R : List Bool) : run0 table 9 ⟨3,([true]) ++ (L),([true,false,true,true,false,true,true,false,true,true,false]) ++ ([true,true,false,true,true,false,true,true,false]) ++ (R)⟩ = some ⟨3,([true]) ++ ([false,true,false,false,true,false,false,true,false]) ++ (L),([true,false,true,true,false,true,true,false,true,true,false]) ++ (R)⟩ := by rfl

theorem phase7 (n : Nat) : run0 table (9*n) ⟨3,([true,false]),([true,false,true,true,false,true,true,false,true,true,false]) ++ (rep [true,true,false,true,true,false,true,true,false] (n)) ++ ([true,false,true])⟩ = some ⟨3,([true]) ++ (rep [false,true,false,false,true,false,false,true,false] (n)) ++ ([false]),([true,false,true,true,false,true,true,false,true,true,false,true,false,true])⟩ := by
  simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using sweepR table 3 [true] [true,false,true,true,false,true,true,false,true,true,false] [true,true,false,true,true,false,true,true,false] [false,true,false,false,true,false,false,true,false] 9 local7 n (([false])) (([true,false,true]))

theorem phase8 (n : Nat) : run0 table 15 ⟨3,([true]) ++ (rep [false,true,false,false,true,false,false,true,false] (n)) ++ ([false]),([true,false,true,true,false,true,true,false,true,true,false,true,false,true])⟩ = some ⟨5,([false,true,true,false,false,true,false,false,true,false,false,true,false,false,true,false]) ++ (rep [false,true,false,false,true,false,false,true,false] (n)) ++ ([false]),[]⟩ := by rfl

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

end M1479

namespace M1499

-- 1RB1RC_1RC---_0RD1LF_1LD0RA_0RB1LB_0LE0LF

def table : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 0,true => some (some ⟨true,true,2⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 2,false => some (some ⟨false,true,3⟩)
  | 2,true => some (some ⟨true,false,5⟩)
  | 3,false => some (some ⟨true,false,3⟩)
  | 3,true => some (some ⟨false,true,0⟩)
  | 4,false => some (some ⟨false,true,1⟩)
  | 4,true => some (some ⟨true,false,1⟩)
  | 5,false => some (some ⟨false,false,4⟩)
  | 5,true => some (some ⟨false,false,5⟩)
  | _,_ => none

def family (n : Nat) : Z0 := ⟨5,[],([false,true,false,false,true]) ++ (rep [false,false,true,false,false,true,false,false,true,false,false,true,false,false,true] (n))⟩

theorem entry : run0 table 14 ⟨0,[],[]⟩ = some (family 0) := by rfl

theorem phase0 (n : Nat) : run0 table 13 ⟨5,[],([false,true,false,false,true]) ++ (rep [false,false,true,false,false,true,false,false,true,false,false,true,false,false,true] (n))⟩ = some ⟨2,([false,true,false,true,false]),([false,true]) ++ (rep [false,false,true,false,false,true,false,false,true,false,false,true,false,false,true] (n))⟩ := by rfl

theorem local1 (L R : List Bool) : run0 table 65 ⟨2,([false,true,false]) ++ (L),([false,true]) ++ ([false,false,true,false,false,true,false,false,true,false,false,true,false,false,true]) ++ (R)⟩ = some ⟨2,([false,true,false]) ++ ([false,true,false,false,true,false,false,true,false,false,true,false,false,true,false]) ++ (L),([false,true]) ++ (R)⟩ := by rfl

theorem phase1 (n : Nat) : run0 table (65*n) ⟨2,([false,true,false,true,false]),([false,true]) ++ (rep [false,false,true,false,false,true,false,false,true,false,false,true,false,false,true] (n))⟩ = some ⟨2,([false,true,false]) ++ (rep [false,true,false,false,true,false,false,true,false,false,true,false,false,true,false] (n)) ++ ([true,false]),([false,true])⟩ := by
  simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using sweepR table 2 [false,true,false] [false,true] [false,false,true,false,false,true,false,false,true,false,false,true,false,false,true] [false,true,false,false,true,false,false,true,false,false,true,false,false,true,false] 65 local1 n (([true,false])) ([])

theorem phase2 (n : Nat) : run0 table 32 ⟨2,([false,true,false]) ++ (rep [false,true,false,false,true,false,false,true,false,false,true,false,false,true,false] (n)) ++ ([true,false]),([false,true])⟩ = some ⟨2,([true,true,false,true,false,false,true,false,false,true,false]) ++ (rep [false,true,false,false,true,false,false,true,false,false,true,false,false,true,false] (n)) ++ ([true,false]),[]⟩ := by rfl

theorem local3 (L R : List Bool) : run0 table 25 ⟨2,([true,true,false,true,false,false,true,false,false,true,false]) ++ ([false,true,false,false,true,false,false,true,false,false,true,false,false,true,false]) ++ (L),(R)⟩ = some ⟨2,([true,true,false,true,false,false,true,false,false,true,false]) ++ (L),([false,false,true,false,false,true,false,false,true,false,false,true,false,false,true]) ++ (R)⟩ := by rfl

theorem phase3 (n : Nat) : run0 table (25*n) ⟨2,([true,true,false,true,false,false,true,false,false,true,false]) ++ (rep [false,true,false,false,true,false,false,true,false,false,true,false,false,true,false] (n)) ++ ([true,false]),[]⟩ = some ⟨2,([true,true,false,true,false,false,true,false,false,true,false,true,false]),(rep [false,false,true,false,false,true,false,false,true,false,false,true,false,false,true] (n))⟩ := by
  simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using sweepL table 2 [true,true,false,true,false,false,true,false,false,true,false] [] [false,true,false,false,true,false,false,true,false,false,true,false,false,true,false] [false,false,true,false,false,true,false,false,true,false,false,true,false,false,true] 25 local3 n (([true,false])) ([])

theorem phase4 (n : Nat) : run0 table 21 ⟨2,([true,true,false,true,false,false,true,false,false,true,false,true,false]),(rep [false,false,true,false,false,true,false,false,true,false,false,true,false,false,true] (n))⟩ = some ⟨2,([false,true,false]),([false,true,false,false,true,false,false,true,false,false,true]) ++ (rep [false,false,true,false,false,true,false,false,true,false,false,true,false,false,true] (n))⟩ := by rfl

theorem local5 (L R : List Bool) : run0 table 65 ⟨2,([false,true,false]) ++ (L),([false,true,false,false,true,false,false,true,false,false,true]) ++ ([false,false,true,false,false,true,false,false,true,false,false,true,false,false,true]) ++ (R)⟩ = some ⟨2,([false,true,false]) ++ ([false,true,false,false,true,false,false,true,false,false,true,false,false,true,false]) ++ (L),([false,true,false,false,true,false,false,true,false,false,true]) ++ (R)⟩ := by rfl

theorem phase5 (n : Nat) : run0 table (65*n) ⟨2,([false,true,false]),([false,true,false,false,true,false,false,true,false,false,true]) ++ (rep [false,false,true,false,false,true,false,false,true,false,false,true,false,false,true] (n))⟩ = some ⟨2,([false,true,false]) ++ (rep [false,true,false,false,true,false,false,true,false,false,true,false,false,true,false] (n)),([false,true,false,false,true,false,false,true,false,false,true])⟩ := by
  simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using sweepR table 2 [false,true,false] [false,true,false,false,true,false,false,true,false,false,true] [false,false,true,false,false,true,false,false,true,false,false,true,false,false,true] [false,true,false,false,true,false,false,true,false,false,true,false,false,true,false] 65 local5 n ([]) ([])

theorem phase6 (n : Nat) : run0 table 71 ⟨2,([false,true,false]) ++ (rep [false,true,false,false,true,false,false,true,false,false,true,false,false,true,false] (n)),([false,true,false,false,true,false,false,true,false,false,true])⟩ = some ⟨2,([true,true,false,true,false,false,true,false,false,true,false,false,true,false,false,true,false,false,true,false]) ++ (rep [false,true,false,false,true,false,false,true,false,false,true,false,false,true,false] (n)),[]⟩ := by rfl

theorem local7 (L R : List Bool) : run0 table 25 ⟨2,([true,true,false,true,false,false,true,false,false,true,false,false,true,false,false,true,false,false,true,false]) ++ ([false,true,false,false,true,false,false,true,false,false,true,false,false,true,false]) ++ (L),(R)⟩ = some ⟨2,([true,true,false,true,false,false,true,false,false,true,false,false,true,false,false,true,false,false,true,false]) ++ (L),([false,false,true,false,false,true,false,false,true,false,false,true,false,false,true]) ++ (R)⟩ := by rfl

theorem phase7 (n : Nat) : run0 table (25*n) ⟨2,([true,true,false,true,false,false,true,false,false,true,false,false,true,false,false,true,false,false,true,false]) ++ (rep [false,true,false,false,true,false,false,true,false,false,true,false,false,true,false] (n)),[]⟩ = some ⟨2,([true,true,false,true,false,false,true,false,false,true,false,false,true,false,false,true,false,false,true,false]),(rep [false,false,true,false,false,true,false,false,true,false,false,true,false,false,true] (n))⟩ := by
  simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using sweepL table 2 [true,true,false,true,false,false,true,false,false,true,false,false,true,false,false,true,false,false,true,false] [] [false,true,false,false,true,false,false,true,false,false,true,false,false,true,false] [false,false,true,false,false,true,false,false,true,false,false,true,false,false,true] 25 local7 n ([]) ([])

theorem phase8 (n : Nat) : run0 table 32 ⟨2,([true,true,false,true,false,false,true,false,false,true,false,false,true,false,false,true,false,false,true,false]),(rep [false,false,true,false,false,true,false,false,true,false,false,true,false,false,true] (n))⟩ = some ⟨5,[],([false,true,false,false,true,false,false,true,false,false,true,false,false,true,false,false,true,false,false,true]) ++ (rep [false,false,true,false,false,true,false,false,true,false,false,true,false,false,true] (n))⟩ := by rfl

theorem finalL (n : Nat) : ([] : List Bool) = [] := by
  rfl

theorem finalR (n : Nat) : ([false,true,false,false,true,false,false,true,false,false,true,false,false,true,false,false,true,false,false,true]) ++ (rep [false,false,true,false,false,true,false,false,true,false,false,true,false,false,true] (n)) = ([false,true,false,false,true,false,false,true,false,false,true,false,false,true,false,false,true,false,false,true]) ++ (rep [false,false,true,false,false,true,false,false,true,false,false,true,false,false,true] (n)) := by
  rfl

theorem growth (n : Nat) : run0 table (169+180*n) (family n) = some (family (n+1)) := by
  have H := (join0 (join0 (join0 (join0 (join0 (join0 (join0 (join0 (phase0 n) (phase1 n)) (phase2 n)) (phase3 n)) (phase4 n)) (phase5 n)) (phase6 n)) (phase7 n)) (phase8 n))
  rw [show 13+65*n+32+25*n+21+65*n+71+25*n+32=169+180*n by omega] at H
  simpa only [family,rep,List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using H

theorem never (m : Machine) (hm : compatible table m) : NeverHalts m :=
  never_of_growth table family 14 (fun n => 169+180*n) entry (by intro n; omega) growth m hm

#print axioms never

end M1499

namespace M1500

-- 1RB1RC_1RC---_0RD1LF_1LD0RA_1RD1LB_0LE0LF

def table : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 0,true => some (some ⟨true,true,2⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 2,false => some (some ⟨false,true,3⟩)
  | 2,true => some (some ⟨true,false,5⟩)
  | 3,false => some (some ⟨true,false,3⟩)
  | 3,true => some (some ⟨false,true,0⟩)
  | 4,false => some (some ⟨true,true,3⟩)
  | 4,true => some (some ⟨true,false,1⟩)
  | 5,false => some (some ⟨false,false,4⟩)
  | 5,true => some (some ⟨false,false,5⟩)
  | _,_ => none

def family (n : Nat) : Z0 := ⟨5,[],([false,true,false,false,true]) ++ (rep [false,false,true,false,false,true,false,false,true,false,false,true,false,false,true] (n))⟩

theorem entry : run0 table 14 ⟨0,[],[]⟩ = some (family 0) := by rfl

theorem phase0 (n : Nat) : run0 table 15 ⟨5,[],([false,true,false,false,true]) ++ (rep [false,false,true,false,false,true,false,false,true,false,false,true,false,false,true] (n))⟩ = some ⟨3,([true,true,false]),([true,false,false,true]) ++ (rep [false,false,true,false,false,true,false,false,true,false,false,true,false,false,true] (n))⟩ := by rfl

theorem local1 (L R : List Bool) : run0 table 75 ⟨3,([true]) ++ (L),([true,false,false,true]) ++ ([false,false,true,false,false,true,false,false,true,false,false,true,false,false,true]) ++ (R)⟩ = some ⟨3,([true]) ++ ([false,true,false,false,true,false,false,true,false,false,true,false,false,true,false]) ++ (L),([true,false,false,true]) ++ (R)⟩ := by rfl

theorem phase1 (n : Nat) : run0 table (75*n) ⟨3,([true,true,false]),([true,false,false,true]) ++ (rep [false,false,true,false,false,true,false,false,true,false,false,true,false,false,true] (n))⟩ = some ⟨3,([true]) ++ (rep [false,true,false,false,true,false,false,true,false,false,true,false,false,true,false] (n)) ++ ([true,false]),([true,false,false,true])⟩ := by
  simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using sweepR table 3 [true] [true,false,false,true] [false,false,true,false,false,true,false,false,true,false,false,true,false,false,true] [false,true,false,false,true,false,false,true,false,false,true,false,false,true,false] 75 local1 n (([true,false])) ([])

theorem phase2 (n : Nat) : run0 table 38 ⟨3,([true]) ++ (rep [false,true,false,false,true,false,false,true,false,false,true,false,false,true,false] (n)) ++ ([true,false]),([true,false,false,true])⟩ = some ⟨2,([true,true,false,true,false,false,true,false,false,true,false]) ++ (rep [false,true,false,false,true,false,false,true,false,false,true,false,false,true,false] (n)) ++ ([true,false]),[]⟩ := by rfl

theorem local3 (L R : List Bool) : run0 table 25 ⟨2,([true,true,false,true,false,false,true,false,false,true,false]) ++ ([false,true,false,false,true,false,false,true,false,false,true,false,false,true,false]) ++ (L),(R)⟩ = some ⟨2,([true,true,false,true,false,false,true,false,false,true,false]) ++ (L),([false,false,true,false,false,true,false,false,true,false,false,true,false,false,true]) ++ (R)⟩ := by rfl

theorem phase3 (n : Nat) : run0 table (25*n) ⟨2,([true,true,false,true,false,false,true,false,false,true,false]) ++ (rep [false,true,false,false,true,false,false,true,false,false,true,false,false,true,false] (n)) ++ ([true,false]),[]⟩ = some ⟨2,([true,true,false,true,false,false,true,false,false,true,false,true,false]),(rep [false,false,true,false,false,true,false,false,true,false,false,true,false,false,true] (n))⟩ := by
  simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using sweepL table 2 [true,true,false,true,false,false,true,false,false,true,false] [] [false,true,false,false,true,false,false,true,false,false,true,false,false,true,false] [false,false,true,false,false,true,false,false,true,false,false,true,false,false,true] 25 local3 n (([true,false])) ([])

theorem phase4 (n : Nat) : run0 table 21 ⟨2,([true,true,false,true,false,false,true,false,false,true,false,true,false]),(rep [false,false,true,false,false,true,false,false,true,false,false,true,false,false,true] (n))⟩ = some ⟨3,([true]),([true,false,false,true,false,false,true,false,false,true,false,false,true]) ++ (rep [false,false,true,false,false,true,false,false,true,false,false,true,false,false,true] (n))⟩ := by rfl

theorem local5 (L R : List Bool) : run0 table 75 ⟨3,([true]) ++ (L),([true,false,false,true,false,false,true,false,false,true,false,false,true]) ++ ([false,false,true,false,false,true,false,false,true,false,false,true,false,false,true]) ++ (R)⟩ = some ⟨3,([true]) ++ ([false,true,false,false,true,false,false,true,false,false,true,false,false,true,false]) ++ (L),([true,false,false,true,false,false,true,false,false,true,false,false,true]) ++ (R)⟩ := by rfl

theorem phase5 (n : Nat) : run0 table (75*n) ⟨3,([true]),([true,false,false,true,false,false,true,false,false,true,false,false,true]) ++ (rep [false,false,true,false,false,true,false,false,true,false,false,true,false,false,true] (n))⟩ = some ⟨3,([true]) ++ (rep [false,true,false,false,true,false,false,true,false,false,true,false,false,true,false] (n)),([true,false,false,true,false,false,true,false,false,true,false,false,true])⟩ := by
  simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using sweepR table 3 [true] [true,false,false,true,false,false,true,false,false,true,false,false,true] [false,false,true,false,false,true,false,false,true,false,false,true,false,false,true] [false,true,false,false,true,false,false,true,false,false,true,false,false,true,false] 75 local5 n ([]) ([])

theorem phase6 (n : Nat) : run0 table 83 ⟨3,([true]) ++ (rep [false,true,false,false,true,false,false,true,false,false,true,false,false,true,false] (n)),([true,false,false,true,false,false,true,false,false,true,false,false,true])⟩ = some ⟨2,([true,true,false,true,false,false,true,false,false,true,false,false,true,false,false,true,false,false,true,false]) ++ (rep [false,true,false,false,true,false,false,true,false,false,true,false,false,true,false] (n)),[]⟩ := by rfl

theorem local7 (L R : List Bool) : run0 table 25 ⟨2,([true,true,false,true,false,false,true,false,false,true,false,false,true,false,false,true,false,false,true,false]) ++ ([false,true,false,false,true,false,false,true,false,false,true,false,false,true,false]) ++ (L),(R)⟩ = some ⟨2,([true,true,false,true,false,false,true,false,false,true,false,false,true,false,false,true,false,false,true,false]) ++ (L),([false,false,true,false,false,true,false,false,true,false,false,true,false,false,true]) ++ (R)⟩ := by rfl

theorem phase7 (n : Nat) : run0 table (25*n) ⟨2,([true,true,false,true,false,false,true,false,false,true,false,false,true,false,false,true,false,false,true,false]) ++ (rep [false,true,false,false,true,false,false,true,false,false,true,false,false,true,false] (n)),[]⟩ = some ⟨2,([true,true,false,true,false,false,true,false,false,true,false,false,true,false,false,true,false,false,true,false]),(rep [false,false,true,false,false,true,false,false,true,false,false,true,false,false,true] (n))⟩ := by
  simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using sweepL table 2 [true,true,false,true,false,false,true,false,false,true,false,false,true,false,false,true,false,false,true,false] [] [false,true,false,false,true,false,false,true,false,false,true,false,false,true,false] [false,false,true,false,false,true,false,false,true,false,false,true,false,false,true] 25 local7 n ([]) ([])

theorem phase8 (n : Nat) : run0 table 32 ⟨2,([true,true,false,true,false,false,true,false,false,true,false,false,true,false,false,true,false,false,true,false]),(rep [false,false,true,false,false,true,false,false,true,false,false,true,false,false,true] (n))⟩ = some ⟨5,[],([false,true,false,false,true,false,false,true,false,false,true,false,false,true,false,false,true,false,false,true]) ++ (rep [false,false,true,false,false,true,false,false,true,false,false,true,false,false,true] (n))⟩ := by rfl

theorem finalL (n : Nat) : ([] : List Bool) = [] := by
  rfl

theorem finalR (n : Nat) : ([false,true,false,false,true,false,false,true,false,false,true,false,false,true,false,false,true,false,false,true]) ++ (rep [false,false,true,false,false,true,false,false,true,false,false,true,false,false,true] (n)) = ([false,true,false,false,true,false,false,true,false,false,true,false,false,true,false,false,true,false,false,true]) ++ (rep [false,false,true,false,false,true,false,false,true,false,false,true,false,false,true] (n)) := by
  rfl

theorem growth (n : Nat) : run0 table (189+200*n) (family n) = some (family (n+1)) := by
  have H := (join0 (join0 (join0 (join0 (join0 (join0 (join0 (join0 (phase0 n) (phase1 n)) (phase2 n)) (phase3 n)) (phase4 n)) (phase5 n)) (phase6 n)) (phase7 n)) (phase8 n))
  rw [show 15+75*n+38+25*n+21+75*n+83+25*n+32=189+200*n by omega] at H
  simpa only [family,rep,List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using H

theorem never (m : Machine) (hm : compatible table m) : NeverHalts m :=
  never_of_growth table family 14 (fun n => 189+200*n) entry (by intro n; omega) growth m hm

#print axioms never

end M1500

namespace M1515

-- 1RB1RC_1RC1RE_0RD1LF_1LD0RA_0RC---_1LA0LF

def table : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 0,true => some (some ⟨true,true,2⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 1,true => some (some ⟨true,true,4⟩)
  | 2,false => some (some ⟨false,true,3⟩)
  | 2,true => some (some ⟨true,false,5⟩)
  | 3,false => some (some ⟨true,false,3⟩)
  | 3,true => some (some ⟨false,true,0⟩)
  | 4,false => some (some ⟨false,true,2⟩)
  | 5,false => some (some ⟨true,false,0⟩)
  | 5,true => some (some ⟨false,false,5⟩)
  | _,_ => none

def family (n : Nat) : Z0 := ⟨0,([false,false,false,true,false,false,false,true,true]) ++ (rep [false,true,true,false,true,true,false,true,true,false,true,true] (n)),[]⟩

theorem entry : run0 table 32 ⟨0,[],[]⟩ = some (family 0) := by rfl

theorem phase0 (n : Nat) : run0 table 39 ⟨0,([false,false,false,true,false,false,false,true,true]) ++ (rep [false,true,true,false,true,true,false,true,true,false,true,true] (n)),[]⟩ = some ⟨5,([true,false,true,true]) ++ (rep [false,true,true,false,true,true,false,true,true,false,true,true] (n)),([true,false,true,true,true,true,false,true])⟩ := by rfl

theorem local1 (L R : List Bool) : run0 table 20 ⟨5,([true,false,true,true]) ++ ([false,true,true,false,true,true,false,true,true,false,true,true]) ++ (L),(R)⟩ = some ⟨5,([true,false,true,true]) ++ (L),([false,true,false,false,true,false,false,true,false,false,true,false]) ++ (R)⟩ := by rfl

theorem phase1 (n : Nat) : run0 table (20*n) ⟨5,([true,false,true,true]) ++ (rep [false,true,true,false,true,true,false,true,true,false,true,true] (n)),([true,false,true,true,true,true,false,true])⟩ = some ⟨5,([true,false,true,true]),(rep [false,true,false,false,true,false,false,true,false,false,true,false] (n)) ++ ([true,false,true,true,true,true,false,true])⟩ := by
  simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using sweepL table 5 [true,false,true,true] [] [false,true,true,false,true,true,false,true,true,false,true,true] [false,true,false,false,true,false,false,true,false,false,true,false] 20 local1 n ([]) (([true,false,true,true,true,true,false,true]))

theorem phase2 (n : Nat) : run0 table 8 ⟨5,([true,false,true,true]),(rep [false,true,false,false,true,false,false,true,false,false,true,false] (n)) ++ ([true,false,true,true,true,true,false,true])⟩ = some ⟨1,([true,true]),([false,false,true,false]) ++ (rep [false,true,false,false,true,false,false,true,false,false,true,false] (n)) ++ ([true,false,true,true,true,true,false,true])⟩ := by rfl

theorem local3 (L R : List Bool) : run0 table 44 ⟨1,([true]) ++ (L),([false,false,true,false]) ++ ([false,true,false,false,true,false,false,true,false,false,true,false]) ++ (R)⟩ = some ⟨1,([true]) ++ ([true,false,true,true,false,true,true,false,true,true,false,true]) ++ (L),([false,false,true,false]) ++ (R)⟩ := by rfl

theorem phase3 (n : Nat) : run0 table (44*n) ⟨1,([true,true]),([false,false,true,false]) ++ (rep [false,true,false,false,true,false,false,true,false,false,true,false] (n)) ++ ([true,false,true,true,true,true,false,true])⟩ = some ⟨1,([true]) ++ (rep [true,false,true,true,false,true,true,false,true,true,false,true] (n)) ++ ([true]),([false,false,true,false,true,false,true,true,true,true,false,true])⟩ := by
  simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using sweepR table 1 [true] [false,false,true,false] [false,true,false,false,true,false,false,true,false,false,true,false] [true,false,true,true,false,true,true,false,true,true,false,true] 44 local3 n (([true])) (([true,false,true,true,true,true,false,true]))

theorem phase4 (n : Nat) : run0 table 27 ⟨1,([true]) ++ (rep [true,false,true,true,false,true,true,false,true,true,false,true] (n)) ++ ([true]),([false,false,true,false,true,false,true,true,true,true,false,true])⟩ = some ⟨5,([false,true,true,false,true,true,false,true]) ++ (rep [true,false,true,true,false,true,true,false,true,true,false,true] (n)) ++ ([true]),([true,true,true,false,true])⟩ := by rfl

theorem local5 (L R : List Bool) : run0 table 20 ⟨5,([false,true,true,false,true,true,false,true]) ++ ([true,false,true,true,false,true,true,false,true,true,false,true]) ++ (L),(R)⟩ = some ⟨5,([false,true,true,false,true,true,false,true]) ++ (L),([false,false,true,false,false,true,false,false,true,false,false,true]) ++ (R)⟩ := by rfl

theorem phase5 (n : Nat) : run0 table (20*n) ⟨5,([false,true,true,false,true,true,false,true]) ++ (rep [true,false,true,true,false,true,true,false,true,true,false,true] (n)) ++ ([true]),([true,true,true,false,true])⟩ = some ⟨5,([false,true,true,false,true,true,false,true,true]),(rep [false,false,true,false,false,true,false,false,true,false,false,true] (n)) ++ ([true,true,true,false,true])⟩ := by
  simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using sweepL table 5 [false,true,true,false,true,true,false,true] [] [true,false,true,true,false,true,true,false,true,true,false,true] [false,false,true,false,false,true,false,false,true,false,false,true] 20 local5 n (([true])) (([true,true,true,false,true]))

theorem phase6 (n : Nat) : run0 table 17 ⟨5,([false,true,true,false,true,true,false,true,true]),(rep [false,false,true,false,false,true,false,false,true,false,false,true] (n)) ++ ([true,true,true,false,true])⟩ = some ⟨1,([true,true]),([false,false,true,false,false,true,false,false,true]) ++ (rep [false,false,true,false,false,true,false,false,true,false,false,true] (n)) ++ ([true,true,true,false,true])⟩ := by rfl

theorem local7 (L R : List Bool) : run0 table 44 ⟨1,([true]) ++ (L),([false,false,true,false,false,true,false,false,true]) ++ ([false,false,true,false,false,true,false,false,true,false,false,true]) ++ (R)⟩ = some ⟨1,([true]) ++ ([true,false,true,true,false,true,true,false,true,true,false,true]) ++ (L),([false,false,true,false,false,true,false,false,true]) ++ (R)⟩ := by rfl

theorem phase7 (n : Nat) : run0 table (44*n) ⟨1,([true,true]),([false,false,true,false,false,true,false,false,true]) ++ (rep [false,false,true,false,false,true,false,false,true,false,false,true] (n)) ++ ([true,true,true,false,true])⟩ = some ⟨1,([true]) ++ (rep [true,false,true,true,false,true,true,false,true,true,false,true] (n)) ++ ([true]),([false,false,true,false,false,true,false,false,true,true,true,true,false,true])⟩ := by
  simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using sweepR table 1 [true] [false,false,true,false,false,true,false,false,true] [false,false,true,false,false,true,false,false,true,false,false,true] [true,false,true,true,false,true,true,false,true,true,false,true] 44 local7 n (([true])) (([true,true,true,false,true]))

theorem phase8 (n : Nat) : run0 table 34 ⟨1,([true]) ++ (rep [true,false,true,true,false,true,true,false,true,true,false,true] (n)) ++ ([true]),([false,false,true,false,false,true,false,false,true,true,true,true,false,true])⟩ = some ⟨5,([false,true,true,false,true,true,false,true,true,false,true]) ++ (rep [true,false,true,true,false,true,true,false,true,true,false,true] (n)) ++ ([true]),([true,true,false,true])⟩ := by rfl

theorem local9 (L R : List Bool) : run0 table 20 ⟨5,([false,true,true,false,true,true,false,true,true,false,true]) ++ ([true,false,true,true,false,true,true,false,true,true,false,true]) ++ (L),(R)⟩ = some ⟨5,([false,true,true,false,true,true,false,true,true,false,true]) ++ (L),([false,false,true,false,false,true,false,false,true,false,false,true]) ++ (R)⟩ := by rfl

theorem phase9 (n : Nat) : run0 table (20*n) ⟨5,([false,true,true,false,true,true,false,true,true,false,true]) ++ (rep [true,false,true,true,false,true,true,false,true,true,false,true] (n)) ++ ([true]),([true,true,false,true])⟩ = some ⟨5,([false,true,true,false,true,true,false,true,true,false,true,true]),(rep [false,false,true,false,false,true,false,false,true,false,false,true] (n)) ++ ([true,true,false,true])⟩ := by
  simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using sweepL table 5 [false,true,true,false,true,true,false,true,true,false,true] [] [true,false,true,true,false,true,true,false,true,true,false,true] [false,false,true,false,false,true,false,false,true,false,false,true] 20 local9 n (([true])) (([true,true,false,true]))

theorem phase10 (n : Nat) : run0 table 22 ⟨5,([false,true,true,false,true,true,false,true,true,false,true,true]),(rep [false,false,true,false,false,true,false,false,true,false,false,true] (n)) ++ ([true,true,false,true])⟩ = some ⟨1,([true,true]),([false,false,true,false,false,true,false,false,true,false,false,true]) ++ (rep [false,false,true,false,false,true,false,false,true,false,false,true] (n)) ++ ([true,true,false,true])⟩ := by rfl

theorem local11 (L R : List Bool) : run0 table 44 ⟨1,([true]) ++ (L),([false,false,true,false,false,true,false,false,true,false,false,true]) ++ ([false,false,true,false,false,true,false,false,true,false,false,true]) ++ (R)⟩ = some ⟨1,([true]) ++ ([true,false,true,true,false,true,true,false,true,true,false,true]) ++ (L),([false,false,true,false,false,true,false,false,true,false,false,true]) ++ (R)⟩ := by rfl

theorem phase11 (n : Nat) : run0 table (44*n) ⟨1,([true,true]),([false,false,true,false,false,true,false,false,true,false,false,true]) ++ (rep [false,false,true,false,false,true,false,false,true,false,false,true] (n)) ++ ([true,true,false,true])⟩ = some ⟨1,([true]) ++ (rep [true,false,true,true,false,true,true,false,true,true,false,true] (n)) ++ ([true]),([false,false,true,false,false,true,false,false,true,false,false,true,true,true,false,true])⟩ := by
  simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using sweepR table 1 [true] [false,false,true,false,false,true,false,false,true,false,false,true] [false,false,true,false,false,true,false,false,true,false,false,true] [true,false,true,true,false,true,true,false,true,true,false,true] 44 local11 n (([true])) (([true,true,false,true]))

theorem phase12 (n : Nat) : run0 table 45 ⟨1,([true]) ++ (rep [true,false,true,true,false,true,true,false,true,true,false,true] (n)) ++ ([true]),([false,false,true,false,false,true,false,false,true,false,false,true,true,true,false,true])⟩ = some ⟨5,([false,true,true,false,true,true,false,true,true,false,true,true,false,true]) ++ (rep [true,false,true,true,false,true,true,false,true,true,false,true] (n)) ++ ([true]),([true,false,true])⟩ := by rfl

theorem local13 (L R : List Bool) : run0 table 20 ⟨5,([false,true,true,false,true,true,false,true,true,false,true,true,false,true]) ++ ([true,false,true,true,false,true,true,false,true,true,false,true]) ++ (L),(R)⟩ = some ⟨5,([false,true,true,false,true,true,false,true,true,false,true,true,false,true]) ++ (L),([false,false,true,false,false,true,false,false,true,false,false,true]) ++ (R)⟩ := by rfl

theorem phase13 (n : Nat) : run0 table (20*n) ⟨5,([false,true,true,false,true,true,false,true,true,false,true,true,false,true]) ++ (rep [true,false,true,true,false,true,true,false,true,true,false,true] (n)) ++ ([true]),([true,false,true])⟩ = some ⟨5,([false,true,true,false,true,true,false,true,true,false,true,true,false,true,true]),(rep [false,false,true,false,false,true,false,false,true,false,false,true] (n)) ++ ([true,false,true])⟩ := by
  simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using sweepL table 5 [false,true,true,false,true,true,false,true,true,false,true,true,false,true] [] [true,false,true,true,false,true,true,false,true,true,false,true] [false,false,true,false,false,true,false,false,true,false,false,true] 20 local13 n (([true])) (([true,false,true]))

theorem phase14 (n : Nat) : run0 table 27 ⟨5,([false,true,true,false,true,true,false,true,true,false,true,true,false,true,true]),(rep [false,false,true,false,false,true,false,false,true,false,false,true] (n)) ++ ([true,false,true])⟩ = some ⟨1,([true,true]),([false,false,true,false,false,true,false,false,true,false,false,true,false,false,true]) ++ (rep [false,false,true,false,false,true,false,false,true,false,false,true] (n)) ++ ([true,false,true])⟩ := by rfl

theorem local15 (L R : List Bool) : run0 table 44 ⟨1,([true]) ++ (L),([false,false,true,false,false,true,false,false,true,false,false,true,false,false,true]) ++ ([false,false,true,false,false,true,false,false,true,false,false,true]) ++ (R)⟩ = some ⟨1,([true]) ++ ([true,false,true,true,false,true,true,false,true,true,false,true]) ++ (L),([false,false,true,false,false,true,false,false,true,false,false,true,false,false,true]) ++ (R)⟩ := by rfl

theorem phase15 (n : Nat) : run0 table (44*n) ⟨1,([true,true]),([false,false,true,false,false,true,false,false,true,false,false,true,false,false,true]) ++ (rep [false,false,true,false,false,true,false,false,true,false,false,true] (n)) ++ ([true,false,true])⟩ = some ⟨1,([true]) ++ (rep [true,false,true,true,false,true,true,false,true,true,false,true] (n)) ++ ([true]),([false,false,true,false,false,true,false,false,true,false,false,true,false,false,true,true,false,true])⟩ := by
  simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using sweepR table 1 [true] [false,false,true,false,false,true,false,false,true,false,false,true,false,false,true] [false,false,true,false,false,true,false,false,true,false,false,true] [true,false,true,true,false,true,true,false,true,true,false,true] 44 local15 n (([true])) (([true,false,true]))

theorem phase16 (n : Nat) : run0 table 51 ⟨1,([true]) ++ (rep [true,false,true,true,false,true,true,false,true,true,false,true] (n)) ++ ([true]),([false,false,true,false,false,true,false,false,true,false,false,true,false,false,true,true,false,true])⟩ = some ⟨0,([false,false,false,true,false,false,false,true,true,false,true,true,false,true,true,false,true,true,false,true]) ++ (rep [true,false,true,true,false,true,true,false,true,true,false,true] (n)) ++ ([true]),[]⟩ := by rfl

theorem finalL (n : Nat) : ([false,false,false,true,false,false,false,true,true,false,true,true,false,true,true,false,true,true,false,true]) ++ (rep [true,false,true,true,false,true,true,false,true,true,false,true] (n)) ++ ([true]) = ([false,false,false,true,false,false,false,true,true,false,true,true,false,true,true,false,true,true,false,true,true]) ++ (rep [false,true,true,false,true,true,false,true,true,false,true,true] (n)) := by
  calc
    _ = ([false,false,false,true,false,false,false,true,true,false,true,true,false,true,true,false,true,true,false,true,true]) ++ (rep [false,true,true,false,true,true,false,true,true,false,true,true] (n)) := by symm; simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using moveCut (([false,false,false,true,false,false,false,true,true,false,true,true,false,true,true,false,true,true,false,true])) ([]) [false,true,true,false,true,true,false,true,true,false,true] true n

theorem finalR (n : Nat) : ([] : List Bool) = [] := by
  rfl

theorem growth (n : Nat) : run0 table (270+256*n) (family n) = some (family (n+1)) := by
  have H := (join0 (join0 (join0 (join0 (join0 (join0 (join0 (join0 (join0 (join0 (join0 (join0 (join0 (join0 (join0 (join0 (phase0 n) (phase1 n)) (phase2 n)) (phase3 n)) (phase4 n)) (phase5 n)) (phase6 n)) (phase7 n)) (phase8 n)) (phase9 n)) (phase10 n)) (phase11 n)) (phase12 n)) (phase13 n)) (phase14 n)) (phase15 n)) (phase16 n))
  rw [finalL n] at H
  rw [show 39+20*n+8+44*n+27+20*n+17+44*n+34+20*n+22+44*n+45+20*n+27+44*n+51=270+256*n by omega] at H
  simpa only [family,rep,List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using H

theorem never (m : Machine) (hm : compatible table m) : NeverHalts m :=
  never_of_growth table family 32 (fun n => 270+256*n) entry (by intro n; omega) growth m hm

#print axioms never

end M1515

namespace M1519

-- 1RB1RC_1RC---_0RD1LF_1LD0RA_0RA0LA_1LE0LF

def table : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 0,true => some (some ⟨true,true,2⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 2,false => some (some ⟨false,true,3⟩)
  | 2,true => some (some ⟨true,false,5⟩)
  | 3,false => some (some ⟨true,false,3⟩)
  | 3,true => some (some ⟨false,true,0⟩)
  | 4,false => some (some ⟨false,true,0⟩)
  | 4,true => some (some ⟨false,false,0⟩)
  | 5,false => some (some ⟨true,false,4⟩)
  | 5,true => some (some ⟨false,false,5⟩)
  | _,_ => none

def family (n : Nat) : Z0 := ⟨5,[],([false,false,true,false]) ++ (rep [false,true,false,false,true,false] (n)) ++ ([true])⟩

theorem entry : run0 table 16 ⟨0,[],[]⟩ = some (family 0) := by rfl

theorem phase0 (n : Nat) : run0 table 2 ⟨5,[],([false,false,true,false]) ++ (rep [false,true,false,false,true,false] (n)) ++ ([true])⟩ = some ⟨0,([true,false]),([false,false,true,false]) ++ (rep [false,true,false,false,true,false] (n)) ++ ([true])⟩ := by rfl

theorem local1 (L R : List Bool) : run0 table 26 ⟨0,([true,false]) ++ (L),([false,false,true,false]) ++ ([false,true,false,false,true,false]) ++ (R)⟩ = some ⟨0,([true,false]) ++ ([false,true,false,false,true,false]) ++ (L),([false,false,true,false]) ++ (R)⟩ := by rfl

theorem phase1 (n : Nat) : run0 table (26*n) ⟨0,([true,false]),([false,false,true,false]) ++ (rep [false,true,false,false,true,false] (n)) ++ ([true])⟩ = some ⟨0,([true,false]) ++ (rep [false,true,false,false,true,false] (n)),([false,false,true,false,true])⟩ := by
  simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using sweepR table 0 [true,false] [false,false,true,false] [false,true,false,false,true,false] [false,true,false,false,true,false] 26 local1 n ([]) (([true]))

theorem phase2 (n : Nat) : run0 table 24 ⟨0,([true,false]) ++ (rep [false,true,false,false,true,false] (n)),([false,false,true,false,true])⟩ = some ⟨5,([true,false,true,false,false,true,false,false,true,false]) ++ (rep [false,true,false,false,true,false] (n)),([true])⟩ := by rfl

theorem local3 (L R : List Bool) : run0 table 14 ⟨5,([true,false,true,false,false,true,false,false,true,false]) ++ ([false,true,false,false,true,false]) ++ (L),(R)⟩ = some ⟨5,([true,false,true,false,false,true,false,false,true,false]) ++ (L),([false,true,false,false,true,false]) ++ (R)⟩ := by rfl

theorem phase3 (n : Nat) : run0 table (14*n) ⟨5,([true,false,true,false,false,true,false,false,true,false]) ++ (rep [false,true,false,false,true,false] (n)),([true])⟩ = some ⟨5,([true,false,true,false,false,true,false,false,true,false]),(rep [false,true,false,false,true,false] (n)) ++ ([true])⟩ := by
  simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using sweepL table 5 [true,false,true,false,false,true,false,false,true,false] [] [false,true,false,false,true,false] [false,true,false,false,true,false] 14 local3 n ([]) (([true]))

theorem phase4 (n : Nat) : run0 table 22 ⟨5,([true,false,true,false,false,true,false,false,true,false]),(rep [false,true,false,false,true,false] (n)) ++ ([true])⟩ = some ⟨5,[],([false,false,true,false,false,true,false,false,true,false]) ++ (rep [false,true,false,false,true,false] (n)) ++ ([true])⟩ := by rfl

theorem finalL (n : Nat) : ([] : List Bool) = [] := by
  rfl

theorem finalR (n : Nat) : ([false,false,true,false,false,true,false,false,true,false]) ++ (rep [false,true,false,false,true,false] (n)) ++ ([true]) = ([false,false,true,false,false,true,false,false,true,false]) ++ (rep [false,true,false,false,true,false] (n)) ++ ([true]) := by
  rfl

theorem growth (n : Nat) : run0 table (48+40*n) (family n) = some (family (n+1)) := by
  have H := (join0 (join0 (join0 (join0 (phase0 n) (phase1 n)) (phase2 n)) (phase3 n)) (phase4 n))
  rw [show 2+26*n+24+14*n+22=48+40*n by omega] at H
  simpa only [family,rep,List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using H

theorem never (m : Machine) (hm : compatible table m) : NeverHalts m :=
  never_of_growth table family 16 (fun n => 48+40*n) entry (by intro n; omega) growth m hm

#print axioms never

end M1519

namespace M1520

-- 1RB1RC_1RC---_0RD1LF_1LD0RA_1LC0LA_1LE0LF

def table : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 0,true => some (some ⟨true,true,2⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 2,false => some (some ⟨false,true,3⟩)
  | 2,true => some (some ⟨true,false,5⟩)
  | 3,false => some (some ⟨true,false,3⟩)
  | 3,true => some (some ⟨false,true,0⟩)
  | 4,false => some (some ⟨true,false,2⟩)
  | 4,true => some (some ⟨false,false,0⟩)
  | 5,false => some (some ⟨true,false,4⟩)
  | 5,true => some (some ⟨false,false,5⟩)
  | _,_ => none

def family (n : Nat) : Z0 := ⟨4,[],([true,false,false,true,false]) ++ (rep [false,true,false,false,true,false] (n)) ++ ([true])⟩

theorem entry : run0 table 17 ⟨0,[],[]⟩ = some (family 0) := by rfl

theorem phase0 (n : Nat) : run0 table 2 ⟨4,[],([true,false,false,true,false]) ++ (rep [false,true,false,false,true,false] (n)) ++ ([true])⟩ = some ⟨3,([true,false]),([true,false,false,true,false]) ++ (rep [false,true,false,false,true,false] (n)) ++ ([true])⟩ := by rfl

theorem local1 (L R : List Bool) : run0 table 30 ⟨3,([true,false]) ++ (L),([true,false,false,true,false]) ++ ([false,true,false,false,true,false]) ++ (R)⟩ = some ⟨3,([true,false]) ++ ([true,false,false,true,false,false]) ++ (L),([true,false,false,true,false]) ++ (R)⟩ := by rfl

theorem phase1 (n : Nat) : run0 table (30*n) ⟨3,([true,false]),([true,false,false,true,false]) ++ (rep [false,true,false,false,true,false] (n)) ++ ([true])⟩ = some ⟨3,([true,false]) ++ (rep [true,false,false,true,false,false] (n)),([true,false,false,true,false,true])⟩ := by
  simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using sweepR table 3 [true,false] [true,false,false,true,false] [false,true,false,false,true,false] [true,false,false,true,false,false] 30 local1 n ([]) (([true]))

theorem phase2 (n : Nat) : run0 table 27 ⟨3,([true,false]) ++ (rep [true,false,false,true,false,false] (n)),([true,false,false,true,false,true])⟩ = some ⟨5,([true,false,true,false,false,true,false,false,true,false,false]) ++ (rep [true,false,false,true,false,false] (n)),([true])⟩ := by rfl

theorem local3 (L R : List Bool) : run0 table 14 ⟨5,([true,false,true,false,false,true,false,false,true,false,false]) ++ ([true,false,false,true,false,false]) ++ (L),(R)⟩ = some ⟨5,([true,false,true,false,false,true,false,false,true,false,false]) ++ (L),([false,true,false,false,true,false]) ++ (R)⟩ := by rfl

theorem phase3 (n : Nat) : run0 table (14*n) ⟨5,([true,false,true,false,false,true,false,false,true,false,false]) ++ (rep [true,false,false,true,false,false] (n)),([true])⟩ = some ⟨5,([true,false,true,false,false,true,false,false,true,false,false]),(rep [false,true,false,false,true,false] (n)) ++ ([true])⟩ := by
  simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using sweepL table 5 [true,false,true,false,false,true,false,false,true,false,false] [] [true,false,false,true,false,false] [false,true,false,false,true,false] 14 local3 n ([]) (([true]))

theorem phase4 (n : Nat) : run0 table 23 ⟨5,([true,false,true,false,false,true,false,false,true,false,false]),(rep [false,true,false,false,true,false] (n)) ++ ([true])⟩ = some ⟨4,[],([true,false,false,true,false,false,true,false,false,true,false]) ++ (rep [false,true,false,false,true,false] (n)) ++ ([true])⟩ := by rfl

theorem finalL (n : Nat) : ([] : List Bool) = [] := by
  rfl

theorem finalR (n : Nat) : ([true,false,false,true,false,false,true,false,false,true,false]) ++ (rep [false,true,false,false,true,false] (n)) ++ ([true]) = ([true,false,false,true,false,false,true,false,false,true,false]) ++ (rep [false,true,false,false,true,false] (n)) ++ ([true]) := by
  rfl

theorem growth (n : Nat) : run0 table (52+44*n) (family n) = some (family (n+1)) := by
  have H := (join0 (join0 (join0 (join0 (phase0 n) (phase1 n)) (phase2 n)) (phase3 n)) (phase4 n))
  rw [show 2+30*n+27+14*n+23=52+44*n by omega] at H
  simpa only [family,rep,List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using H

theorem never (m : Machine) (hm : compatible table m) : NeverHalts m :=
  never_of_growth table family 17 (fun n => 52+44*n) entry (by intro n; omega) growth m hm

#print axioms never

end M1520

namespace M1614

-- 1RB1RC_1RC1RD_0RD1LF_1LD0RA_0LC---_0LB1LE

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
  | 4,false => some (some ⟨false,false,2⟩)
  | 5,false => some (some ⟨false,false,1⟩)
  | 5,true => some (some ⟨true,false,4⟩)
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

end M1614

namespace M1639

-- 1RB1RC_1RC1LE_0RD1LF_1LD0RA_1LF---_0LB1LE

def table : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 0,true => some (some ⟨true,true,2⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 1,true => some (some ⟨true,false,4⟩)
  | 2,false => some (some ⟨false,true,3⟩)
  | 2,true => some (some ⟨true,false,5⟩)
  | 3,false => some (some ⟨true,false,3⟩)
  | 3,true => some (some ⟨false,true,0⟩)
  | 4,false => some (some ⟨true,false,5⟩)
  | 5,false => some (some ⟨false,false,1⟩)
  | 5,true => some (some ⟨true,false,4⟩)
  | _,_ => none

def family (n : Nat) : Z0 := ⟨4,[],([true]) ++ (rep [false,true,true] (n)) ++ ([true,true,true])⟩

theorem entry : run0 table 11 ⟨0,[],[]⟩ = some (family 0) := by rfl

theorem phase0 (n : Nat) : run0 table 3 ⟨4,[],([true]) ++ (rep [false,true,true] (n)) ++ ([true,true,true])⟩ = some ⟨2,([false,true]),([true,true]) ++ (rep [false,true,true] (n)) ++ ([true,true,true])⟩ := by rfl

theorem local1 (L R : List Bool) : run0 table 3 ⟨2,([false]) ++ (L),([true,true]) ++ ([false,true,true]) ++ (R)⟩ = some ⟨2,([false]) ++ ([true,false,false]) ++ (L),([true,true]) ++ (R)⟩ := by rfl

theorem phase1 (n : Nat) : run0 table (3*n) ⟨2,([false,true]),([true,true]) ++ (rep [false,true,true] (n)) ++ ([true,true,true])⟩ = some ⟨2,([false]) ++ (rep [true,false,false] (n)) ++ ([true]),([true,true,true,true,true])⟩ := by
  simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using sweepR table 2 [false] [true,true] [false,true,true] [true,false,false] 3 local1 n (([true])) (([true,true,true]))

theorem phase2 (n : Nat) : run0 table 5 ⟨2,([false]) ++ (rep [true,false,false] (n)) ++ ([true]),([true,true,true,true,true])⟩ = some ⟨4,([false,false]) ++ (rep [true,false,false] (n)) ++ ([true]),([true,true,true,true])⟩ := by rfl

theorem local3 (L R : List Bool) : run0 table 3 ⟨4,([false,false]) ++ ([true,false,false]) ++ (L),(R)⟩ = some ⟨4,([false,false]) ++ (L),([true,false,true]) ++ (R)⟩ := by rfl

theorem phase3 (n : Nat) : run0 table (3*n) ⟨4,([false,false]) ++ (rep [true,false,false] (n)) ++ ([true]),([true,true,true,true])⟩ = some ⟨4,([false,false,true]),(rep [true,false,true] (n)) ++ ([true,true,true,true])⟩ := by
  simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using sweepL table 4 [false,false] [] [true,false,false] [true,false,true] 3 local3 n (([true])) (([true,true,true,true]))

theorem phase4 (n : Nat) : run0 table 3 ⟨4,([false,false,true]),(rep [true,false,true] (n)) ++ ([true,true,true,true])⟩ = some ⟨4,[],([true,false,true]) ++ (rep [true,false,true] (n)) ++ ([true,true,true,true])⟩ := by rfl

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

end M1639

namespace M1641

-- 1RB1RC_1RC---_0RD1LF_1LD0RA_1RA0LF_1LB1LE

def table : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 0,true => some (some ⟨true,true,2⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 2,false => some (some ⟨false,true,3⟩)
  | 2,true => some (some ⟨true,false,5⟩)
  | 3,false => some (some ⟨true,false,3⟩)
  | 3,true => some (some ⟨false,true,0⟩)
  | 4,false => some (some ⟨true,true,0⟩)
  | 4,true => some (some ⟨false,false,5⟩)
  | 5,false => some (some ⟨true,false,1⟩)
  | 5,true => some (some ⟨true,false,4⟩)
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

end M1641

namespace M1683

-- 1RB1RC_1RC---_0RD1LF_1LD0RA_1LC0LE_1LB1RE

def table : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 0,true => some (some ⟨true,true,2⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 2,false => some (some ⟨false,true,3⟩)
  | 2,true => some (some ⟨true,false,5⟩)
  | 3,false => some (some ⟨true,false,3⟩)
  | 3,true => some (some ⟨false,true,0⟩)
  | 4,false => some (some ⟨true,false,2⟩)
  | 4,true => some (some ⟨false,false,4⟩)
  | 5,false => some (some ⟨true,false,1⟩)
  | 5,true => some (some ⟨true,true,4⟩)
  | _,_ => none

def family (n : Nat) : Z0 := ⟨4,[],([false,false,true,true,false,false]) ++ (rep [true,true,false,false] (n))⟩

theorem entry : run0 table 19 ⟨0,[],[]⟩ = some (family 0) := by rfl

theorem phase0 (n : Nat) : run0 table 2 ⟨4,[],([false,false,true,true,false,false]) ++ (rep [true,true,false,false] (n))⟩ = some ⟨3,([true,false]),([false,false,true,true,false,false]) ++ (rep [true,true,false,false] (n))⟩ := by rfl

theorem local1 (L R : List Bool) : run0 table 14 ⟨3,([true,false]) ++ (L),([false,false,true,true,false,false]) ++ ([true,true,false,false]) ++ (R)⟩ = some ⟨3,([true,false]) ++ ([true,true,false,false]) ++ (L),([false,false,true,true,false,false]) ++ (R)⟩ := by rfl

theorem phase1 (n : Nat) : run0 table (14*n) ⟨3,([true,false]),([false,false,true,true,false,false]) ++ (rep [true,true,false,false] (n))⟩ = some ⟨3,([true,false]) ++ (rep [true,true,false,false] (n)),([false,false,true,true,false,false])⟩ := by
  simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using sweepR table 3 [true,false] [false,false,true,true,false,false] [true,true,false,false] [true,true,false,false] 14 local1 n ([]) ([])

theorem phase2 (n : Nat) : run0 table 18 ⟨3,([true,false]) ++ (rep [true,true,false,false] (n)),([false,false,true,true,false,false])⟩ = some ⟨3,([false,false,true,true,false,false,true,true,false,false]) ++ (rep [true,true,false,false] (n)),[]⟩ := by rfl

theorem local3 (L R : List Bool) : run0 table 24 ⟨3,([false,false,true,true,false,false,true,true,false,false]) ++ ([true,true,false,false]) ++ (L),(R)⟩ = some ⟨3,([false,false,true,true,false,false,true,true,false,false]) ++ (L),([true,true,false,false]) ++ (R)⟩ := by rfl

theorem phase3 (n : Nat) : run0 table (24*n) ⟨3,([false,false,true,true,false,false,true,true,false,false]) ++ (rep [true,true,false,false] (n)),[]⟩ = some ⟨3,([false,false,true,true,false,false,true,true,false,false]),(rep [true,true,false,false] (n))⟩ := by
  simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using sweepL table 3 [false,false,true,true,false,false,true,true,false,false] [] [true,true,false,false] [true,true,false,false] 24 local3 n ([]) ([])

theorem phase4 (n : Nat) : run0 table 40 ⟨3,([false,false,true,true,false,false,true,true,false,false]),(rep [true,true,false,false] (n))⟩ = some ⟨4,[],([false,false,true,true,false,false,true,true,false,false]) ++ (rep [true,true,false,false] (n))⟩ := by rfl

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

end M1683

end BB6.Agent11Raw39B1RCPumps
