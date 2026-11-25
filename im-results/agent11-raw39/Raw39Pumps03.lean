import SweepPumping
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedVariables false
namespace BB6.Agent11Raw39Pumps
open BB6Coverage BB6Coverage.Agent31Pump


namespace M1525

-- 1RB1RB_1RC1LE_0RD0RF_1LD0RA_---0LD_0RB0RB

def table : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 0,true => some (some ⟨true,true,1⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 1,true => some (some ⟨true,false,4⟩)
  | 2,false => some (some ⟨false,true,3⟩)
  | 2,true => some (some ⟨false,true,5⟩)
  | 3,false => some (some ⟨true,false,3⟩)
  | 3,true => some (some ⟨false,true,0⟩)
  | 4,true => some (some ⟨false,false,3⟩)
  | 5,false => some (some ⟨false,true,1⟩)
  | 5,true => some (some ⟨false,true,1⟩)
  | _,_ => none

def family (n : Nat) : Z0 := ⟨1,([false]) ++ (rep [false,false,true] (n)) ++ ([true]) ++ (rep [false] (n)),[]⟩

theorem entry : run0 table 1 ⟨0,[],[]⟩ = some (family 0) := by rfl

theorem phase0 (n : Nat) : run0 table 2 ⟨1,([false]) ++ (rep [false,false,true] (n)) ++ ([true]) ++ (rep [false] (n)),[]⟩ = some ⟨3,([false,false,true]) ++ (rep [false,false,true] (n)) ++ ([true]) ++ (rep [false] (n)),[]⟩ := by rfl

theorem local1 (L R : List Bool) : run0 table 7 ⟨3,([false,false,true]) ++ ([false,false,true]) ++ (L),(R)⟩ = some ⟨3,([false,false,true]) ++ (L),([true,false,true]) ++ (R)⟩ := by rfl

theorem phase1 (n : Nat) : run0 table (7*n) ⟨3,([false,false,true]) ++ (rep [false,false,true] (n)) ++ ([true]) ++ (rep [false] (n)),[]⟩ = some ⟨3,([false,false,true,true]) ++ (rep [false] (n)),(rep [true,false,true] (n))⟩ := by
  simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using sweepL table 3 [false,false,true] [] [false,false,true] [true,false,true] 7 local1 n (([true]) ++ (rep [false] (n))) ([])

theorem phase2 (n : Nat) : run0 table 9 ⟨3,([false,false,true,true]) ++ (rep [false] (n)),(rep [true,false,true] (n))⟩ = some ⟨1,([false,true,false]) ++ (rep [false] (n)),([true]) ++ (rep [true,false,true] (n))⟩ := by rfl

theorem local3 (L R : List Bool) : run0 table 3 ⟨1,([false]) ++ (L),([true]) ++ ([true,false,true]) ++ (R)⟩ = some ⟨1,([false]) ++ ([false,false,true]) ++ (L),([true]) ++ (R)⟩ := by rfl

theorem phase3 (n : Nat) : run0 table (3*n) ⟨1,([false,true,false]) ++ (rep [false] (n)),([true]) ++ (rep [true,false,true] (n))⟩ = some ⟨1,([false]) ++ (rep [false,false,true] (n)) ++ ([true,false]) ++ (rep [false] (n)),([true])⟩ := by
  simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using sweepR table 1 [false] [true] [true,false,true] [false,false,true] 3 local3 n (([true,false]) ++ (rep [false] (n))) ([])

theorem phase4 (n : Nat) : run0 table 3 ⟨1,([false]) ++ (rep [false,false,true] (n)) ++ ([true,false]) ++ (rep [false] (n)),([true])⟩ = some ⟨1,([false,false,false,true]) ++ (rep [false,false,true] (n)) ++ ([true,false]) ++ (rep [false] (n)),[]⟩ := by rfl

theorem finalL (n : Nat) : ([false,false,false,true]) ++ (rep [false,false,true] (n)) ++ ([true,false]) ++ (rep [false] (n)) = ([false,false,false,true]) ++ (rep [false,false,true] (n)) ++ ([true,false]) ++ (rep [false] (n)) := by
  rfl

theorem finalR (n : Nat) : ([] : List Bool) = [] := by
  rfl

theorem growth (n : Nat) : run0 table (14+10*n) (family n) = some (family (n+1)) := by
  have H := (join0 (join0 (join0 (join0 (phase0 n) (phase1 n)) (phase2 n)) (phase3 n)) (phase4 n))
  rw [show 2+7*n+9+3*n+3=14+10*n by omega] at H
  simpa only [family,rep,List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using H

theorem never (m : Machine) (hm : compatible table m) : NeverHalts m :=
  never_of_growth table family 1 (fun n => 14+10*n) entry (by intro n; omega) growth m hm

#print axioms never

end M1525

namespace M1531

-- 1RB1RB_1RC1LE_0RD0RF_1LD0RA_---0LD_0RD0RB

def table : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 0,true => some (some ⟨true,true,1⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 1,true => some (some ⟨true,false,4⟩)
  | 2,false => some (some ⟨false,true,3⟩)
  | 2,true => some (some ⟨false,true,5⟩)
  | 3,false => some (some ⟨true,false,3⟩)
  | 3,true => some (some ⟨false,true,0⟩)
  | 4,true => some (some ⟨false,false,3⟩)
  | 5,false => some (some ⟨false,true,3⟩)
  | 5,true => some (some ⟨false,true,1⟩)
  | _,_ => none

def family (n : Nat) : Z0 := ⟨1,([false]) ++ (rep [false,false,true] (n)) ++ ([true]) ++ (rep [false,false] (n)),[]⟩

theorem entry : run0 table 1 ⟨0,[],[]⟩ = some (family 0) := by rfl

theorem phase0 (n : Nat) : run0 table 2 ⟨1,([false]) ++ (rep [false,false,true] (n)) ++ ([true]) ++ (rep [false,false] (n)),[]⟩ = some ⟨3,([false,false,true]) ++ (rep [false,false,true] (n)) ++ ([true]) ++ (rep [false,false] (n)),[]⟩ := by rfl

theorem local1 (L R : List Bool) : run0 table 7 ⟨3,([false,false,true]) ++ ([false,false,true]) ++ (L),(R)⟩ = some ⟨3,([false,false,true]) ++ (L),([true,false,true]) ++ (R)⟩ := by rfl

theorem phase1 (n : Nat) : run0 table (7*n) ⟨3,([false,false,true]) ++ (rep [false,false,true] (n)) ++ ([true]) ++ (rep [false,false] (n)),[]⟩ = some ⟨3,([false,false,true,true]) ++ (rep [false,false] (n)),(rep [true,false,true] (n))⟩ := by
  simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using sweepL table 3 [false,false,true] [] [false,false,true] [true,false,true] 7 local1 n (([true]) ++ (rep [false,false] (n))) ([])

theorem phase2 (n : Nat) : run0 table 9 ⟨3,([false,false,true,true]) ++ (rep [false,false] (n)),(rep [true,false,true] (n))⟩ = some ⟨1,([false,true,false]) ++ (rep [false,false] (n)),([true]) ++ (rep [true,false,true] (n))⟩ := by rfl

theorem local3 (L R : List Bool) : run0 table 3 ⟨1,([false]) ++ (L),([true]) ++ ([true,false,true]) ++ (R)⟩ = some ⟨1,([false]) ++ ([false,false,true]) ++ (L),([true]) ++ (R)⟩ := by rfl

theorem phase3 (n : Nat) : run0 table (3*n) ⟨1,([false,true,false]) ++ (rep [false,false] (n)),([true]) ++ (rep [true,false,true] (n))⟩ = some ⟨1,([false]) ++ (rep [false,false,true] (n)) ++ ([true,false]) ++ (rep [false,false] (n)),([true])⟩ := by
  simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using sweepR table 1 [false] [true] [true,false,true] [false,false,true] 3 local3 n (([true,false]) ++ (rep [false,false] (n))) ([])

theorem phase4 (n : Nat) : run0 table 3 ⟨1,([false]) ++ (rep [false,false,true] (n)) ++ ([true,false]) ++ (rep [false,false] (n)),([true])⟩ = some ⟨3,([false,false,false,true]) ++ (rep [false,false,true] (n)) ++ ([true,false]) ++ (rep [false,false] (n)),[]⟩ := by rfl

theorem local5 (L R : List Bool) : run0 table 7 ⟨3,([false,false,false,true]) ++ ([false,false,true]) ++ (L),(R)⟩ = some ⟨3,([false,false,false,true]) ++ (L),([false,true,true]) ++ (R)⟩ := by rfl

theorem phase5 (n : Nat) : run0 table (7*n) ⟨3,([false,false,false,true]) ++ (rep [false,false,true] (n)) ++ ([true,false]) ++ (rep [false,false] (n)),[]⟩ = some ⟨3,([false,false,false,true,true,false]) ++ (rep [false,false] (n)),(rep [false,true,true] (n))⟩ := by
  simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using sweepL table 3 [false,false,false,true] [] [false,false,true] [false,true,true] 7 local5 n (([true,false]) ++ (rep [false,false] (n))) ([])

theorem phase6 (n : Nat) : run0 table 10 ⟨3,([false,false,false,true,true,false]) ++ (rep [false,false] (n)),(rep [false,true,true] (n))⟩ = some ⟨1,([false,true,false,false]) ++ (rep [false,false] (n)),([true,true]) ++ (rep [false,true,true] (n))⟩ := by rfl

theorem local7 (L R : List Bool) : run0 table 3 ⟨1,([false]) ++ (L),([true,true]) ++ ([false,true,true]) ++ (R)⟩ = some ⟨1,([false]) ++ ([false,false,true]) ++ (L),([true,true]) ++ (R)⟩ := by rfl

theorem phase7 (n : Nat) : run0 table (3*n) ⟨1,([false,true,false,false]) ++ (rep [false,false] (n)),([true,true]) ++ (rep [false,true,true] (n))⟩ = some ⟨1,([false]) ++ (rep [false,false,true] (n)) ++ ([true,false,false]) ++ (rep [false,false] (n)),([true,true])⟩ := by
  simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using sweepR table 1 [false] [true,true] [false,true,true] [false,false,true] 3 local7 n (([true,false,false]) ++ (rep [false,false] (n))) ([])

theorem phase8 (n : Nat) : run0 table 3 ⟨1,([false]) ++ (rep [false,false,true] (n)) ++ ([true,false,false]) ++ (rep [false,false] (n)),([true,true])⟩ = some ⟨1,([false,false,false,true]) ++ (rep [false,false,true] (n)) ++ ([true,false,false]) ++ (rep [false,false] (n)),[]⟩ := by rfl

theorem finalL (n : Nat) : ([false,false,false,true]) ++ (rep [false,false,true] (n)) ++ ([true,false,false]) ++ (rep [false,false] (n)) = ([false,false,false,true]) ++ (rep [false,false,true] (n)) ++ ([true,false,false]) ++ (rep [false,false] (n)) := by
  rfl

theorem finalR (n : Nat) : ([] : List Bool) = [] := by
  rfl

theorem growth (n : Nat) : run0 table (27+20*n) (family n) = some (family (n+1)) := by
  have H := (join0 (join0 (join0 (join0 (join0 (join0 (join0 (join0 (phase0 n) (phase1 n)) (phase2 n)) (phase3 n)) (phase4 n)) (phase5 n)) (phase6 n)) (phase7 n)) (phase8 n))
  rw [show 2+7*n+9+3*n+3+7*n+10+3*n+3=27+20*n by omega] at H
  simpa only [family,rep,List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using H

theorem never (m : Machine) (hm : compatible table m) : NeverHalts m :=
  never_of_growth table family 1 (fun n => 27+20*n) entry (by intro n; omega) growth m hm

#print axioms never

end M1531

namespace M1540

-- 1RB1RB_1RC1LE_0RD1RF_1LD0RA_---0LD_0RC0RB

def table : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 0,true => some (some ⟨true,true,1⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 1,true => some (some ⟨true,false,4⟩)
  | 2,false => some (some ⟨false,true,3⟩)
  | 2,true => some (some ⟨true,true,5⟩)
  | 3,false => some (some ⟨true,false,3⟩)
  | 3,true => some (some ⟨false,true,0⟩)
  | 4,true => some (some ⟨false,false,3⟩)
  | 5,false => some (some ⟨false,true,2⟩)
  | 5,true => some (some ⟨false,true,1⟩)
  | _,_ => none

def family (n : Nat) : Z0 := ⟨1,([false]) ++ (rep [false,true] (n)) ++ ([true]) ++ (rep [true,false,true,false] (n)),[]⟩

theorem entry : run0 table 1 ⟨0,[],[]⟩ = some (family 0) := by rfl

theorem phase0 (n : Nat) : run0 table 2 ⟨1,([false]) ++ (rep [false,true] (n)) ++ ([true]) ++ (rep [true,false,true,false] (n)),[]⟩ = some ⟨3,([false,false,true]) ++ (rep [false,true] (n)) ++ ([true]) ++ (rep [true,false,true,false] (n)),[]⟩ := by rfl

theorem local1 (L R : List Bool) : run0 table 6 ⟨3,([false,false,true]) ++ ([false,true]) ++ (L),(R)⟩ = some ⟨3,([false,false,true]) ++ (L),([false,true]) ++ (R)⟩ := by rfl

theorem phase1 (n : Nat) : run0 table (6*n) ⟨3,([false,false,true]) ++ (rep [false,true] (n)) ++ ([true]) ++ (rep [true,false,true,false] (n)),[]⟩ = some ⟨3,([false,false,true,true]) ++ (rep [true,false,true,false] (n)),(rep [false,true] (n))⟩ := by
  simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using sweepL table 3 [false,false,true] [] [false,true] [false,true] 6 local1 n (([true]) ++ (rep [true,false,true,false] (n))) ([])

theorem phase2 (n : Nat) : run0 table 10 ⟨3,([false,false,true,true]) ++ (rep [true,false,true,false] (n)),(rep [false,true] (n))⟩ = some ⟨2,([true,true,true,false]) ++ (rep [true,false,true,false] (n)),(rep [false,true] (n))⟩ := by rfl

theorem local3 (L R : List Bool) : run0 table 2 ⟨2,([true]) ++ (L),([false,true]) ++ (R)⟩ = some ⟨2,([true]) ++ ([false,true]) ++ (L),(R)⟩ := by rfl

theorem phase3 (n : Nat) : run0 table (2*n) ⟨2,([true,true,true,false]) ++ (rep [true,false,true,false] (n)),(rep [false,true] (n))⟩ = some ⟨2,([true]) ++ (rep [false,true] (n)) ++ ([true,true,false]) ++ (rep [true,false,true,false] (n)),[]⟩ := by
  simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using sweepR table 2 [true] [] [false,true] [false,true] 2 local3 n (([true,true,false]) ++ (rep [true,false,true,false] (n))) ([])

theorem phase4 (n : Nat) : run0 table 4 ⟨2,([true]) ++ (rep [false,true] (n)) ++ ([true,true,false]) ++ (rep [true,false,true,false] (n)),[]⟩ = some ⟨3,([false,false,true]) ++ (rep [false,true] (n)) ++ ([true,true,false]) ++ (rep [true,false,true,false] (n)),([true])⟩ := by rfl

theorem local5 (L R : List Bool) : run0 table 6 ⟨3,([false,false,true]) ++ ([false,true]) ++ (L),(R)⟩ = some ⟨3,([false,false,true]) ++ (L),([false,true]) ++ (R)⟩ := by rfl

theorem phase5 (n : Nat) : run0 table (6*n) ⟨3,([false,false,true]) ++ (rep [false,true] (n)) ++ ([true,true,false]) ++ (rep [true,false,true,false] (n)),([true])⟩ = some ⟨3,([false,false,true,true,true,false]) ++ (rep [true,false,true,false] (n)),(rep [false,true] (n)) ++ ([true])⟩ := by
  simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using sweepL table 3 [false,false,true] [] [false,true] [false,true] 6 local5 n (([true,true,false]) ++ (rep [true,false,true,false] (n))) (([true]))

theorem phase6 (n : Nat) : run0 table 10 ⟨3,([false,false,true,true,true,false]) ++ (rep [true,false,true,false] (n)),(rep [false,true] (n)) ++ ([true])⟩ = some ⟨2,([true,true,true,false,true,false]) ++ (rep [true,false,true,false] (n)),(rep [false,true] (n)) ++ ([true])⟩ := by rfl

theorem local7 (L R : List Bool) : run0 table 2 ⟨2,([true]) ++ (L),([false,true]) ++ (R)⟩ = some ⟨2,([true]) ++ ([false,true]) ++ (L),(R)⟩ := by rfl

theorem phase7 (n : Nat) : run0 table (2*n) ⟨2,([true,true,true,false,true,false]) ++ (rep [true,false,true,false] (n)),(rep [false,true] (n)) ++ ([true])⟩ = some ⟨2,([true]) ++ (rep [false,true] (n)) ++ ([true,true,false,true,false]) ++ (rep [true,false,true,false] (n)),([true])⟩ := by
  simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using sweepR table 2 [true] [] [false,true] [false,true] 2 local7 n (([true,true,false,true,false]) ++ (rep [true,false,true,false] (n))) (([true]))

theorem phase8 (n : Nat) : run0 table 2 ⟨2,([true]) ++ (rep [false,true] (n)) ++ ([true,true,false,true,false]) ++ (rep [true,false,true,false] (n)),([true])⟩ = some ⟨1,([false,false,true]) ++ (rep [false,true] (n)) ++ ([true,true,false,true,false]) ++ (rep [true,false,true,false] (n)),[]⟩ := by rfl

theorem finalL (n : Nat) : ([false,false,true]) ++ (rep [false,true] (n)) ++ ([true,true,false,true,false]) ++ (rep [true,false,true,false] (n)) = ([false,false,true]) ++ (rep [false,true] (n)) ++ ([true,true,false,true,false]) ++ (rep [true,false,true,false] (n)) := by
  rfl

theorem finalR (n : Nat) : ([] : List Bool) = [] := by
  rfl

theorem growth (n : Nat) : run0 table (28+16*n) (family n) = some (family (n+1)) := by
  have H := (join0 (join0 (join0 (join0 (join0 (join0 (join0 (join0 (phase0 n) (phase1 n)) (phase2 n)) (phase3 n)) (phase4 n)) (phase5 n)) (phase6 n)) (phase7 n)) (phase8 n))
  rw [show 2+6*n+10+2*n+4+6*n+10+2*n+2=28+16*n by omega] at H
  simpa only [family,rep,List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using H

theorem never (m : Machine) (hm : compatible table m) : NeverHalts m :=
  never_of_growth table family 1 (fun n => 28+16*n) entry (by intro n; omega) growth m hm

#print axioms never

end M1540

namespace M1552

-- 1RB1RB_1RC1LE_0RD0RF_1LD0RA_0LD0LE_0RB---

def table : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 0,true => some (some ⟨true,true,1⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 1,true => some (some ⟨true,false,4⟩)
  | 2,false => some (some ⟨false,true,3⟩)
  | 2,true => some (some ⟨false,true,5⟩)
  | 3,false => some (some ⟨true,false,3⟩)
  | 3,true => some (some ⟨false,true,0⟩)
  | 4,false => some (some ⟨false,false,3⟩)
  | 4,true => some (some ⟨false,false,4⟩)
  | 5,false => some (some ⟨false,true,1⟩)
  | _,_ => none

def family (n : Nat) : Z0 := ⟨1,([false]) ++ (rep [false,false,true] (n)) ++ ([true]) ++ (rep [false] (n)),[]⟩

theorem entry : run0 table 1 ⟨0,[],[]⟩ = some (family 0) := by rfl

theorem phase0 (n : Nat) : run0 table 2 ⟨1,([false]) ++ (rep [false,false,true] (n)) ++ ([true]) ++ (rep [false] (n)),[]⟩ = some ⟨3,([false,false,true]) ++ (rep [false,false,true] (n)) ++ ([true]) ++ (rep [false] (n)),[]⟩ := by rfl

theorem local1 (L R : List Bool) : run0 table 7 ⟨3,([false,false,true]) ++ ([false,false,true]) ++ (L),(R)⟩ = some ⟨3,([false,false,true]) ++ (L),([false,false,true]) ++ (R)⟩ := by rfl

theorem phase1 (n : Nat) : run0 table (7*n) ⟨3,([false,false,true]) ++ (rep [false,false,true] (n)) ++ ([true]) ++ (rep [false] (n)),[]⟩ = some ⟨3,([false,false,true,true]) ++ (rep [false] (n)),(rep [false,false,true] (n))⟩ := by
  simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using sweepL table 3 [false,false,true] [] [false,false,true] [false,false,true] 7 local1 n (([true]) ++ (rep [false] (n))) ([])

theorem phase2 (n : Nat) : run0 table 9 ⟨3,([false,false,true,true]) ++ (rep [false] (n)),(rep [false,false,true] (n))⟩ = some ⟨1,([false,true,false]) ++ (rep [false] (n)),([true]) ++ (rep [false,false,true] (n))⟩ := by rfl

theorem local3 (L R : List Bool) : run0 table 3 ⟨1,([false]) ++ (L),([true]) ++ ([false,false,true]) ++ (R)⟩ = some ⟨1,([false]) ++ ([false,false,true]) ++ (L),([true]) ++ (R)⟩ := by rfl

theorem phase3 (n : Nat) : run0 table (3*n) ⟨1,([false,true,false]) ++ (rep [false] (n)),([true]) ++ (rep [false,false,true] (n))⟩ = some ⟨1,([false]) ++ (rep [false,false,true] (n)) ++ ([true,false]) ++ (rep [false] (n)),([true])⟩ := by
  simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using sweepR table 1 [false] [true] [false,false,true] [false,false,true] 3 local3 n (([true,false]) ++ (rep [false] (n))) ([])

theorem phase4 (n : Nat) : run0 table 3 ⟨1,([false]) ++ (rep [false,false,true] (n)) ++ ([true,false]) ++ (rep [false] (n)),([true])⟩ = some ⟨1,([false,false,false,true]) ++ (rep [false,false,true] (n)) ++ ([true,false]) ++ (rep [false] (n)),[]⟩ := by rfl

theorem finalL (n : Nat) : ([false,false,false,true]) ++ (rep [false,false,true] (n)) ++ ([true,false]) ++ (rep [false] (n)) = ([false,false,false,true]) ++ (rep [false,false,true] (n)) ++ ([true,false]) ++ (rep [false] (n)) := by
  rfl

theorem finalR (n : Nat) : ([] : List Bool) = [] := by
  rfl

theorem growth (n : Nat) : run0 table (14+10*n) (family n) = some (family (n+1)) := by
  have H := (join0 (join0 (join0 (join0 (phase0 n) (phase1 n)) (phase2 n)) (phase3 n)) (phase4 n))
  rw [show 2+7*n+9+3*n+3=14+10*n by omega] at H
  simpa only [family,rep,List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using H

theorem never (m : Machine) (hm : compatible table m) : NeverHalts m :=
  never_of_growth table family 1 (fun n => 14+10*n) entry (by intro n; omega) growth m hm

#print axioms never

end M1552

namespace M1583

-- 1RB1RB_1RC1LE_0RD0RA_1LD0RA_0LB0LF_0LB---

def table : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 0,true => some (some ⟨true,true,1⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 1,true => some (some ⟨true,false,4⟩)
  | 2,false => some (some ⟨false,true,3⟩)
  | 2,true => some (some ⟨false,true,0⟩)
  | 3,false => some (some ⟨true,false,3⟩)
  | 3,true => some (some ⟨false,true,0⟩)
  | 4,false => some (some ⟨false,false,1⟩)
  | 4,true => some (some ⟨false,false,5⟩)
  | 5,false => some (some ⟨false,false,1⟩)
  | _,_ => none

def family (n : Nat) : Z0 := ⟨4,[],(rep [true,false,false,true,true,false,false,true,false,false,true,true,false,false] (n)) ++ ([true,false,false,true])⟩

theorem entry : run0 table 11 ⟨0,[],[]⟩ = some (family 0) := by rfl

theorem phase0 (n : Nat) : run0 table 2 ⟨4,[],(rep [true,false,false,true,true,false,false,true,false,false,true,true,false,false] (n)) ++ ([true,false,false,true])⟩ = some ⟨2,([false,true]),(rep [true,false,false,true,true,false,false,true,false,false,true,true,false,false] (n)) ++ ([true,false,false,true])⟩ := by rfl

theorem local1 (L R : List Bool) : run0 table 14 ⟨2,([false]) ++ (L),([true,false,false,true,true,false,false,true,false,false,true,true,false,false]) ++ (R)⟩ = some ⟨2,([false]) ++ ([true,true,false,true,true,false,false,true,true,false,true,true,false,false]) ++ (L),(R)⟩ := by rfl

theorem phase1 (n : Nat) : run0 table (14*n) ⟨2,([false,true]),(rep [true,false,false,true,true,false,false,true,false,false,true,true,false,false] (n)) ++ ([true,false,false,true])⟩ = some ⟨2,([false]) ++ (rep [true,true,false,true,true,false,false,true,true,false,true,true,false,false] (n)) ++ ([true]),([true,false,false,true])⟩ := by
  simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using sweepR table 2 [false] [] [true,false,false,true,true,false,false,true,false,false,true,true,false,false] [true,true,false,true,true,false,false,true,true,false,true,true,false,false] 14 local1 n (([true])) (([true,false,false,true]))

theorem phase2 (n : Nat) : run0 table 17 ⟨2,([false]) ++ (rep [true,true,false,true,true,false,false,true,true,false,true,true,false,false] (n)) ++ ([true]),([true,false,false,true])⟩ = some ⟨1,([true,true,false,false]) ++ (rep [true,true,false,true,true,false,false,true,true,false,true,true,false,false] (n)) ++ ([true]),([false,true,false,false,true])⟩ := by rfl

theorem local3 (L R : List Bool) : run0 table 30 ⟨1,([true,true,false,false]) ++ ([true,true,false,true,true,false,false,true,true,false,true,true,false,false]) ++ (L),(R)⟩ = some ⟨1,([true,true,false,false]) ++ (L),([false,false,true,false,false,true,true,false,false,true,false,false,true,true]) ++ (R)⟩ := by rfl

theorem phase3 (n : Nat) : run0 table (30*n) ⟨1,([true,true,false,false]) ++ (rep [true,true,false,true,true,false,false,true,true,false,true,true,false,false] (n)) ++ ([true]),([false,true,false,false,true])⟩ = some ⟨1,([true,true,false,false,true]),(rep [false,false,true,false,false,true,true,false,false,true,false,false,true,true] (n)) ++ ([false,true,false,false,true])⟩ := by
  simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using sweepL table 1 [true,true,false,false] [] [true,true,false,true,true,false,false,true,true,false,true,true,false,false] [false,false,true,false,false,true,true,false,false,true,false,false,true,true] 30 local3 n (([true])) (([false,true,false,false,true]))

theorem phase4 (n : Nat) : run0 table 15 ⟨1,([true,true,false,false,true]),(rep [false,false,true,false,false,true,true,false,false,true,false,false,true,true] (n)) ++ ([false,true,false,false,true])⟩ = some ⟨2,([false,true]),([true,false,false,true,true]) ++ (rep [false,false,true,false,false,true,true,false,false,true,false,false,true,true] (n)) ++ ([false,true,false,false,true])⟩ := by rfl

theorem local5 (L R : List Bool) : run0 table 14 ⟨2,([false]) ++ (L),([true,false,false,true,true]) ++ ([false,false,true,false,false,true,true,false,false,true,false,false,true,true]) ++ (R)⟩ = some ⟨2,([false]) ++ ([true,true,false,true,true,false,false,true,true,false,true,true,false,false]) ++ (L),([true,false,false,true,true]) ++ (R)⟩ := by rfl

theorem phase5 (n : Nat) : run0 table (14*n) ⟨2,([false,true]),([true,false,false,true,true]) ++ (rep [false,false,true,false,false,true,true,false,false,true,false,false,true,true] (n)) ++ ([false,true,false,false,true])⟩ = some ⟨2,([false]) ++ (rep [true,true,false,true,true,false,false,true,true,false,true,true,false,false] (n)) ++ ([true]),([true,false,false,true,true,false,true,false,false,true])⟩ := by
  simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using sweepR table 2 [false] [true,false,false,true,true] [false,false,true,false,false,true,true,false,false,true,false,false,true,true] [true,true,false,true,true,false,false,true,true,false,true,true,false,false] 14 local5 n (([true])) (([false,true,false,false,true]))

theorem phase6 (n : Nat) : run0 table 23 ⟨2,([false]) ++ (rep [true,true,false,true,true,false,false,true,true,false,true,true,false,false] (n)) ++ ([true]),([true,false,false,true,true,false,true,false,false,true])⟩ = some ⟨1,([true,true,false,true,true,false,true,true,false,false]) ++ (rep [true,true,false,true,true,false,false,true,true,false,true,true,false,false] (n)) ++ ([true]),([false,true,false,false,true])⟩ := by rfl

theorem local7 (L R : List Bool) : run0 table 30 ⟨1,([true,true,false,true,true,false,true,true,false,false]) ++ ([true,true,false,true,true,false,false,true,true,false,true,true,false,false]) ++ (L),(R)⟩ = some ⟨1,([true,true,false,true,true,false,true,true,false,false]) ++ (L),([true,false,false,true,false,false,true,true,false,false,true,false,false,true]) ++ (R)⟩ := by rfl

theorem phase7 (n : Nat) : run0 table (30*n) ⟨1,([true,true,false,true,true,false,true,true,false,false]) ++ (rep [true,true,false,true,true,false,false,true,true,false,true,true,false,false] (n)) ++ ([true]),([false,true,false,false,true])⟩ = some ⟨1,([true,true,false,true,true,false,true,true,false,false,true]),(rep [true,false,false,true,false,false,true,true,false,false,true,false,false,true] (n)) ++ ([false,true,false,false,true])⟩ := by
  simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using sweepL table 1 [true,true,false,true,true,false,true,true,false,false] [] [true,true,false,true,true,false,false,true,true,false,true,true,false,false] [true,false,false,true,false,false,true,true,false,false,true,false,false,true] 30 local7 n (([true])) (([false,true,false,false,true]))

theorem phase8 (n : Nat) : run0 table 21 ⟨1,([true,true,false,true,true,false,true,true,false,false,true]),(rep [true,false,false,true,false,false,true,true,false,false,true,false,false,true] (n)) ++ ([false,true,false,false,true])⟩ = some ⟨2,([false,true]),([true,false,false,true,true,false,false,true,false,false,true]) ++ (rep [true,false,false,true,false,false,true,true,false,false,true,false,false,true] (n)) ++ ([false,true,false,false,true])⟩ := by rfl

theorem local9 (L R : List Bool) : run0 table 14 ⟨2,([false]) ++ (L),([true,false,false,true,true,false,false,true,false,false,true]) ++ ([true,false,false,true,false,false,true,true,false,false,true,false,false,true]) ++ (R)⟩ = some ⟨2,([false]) ++ ([true,true,false,true,true,false,false,true,true,false,true,true,false,false]) ++ (L),([true,false,false,true,true,false,false,true,false,false,true]) ++ (R)⟩ := by rfl

theorem phase9 (n : Nat) : run0 table (14*n) ⟨2,([false,true]),([true,false,false,true,true,false,false,true,false,false,true]) ++ (rep [true,false,false,true,false,false,true,true,false,false,true,false,false,true] (n)) ++ ([false,true,false,false,true])⟩ = some ⟨2,([false]) ++ (rep [true,true,false,true,true,false,false,true,true,false,true,true,false,false] (n)) ++ ([true]),([true,false,false,true,true,false,false,true,false,false,true,false,true,false,false,true])⟩ := by
  simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using sweepR table 2 [false] [true,false,false,true,true,false,false,true,false,false,true] [true,false,false,true,false,false,true,true,false,false,true,false,false,true] [true,true,false,true,true,false,false,true,true,false,true,true,false,false] 14 local9 n (([true])) (([false,true,false,false,true]))

theorem phase10 (n : Nat) : run0 table 13 ⟨2,([false]) ++ (rep [true,true,false,true,true,false,false,true,true,false,true,true,false,false] (n)) ++ ([true]),([true,false,false,true,true,false,false,true,false,false,true,false,true,false,false,true])⟩ = some ⟨1,([true,true,false,true,true,false,false,true,true,false,true,true,false,false]) ++ (rep [true,true,false,true,true,false,false,true,true,false,true,true,false,false] (n)) ++ ([true]),([false,false,true])⟩ := by rfl

theorem local11 (L R : List Bool) : run0 table 30 ⟨1,([true,true,false,true,true,false,false,true,true,false,true,true,false,false]) ++ ([true,true,false,true,true,false,false,true,true,false,true,true,false,false]) ++ (L),(R)⟩ = some ⟨1,([true,true,false,true,true,false,false,true,true,false,true,true,false,false]) ++ (L),([false,false,true,true,false,false,true,false,false,true,true,false,false,true]) ++ (R)⟩ := by rfl

theorem phase11 (n : Nat) : run0 table (30*n) ⟨1,([true,true,false,true,true,false,false,true,true,false,true,true,false,false]) ++ (rep [true,true,false,true,true,false,false,true,true,false,true,true,false,false] (n)) ++ ([true]),([false,false,true])⟩ = some ⟨1,([true,true,false,true,true,false,false,true,true,false,true,true,false,false,true]),(rep [false,false,true,true,false,false,true,false,false,true,true,false,false,true] (n)) ++ ([false,false,true])⟩ := by
  simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using sweepL table 1 [true,true,false,true,true,false,false,true,true,false,true,true,false,false] [] [true,true,false,true,true,false,false,true,true,false,true,true,false,false] [false,false,true,true,false,false,true,false,false,true,true,false,false,true] 30 local11 n (([true])) (([false,false,true]))

theorem phase12 (n : Nat) : run0 table 31 ⟨1,([true,true,false,true,true,false,false,true,true,false,true,true,false,false,true]),(rep [false,false,true,true,false,false,true,false,false,true,true,false,false,true] (n)) ++ ([false,false,true])⟩ = some ⟨4,[],([true,false,false,true,true,false,false,true,false,false,true,true,false,false,true]) ++ (rep [false,false,true,true,false,false,true,false,false,true,true,false,false,true] (n)) ++ ([false,false,true])⟩ := by rfl

theorem finalL (n : Nat) : ([] : List Bool) = [] := by
  rfl

theorem finalR (n : Nat) : ([true,false,false,true,true,false,false,true,false,false,true,true,false,false,true]) ++ (rep [false,false,true,true,false,false,true,false,false,true,true,false,false,true] (n)) ++ ([false,false,true]) = ([true,false,false,true,true,false,false,true,false,false,true,true,false,false]) ++ (rep [true,false,false,true,true,false,false,true,false,false,true,true,false,false] (n)) ++ ([true,false,false,true]) := by
  calc
    _ = ([true,false,false,true,true,false,false,true,false,false,true,true,false,false]) ++ (rep [true,false,false,true,true,false,false,true,false,false,true,true,false,false] (n)) ++ ([true,false,false,true]) := by simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using moveCut (([true,false,false,true,true,false,false,true,false,false,true,true,false,false])) (([false,false,true])) [false,false,true,true,false,false,true,false,false,true,true,false,false] true n

theorem growth (n : Nat) : run0 table (122+132*n) (family n) = some (family (n+1)) := by
  have H := (join0 (join0 (join0 (join0 (join0 (join0 (join0 (join0 (join0 (join0 (join0 (join0 (phase0 n) (phase1 n)) (phase2 n)) (phase3 n)) (phase4 n)) (phase5 n)) (phase6 n)) (phase7 n)) (phase8 n)) (phase9 n)) (phase10 n)) (phase11 n)) (phase12 n))
  rw [finalR n] at H
  rw [show 2+14*n+17+30*n+15+14*n+23+30*n+21+14*n+13+30*n+31=122+132*n by omega] at H
  simpa only [family,rep,List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using H

theorem never (m : Machine) (hm : compatible table m) : NeverHalts m :=
  never_of_growth table family 11 (fun n => 122+132*n) entry (by intro n; omega) growth m hm

#print axioms never

end M1583

namespace M1584

-- 1RB1RB_1RC1LE_0RD0RC_1LD0RA_0LB0LF_0LB---

def table : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 0,true => some (some ⟨true,true,1⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 1,true => some (some ⟨true,false,4⟩)
  | 2,false => some (some ⟨false,true,3⟩)
  | 2,true => some (some ⟨false,true,2⟩)
  | 3,false => some (some ⟨true,false,3⟩)
  | 3,true => some (some ⟨false,true,0⟩)
  | 4,false => some (some ⟨false,false,1⟩)
  | 4,true => some (some ⟨false,false,5⟩)
  | 5,false => some (some ⟨false,false,1⟩)
  | _,_ => none

def family (n : Nat) : Z0 := ⟨3,(rep [false] (n)) ++ ([false,false,false,true,true,false,false]) ++ (rep [true] (n)) ++ ([true]),[]⟩

theorem entry : run0 table 19 ⟨0,[],[]⟩ = some (family 0) := by rfl

theorem local0 (L R : List Bool) : run0 table 1 ⟨3,([false]) ++ (L),(R)⟩ = some ⟨3,(L),([true]) ++ (R)⟩ := by rfl

theorem phase0 (n : Nat) : run0 table (1*n) ⟨3,(rep [false] (n)) ++ ([false,false,false,true,true,false,false]) ++ (rep [true] (n)) ++ ([true]),[]⟩ = some ⟨3,([false,false,false,true,true,false,false]) ++ (rep [true] (n)) ++ ([true]),(rep [true] (n))⟩ := by
  simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using sweepL table 3 [] [] [false] [true] 1 local0 n (([false,false,false,true,true,false,false]) ++ (rep [true] (n)) ++ ([true])) ([])

theorem phase1 (n : Nat) : run0 table 15 ⟨3,([false,false,false,true,true,false,false]) ++ (rep [true] (n)) ++ ([true]),(rep [true] (n))⟩ = some ⟨2,([true,true,true,false,false,true]) ++ (rep [true] (n)) ++ ([true]),([true]) ++ (rep [true] (n))⟩ := by rfl

theorem local2 (L R : List Bool) : run0 table 1 ⟨2,([true]) ++ (L),([true]) ++ ([true]) ++ (R)⟩ = some ⟨2,([true]) ++ ([false]) ++ (L),([true]) ++ (R)⟩ := by rfl

theorem phase2 (n : Nat) : run0 table (1*n) ⟨2,([true,true,true,false,false,true]) ++ (rep [true] (n)) ++ ([true]),([true]) ++ (rep [true] (n))⟩ = some ⟨2,([true]) ++ (rep [false] (n)) ++ ([true,true,false,false,true]) ++ (rep [true] (n)) ++ ([true]),([true])⟩ := by
  simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using sweepR table 2 [true] [true] [true] [false] 1 local2 n (([true,true,false,false,true]) ++ (rep [true] (n)) ++ ([true])) ([])

theorem phase3 (n : Nat) : run0 table 3 ⟨2,([true]) ++ (rep [false] (n)) ++ ([true,true,false,false,true]) ++ (rep [true] (n)) ++ ([true]),([true])⟩ = some ⟨3,([false,false,false,false]) ++ (rep [false] (n)) ++ ([true,true,false,false,true]) ++ (rep [true] (n)) ++ ([true]),[]⟩ := by rfl

theorem finalL (n : Nat) : ([false,false,false,false]) ++ (rep [false] (n)) ++ ([true,true,false,false,true]) ++ (rep [true] (n)) ++ ([true]) = ([false]) ++ (rep [false] (n)) ++ ([false,false,false,true,true,false,false,true]) ++ (rep [true] (n)) ++ ([true]) := by
  calc
    _ = ([false,false,false]) ++ (rep [false] (n)) ++ ([false,true,true,false,false,true]) ++ (rep [true] (n)) ++ ([true]) := by simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using moveCut (([false,false,false])) (([true,true,false,false,true]) ++ (rep [true] (n)) ++ ([true])) [] false n
    _ = ([false,false]) ++ (rep [false] (n)) ++ ([false,false,true,true,false,false,true]) ++ (rep [true] (n)) ++ ([true]) := by simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using moveCut (([false,false])) (([false,true,true,false,false,true]) ++ (rep [true] (n)) ++ ([true])) [] false n
    _ = ([false]) ++ (rep [false] (n)) ++ ([false,false,false,true,true,false,false,true]) ++ (rep [true] (n)) ++ ([true]) := by simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using moveCut (([false])) (([false,false,true,true,false,false,true]) ++ (rep [true] (n)) ++ ([true])) [] false n

theorem finalR (n : Nat) : ([] : List Bool) = [] := by
  rfl

theorem growth (n : Nat) : run0 table (18+2*n) (family n) = some (family (n+1)) := by
  have H := (join0 (join0 (join0 (phase0 n) (phase1 n)) (phase2 n)) (phase3 n))
  rw [finalL n] at H
  rw [show 1*n+15+1*n+3=18+2*n by omega] at H
  simpa only [family,rep,List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using H

theorem never (m : Machine) (hm : compatible table m) : NeverHalts m :=
  never_of_growth table family 19 (fun n => 18+2*n) entry (by intro n; omega) growth m hm

#print axioms never

end M1584

namespace M1587

-- 1RB1RB_1RC1LE_0RD0RA_1LD0RA_1LF0LF_0LB---

def table : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 0,true => some (some ⟨true,true,1⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 1,true => some (some ⟨true,false,4⟩)
  | 2,false => some (some ⟨false,true,3⟩)
  | 2,true => some (some ⟨false,true,0⟩)
  | 3,false => some (some ⟨true,false,3⟩)
  | 3,true => some (some ⟨false,true,0⟩)
  | 4,false => some (some ⟨true,false,5⟩)
  | 4,true => some (some ⟨false,false,5⟩)
  | 5,false => some (some ⟨false,false,1⟩)
  | _,_ => none

def family (n : Nat) : Z0 := ⟨4,[],(rep [true,false,false,true,true,false,false,true,true,false,false,true,true,false,false,true,true,false,false,true] (n)) ++ ([true,false,false,true])⟩

theorem entry : run0 table 11 ⟨0,[],[]⟩ = some (family 0) := by rfl

theorem phase0 (n : Nat) : run0 table 3 ⟨4,[],(rep [true,false,false,true,true,false,false,true,true,false,false,true,true,false,false,true,true,false,false,true] (n)) ++ ([true,false,false,true])⟩ = some ⟨2,([false,true]),([true]) ++ (rep [true,false,false,true,true,false,false,true,true,false,false,true,true,false,false,true,true,false,false,true] (n)) ++ ([true,false,false,true])⟩ := by rfl

theorem local1 (L R : List Bool) : run0 table 20 ⟨2,([false]) ++ (L),([true]) ++ ([true,false,false,true,true,false,false,true,true,false,false,true,true,false,false,true,true,false,false,true]) ++ (R)⟩ = some ⟨2,([false]) ++ ([true,true,false,false,true,true,false,false,true,true,false,false,true,true,false,false,true,true,false,false]) ++ (L),([true]) ++ (R)⟩ := by rfl

theorem phase1 (n : Nat) : run0 table (20*n) ⟨2,([false,true]),([true]) ++ (rep [true,false,false,true,true,false,false,true,true,false,false,true,true,false,false,true,true,false,false,true] (n)) ++ ([true,false,false,true])⟩ = some ⟨2,([false]) ++ (rep [true,true,false,false,true,true,false,false,true,true,false,false,true,true,false,false,true,true,false,false] (n)) ++ ([true]),([true,true,false,false,true])⟩ := by
  simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using sweepR table 2 [false] [true] [true,false,false,true,true,false,false,true,true,false,false,true,true,false,false,true,true,false,false,true] [true,true,false,false,true,true,false,false,true,true,false,false,true,true,false,false,true,true,false,false] 20 local1 n (([true])) (([true,false,false,true]))

theorem phase2 (n : Nat) : run0 table 18 ⟨2,([false]) ++ (rep [true,true,false,false,true,true,false,false,true,true,false,false,true,true,false,false,true,true,false,false] (n)) ++ ([true]),([true,true,false,false,true])⟩ = some ⟨5,([false,true,true,false,false]) ++ (rep [true,true,false,false,true,true,false,false,true,true,false,false,true,true,false,false,true,true,false,false] (n)) ++ ([true]),([true,true,false,false,true])⟩ := by rfl

theorem local3 (L R : List Bool) : run0 table 60 ⟨5,([false,true,true,false,false]) ++ ([true,true,false,false,true,true,false,false,true,true,false,false,true,true,false,false,true,true,false,false]) ++ (L),(R)⟩ = some ⟨5,([false,true,true,false,false]) ++ (L),([false,true,true,false,false,true,true,false,false,true,true,false,false,true,true,false,false,true,true,false]) ++ (R)⟩ := by rfl

theorem phase3 (n : Nat) : run0 table (60*n) ⟨5,([false,true,true,false,false]) ++ (rep [true,true,false,false,true,true,false,false,true,true,false,false,true,true,false,false,true,true,false,false] (n)) ++ ([true]),([true,true,false,false,true])⟩ = some ⟨5,([false,true,true,false,false,true]),(rep [false,true,true,false,false,true,true,false,false,true,true,false,false,true,true,false,false,true,true,false] (n)) ++ ([true,true,false,false,true])⟩ := by
  simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using sweepL table 5 [false,true,true,false,false] [] [true,true,false,false,true,true,false,false,true,true,false,false,true,true,false,false,true,true,false,false] [false,true,true,false,false,true,true,false,false,true,true,false,false,true,true,false,false,true,true,false] 60 local3 n (([true])) (([true,true,false,false,true]))

theorem phase4 (n : Nat) : run0 table 17 ⟨5,([false,true,true,false,false,true]),(rep [false,true,true,false,false,true,true,false,false,true,true,false,false,true,true,false,false,true,true,false] (n)) ++ ([true,true,false,false,true])⟩ = some ⟨2,([false,true]),([true,true,false,false,true,true,false]) ++ (rep [false,true,true,false,false,true,true,false,false,true,true,false,false,true,true,false,false,true,true,false] (n)) ++ ([true,true,false,false,true])⟩ := by rfl

theorem local5 (L R : List Bool) : run0 table 20 ⟨2,([false]) ++ (L),([true,true,false,false,true,true,false]) ++ ([false,true,true,false,false,true,true,false,false,true,true,false,false,true,true,false,false,true,true,false]) ++ (R)⟩ = some ⟨2,([false]) ++ ([true,true,false,false,true,true,false,false,true,true,false,false,true,true,false,false,true,true,false,false]) ++ (L),([true,true,false,false,true,true,false]) ++ (R)⟩ := by rfl

theorem phase5 (n : Nat) : run0 table (20*n) ⟨2,([false,true]),([true,true,false,false,true,true,false]) ++ (rep [false,true,true,false,false,true,true,false,false,true,true,false,false,true,true,false,false,true,true,false] (n)) ++ ([true,true,false,false,true])⟩ = some ⟨2,([false]) ++ (rep [true,true,false,false,true,true,false,false,true,true,false,false,true,true,false,false,true,true,false,false] (n)) ++ ([true]),([true,true,false,false,true,true,false,true,true,false,false,true])⟩ := by
  simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using sweepR table 2 [false] [true,true,false,false,true,true,false] [false,true,true,false,false,true,true,false,false,true,true,false,false,true,true,false,false,true,true,false] [true,true,false,false,true,true,false,false,true,true,false,false,true,true,false,false,true,true,false,false] 20 local5 n (([true])) (([true,true,false,false,true]))

theorem phase6 (n : Nat) : run0 table 26 ⟨2,([false]) ++ (rep [true,true,false,false,true,true,false,false,true,true,false,false,true,true,false,false,true,true,false,false] (n)) ++ ([true]),([true,true,false,false,true,true,false,true,true,false,false,true])⟩ = some ⟨1,([true,true,false,true,true,false,false,true,true,false,false]) ++ (rep [true,true,false,false,true,true,false,false,true,true,false,false,true,true,false,false,true,true,false,false] (n)) ++ ([true]),([false,true,true,false,false,true])⟩ := by rfl

theorem local7 (L R : List Bool) : run0 table 60 ⟨1,([true,true,false,true,true,false,false,true,true,false,false]) ++ ([true,true,false,false,true,true,false,false,true,true,false,false,true,true,false,false,true,true,false,false]) ++ (L),(R)⟩ = some ⟨1,([true,true,false,true,true,false,false,true,true,false,false]) ++ (L),([true,false,false,true,true,false,false,true,true,false,false,true,true,false,false,true,true,false,false,true]) ++ (R)⟩ := by rfl

theorem phase7 (n : Nat) : run0 table (60*n) ⟨1,([true,true,false,true,true,false,false,true,true,false,false]) ++ (rep [true,true,false,false,true,true,false,false,true,true,false,false,true,true,false,false,true,true,false,false] (n)) ++ ([true]),([false,true,true,false,false,true])⟩ = some ⟨1,([true,true,false,true,true,false,false,true,true,false,false,true]),(rep [true,false,false,true,true,false,false,true,true,false,false,true,true,false,false,true,true,false,false,true] (n)) ++ ([false,true,true,false,false,true])⟩ := by
  simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using sweepL table 1 [true,true,false,true,true,false,false,true,true,false,false] [] [true,true,false,false,true,true,false,false,true,true,false,false,true,true,false,false,true,true,false,false] [true,false,false,true,true,false,false,true,true,false,false,true,true,false,false,true,true,false,false,true] 60 local7 n (([true])) (([false,true,true,false,false,true]))

theorem phase8 (n : Nat) : run0 table 31 ⟨1,([true,true,false,true,true,false,false,true,true,false,false,true]),(rep [true,false,false,true,true,false,false,true,true,false,false,true,true,false,false,true,true,false,false,true] (n)) ++ ([false,true,true,false,false,true])⟩ = some ⟨2,([false,true]),([true,true,false,false,true,true,false,false,true,true,false,false,true]) ++ (rep [true,false,false,true,true,false,false,true,true,false,false,true,true,false,false,true,true,false,false,true] (n)) ++ ([false,true,true,false,false,true])⟩ := by rfl

theorem local9 (L R : List Bool) : run0 table 20 ⟨2,([false]) ++ (L),([true,true,false,false,true,true,false,false,true,true,false,false,true]) ++ ([true,false,false,true,true,false,false,true,true,false,false,true,true,false,false,true,true,false,false,true]) ++ (R)⟩ = some ⟨2,([false]) ++ ([true,true,false,false,true,true,false,false,true,true,false,false,true,true,false,false,true,true,false,false]) ++ (L),([true,true,false,false,true,true,false,false,true,true,false,false,true]) ++ (R)⟩ := by rfl

theorem phase9 (n : Nat) : run0 table (20*n) ⟨2,([false,true]),([true,true,false,false,true,true,false,false,true,true,false,false,true]) ++ (rep [true,false,false,true,true,false,false,true,true,false,false,true,true,false,false,true,true,false,false,true] (n)) ++ ([false,true,true,false,false,true])⟩ = some ⟨2,([false]) ++ (rep [true,true,false,false,true,true,false,false,true,true,false,false,true,true,false,false,true,true,false,false] (n)) ++ ([true]),([true,true,false,false,true,true,false,false,true,true,false,false,true,false,true,true,false,false,true])⟩ := by
  simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using sweepR table 2 [false] [true,true,false,false,true,true,false,false,true,true,false,false,true] [true,false,false,true,true,false,false,true,true,false,false,true,true,false,false,true,true,false,false,true] [true,true,false,false,true,true,false,false,true,true,false,false,true,true,false,false,true,true,false,false] 20 local9 n (([true])) (([false,true,true,false,false,true]))

theorem phase10 (n : Nat) : run0 table 15 ⟨2,([false]) ++ (rep [true,true,false,false,true,true,false,false,true,true,false,false,true,true,false,false,true,true,false,false] (n)) ++ ([true]),([true,true,false,false,true,true,false,false,true,true,false,false,true,false,true,true,false,false,true])⟩ = some ⟨1,([true,true,false,false,true,true,false,false,true,true,false,false,true,true,false,false]) ++ (rep [true,true,false,false,true,true,false,false,true,true,false,false,true,true,false,false,true,true,false,false] (n)) ++ ([true]),([true,false,false,true])⟩ := by rfl

theorem local11 (L R : List Bool) : run0 table 60 ⟨1,([true,true,false,false,true,true,false,false,true,true,false,false,true,true,false,false]) ++ ([true,true,false,false,true,true,false,false,true,true,false,false,true,true,false,false,true,true,false,false]) ++ (L),(R)⟩ = some ⟨1,([true,true,false,false,true,true,false,false,true,true,false,false,true,true,false,false]) ++ (L),([false,false,true,true,false,false,true,true,false,false,true,true,false,false,true,true,false,false,true,true]) ++ (R)⟩ := by rfl

theorem phase11 (n : Nat) : run0 table (60*n) ⟨1,([true,true,false,false,true,true,false,false,true,true,false,false,true,true,false,false]) ++ (rep [true,true,false,false,true,true,false,false,true,true,false,false,true,true,false,false,true,true,false,false] (n)) ++ ([true]),([true,false,false,true])⟩ = some ⟨1,([true,true,false,false,true,true,false,false,true,true,false,false,true,true,false,false,true]),(rep [false,false,true,true,false,false,true,true,false,false,true,true,false,false,true,true,false,false,true,true] (n)) ++ ([true,false,false,true])⟩ := by
  simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using sweepL table 1 [true,true,false,false,true,true,false,false,true,true,false,false,true,true,false,false] [] [true,true,false,false,true,true,false,false,true,true,false,false,true,true,false,false,true,true,false,false] [false,false,true,true,false,false,true,true,false,false,true,true,false,false,true,true,false,false,true,true] 60 local11 n (([true])) (([true,false,false,true]))

theorem phase12 (n : Nat) : run0 table 52 ⟨1,([true,true,false,false,true,true,false,false,true,true,false,false,true,true,false,false,true]),(rep [false,false,true,true,false,false,true,true,false,false,true,true,false,false,true,true,false,false,true,true] (n)) ++ ([true,false,false,true])⟩ = some ⟨2,([false,true]),([true,true,false,false,true,true,false,false,true,true,false,false,true,true,false,false,true,true]) ++ (rep [false,false,true,true,false,false,true,true,false,false,true,true,false,false,true,true,false,false,true,true] (n)) ++ ([true,false,false,true])⟩ := by rfl

theorem local13 (L R : List Bool) : run0 table 20 ⟨2,([false]) ++ (L),([true,true,false,false,true,true,false,false,true,true,false,false,true,true,false,false,true,true]) ++ ([false,false,true,true,false,false,true,true,false,false,true,true,false,false,true,true,false,false,true,true]) ++ (R)⟩ = some ⟨2,([false]) ++ ([true,true,false,false,true,true,false,false,true,true,false,false,true,true,false,false,true,true,false,false]) ++ (L),([true,true,false,false,true,true,false,false,true,true,false,false,true,true,false,false,true,true]) ++ (R)⟩ := by rfl

theorem phase13 (n : Nat) : run0 table (20*n) ⟨2,([false,true]),([true,true,false,false,true,true,false,false,true,true,false,false,true,true,false,false,true,true]) ++ (rep [false,false,true,true,false,false,true,true,false,false,true,true,false,false,true,true,false,false,true,true] (n)) ++ ([true,false,false,true])⟩ = some ⟨2,([false]) ++ (rep [true,true,false,false,true,true,false,false,true,true,false,false,true,true,false,false,true,true,false,false] (n)) ++ ([true]),([true,true,false,false,true,true,false,false,true,true,false,false,true,true,false,false,true,true,true,false,false,true])⟩ := by
  simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using sweepR table 2 [false] [true,true,false,false,true,true,false,false,true,true,false,false,true,true,false,false,true,true] [false,false,true,true,false,false,true,true,false,false,true,true,false,false,true,true,false,false,true,true] [true,true,false,false,true,true,false,false,true,true,false,false,true,true,false,false,true,true,false,false] 20 local13 n (([true])) (([true,false,false,true]))

theorem phase14 (n : Nat) : run0 table 19 ⟨2,([false]) ++ (rep [true,true,false,false,true,true,false,false,true,true,false,false,true,true,false,false,true,true,false,false] (n)) ++ ([true]),([true,true,false,false,true,true,false,false,true,true,false,false,true,true,false,false,true,true,true,false,false,true])⟩ = some ⟨1,([true,true,false,false,true,true,false,false,true,true,false,false,true,true,false,false,true,true,false,false]) ++ (rep [true,true,false,false,true,true,false,false,true,true,false,false,true,true,false,false,true,true,false,false] (n)) ++ ([true]),([false,false,true])⟩ := by rfl

theorem local15 (L R : List Bool) : run0 table 60 ⟨1,([true,true,false,false,true,true,false,false,true,true,false,false,true,true,false,false,true,true,false,false]) ++ ([true,true,false,false,true,true,false,false,true,true,false,false,true,true,false,false,true,true,false,false]) ++ (L),(R)⟩ = some ⟨1,([true,true,false,false,true,true,false,false,true,true,false,false,true,true,false,false,true,true,false,false]) ++ (L),([false,false,true,true,false,false,true,true,false,false,true,true,false,false,true,true,false,false,true,true]) ++ (R)⟩ := by rfl

theorem phase15 (n : Nat) : run0 table (60*n) ⟨1,([true,true,false,false,true,true,false,false,true,true,false,false,true,true,false,false,true,true,false,false]) ++ (rep [true,true,false,false,true,true,false,false,true,true,false,false,true,true,false,false,true,true,false,false] (n)) ++ ([true]),([false,false,true])⟩ = some ⟨1,([true,true,false,false,true,true,false,false,true,true,false,false,true,true,false,false,true,true,false,false,true]),(rep [false,false,true,true,false,false,true,true,false,false,true,true,false,false,true,true,false,false,true,true] (n)) ++ ([false,false,true])⟩ := by
  simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using sweepL table 1 [true,true,false,false,true,true,false,false,true,true,false,false,true,true,false,false,true,true,false,false] [] [true,true,false,false,true,true,false,false,true,true,false,false,true,true,false,false,true,true,false,false] [false,false,true,true,false,false,true,true,false,false,true,true,false,false,true,true,false,false,true,true] 60 local15 n (([true])) (([false,false,true]))

theorem phase16 (n : Nat) : run0 table 61 ⟨1,([true,true,false,false,true,true,false,false,true,true,false,false,true,true,false,false,true,true,false,false,true]),(rep [false,false,true,true,false,false,true,true,false,false,true,true,false,false,true,true,false,false,true,true] (n)) ++ ([false,false,true])⟩ = some ⟨4,[],([true,false,false,true,true,false,false,true,true,false,false,true,true,false,false,true,true,false,false,true,true]) ++ (rep [false,false,true,true,false,false,true,true,false,false,true,true,false,false,true,true,false,false,true,true] (n)) ++ ([false,false,true])⟩ := by rfl

theorem finalL (n : Nat) : ([] : List Bool) = [] := by
  rfl

theorem finalR (n : Nat) : ([true,false,false,true,true,false,false,true,true,false,false,true,true,false,false,true,true,false,false,true,true]) ++ (rep [false,false,true,true,false,false,true,true,false,false,true,true,false,false,true,true,false,false,true,true] (n)) ++ ([false,false,true]) = ([true,false,false,true,true,false,false,true,true,false,false,true,true,false,false,true,true,false,false,true]) ++ (rep [true,false,false,true,true,false,false,true,true,false,false,true,true,false,false,true,true,false,false,true] (n)) ++ ([true,false,false,true]) := by
  calc
    _ = ([true,false,false,true,true,false,false,true,true,false,false,true,true,false,false,true,true,false,false,true]) ++ (rep [true,false,false,true,true,false,false,true,true,false,false,true,true,false,false,true,true,false,false,true] (n)) ++ ([true,false,false,true]) := by simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using moveCut (([true,false,false,true,true,false,false,true,true,false,false,true,true,false,false,true,true,false,false,true])) (([false,false,true])) [false,false,true,true,false,false,true,true,false,false,true,true,false,false,true,true,false,false,true] true n

theorem growth (n : Nat) : run0 table (242+320*n) (family n) = some (family (n+1)) := by
  have H := (join0 (join0 (join0 (join0 (join0 (join0 (join0 (join0 (join0 (join0 (join0 (join0 (join0 (join0 (join0 (join0 (phase0 n) (phase1 n)) (phase2 n)) (phase3 n)) (phase4 n)) (phase5 n)) (phase6 n)) (phase7 n)) (phase8 n)) (phase9 n)) (phase10 n)) (phase11 n)) (phase12 n)) (phase13 n)) (phase14 n)) (phase15 n)) (phase16 n))
  rw [finalR n] at H
  rw [show 3+20*n+18+60*n+17+20*n+26+60*n+31+20*n+15+60*n+52+20*n+19+60*n+61=242+320*n by omega] at H
  simpa only [family,rep,List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using H

theorem never (m : Machine) (hm : compatible table m) : NeverHalts m :=
  never_of_growth table family 11 (fun n => 242+320*n) entry (by intro n; omega) growth m hm

#print axioms never

end M1587

namespace M1592

-- 1RB1RB_1RC1LE_0RD0RC_1LD0RA_1RD0LF_0LB---

def table : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 0,true => some (some ⟨true,true,1⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 1,true => some (some ⟨true,false,4⟩)
  | 2,false => some (some ⟨false,true,3⟩)
  | 2,true => some (some ⟨false,true,2⟩)
  | 3,false => some (some ⟨true,false,3⟩)
  | 3,true => some (some ⟨false,true,0⟩)
  | 4,false => some (some ⟨true,true,3⟩)
  | 4,true => some (some ⟨false,false,5⟩)
  | 5,false => some (some ⟨false,false,1⟩)
  | _,_ => none

def family (n : Nat) : Z0 := ⟨3,(rep [false] (n)) ++ ([false,false,false,true,true,false]) ++ (rep [true] (n)) ++ ([true]),[]⟩

theorem entry : run0 table 17 ⟨0,[],[]⟩ = some (family 0) := by rfl

theorem local0 (L R : List Bool) : run0 table 1 ⟨3,([false]) ++ (L),(R)⟩ = some ⟨3,(L),([true]) ++ (R)⟩ := by rfl

theorem phase0 (n : Nat) : run0 table (1*n) ⟨3,(rep [false] (n)) ++ ([false,false,false,true,true,false]) ++ (rep [true] (n)) ++ ([true]),[]⟩ = some ⟨3,([false,false,false,true,true,false]) ++ (rep [true] (n)) ++ ([true]),(rep [true] (n))⟩ := by
  simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using sweepL table 3 [] [] [false] [true] 1 local0 n (([false,false,false,true,true,false]) ++ (rep [true] (n)) ++ ([true])) ([])

theorem phase1 (n : Nat) : run0 table 13 ⟨3,([false,false,false,true,true,false]) ++ (rep [true] (n)) ++ ([true]),(rep [true] (n))⟩ = some ⟨2,([true,true,true,false,true]) ++ (rep [true] (n)) ++ ([true]),([true]) ++ (rep [true] (n))⟩ := by rfl

theorem local2 (L R : List Bool) : run0 table 1 ⟨2,([true]) ++ (L),([true]) ++ ([true]) ++ (R)⟩ = some ⟨2,([true]) ++ ([false]) ++ (L),([true]) ++ (R)⟩ := by rfl

theorem phase2 (n : Nat) : run0 table (1*n) ⟨2,([true,true,true,false,true]) ++ (rep [true] (n)) ++ ([true]),([true]) ++ (rep [true] (n))⟩ = some ⟨2,([true]) ++ (rep [false] (n)) ++ ([true,true,false,true]) ++ (rep [true] (n)) ++ ([true]),([true])⟩ := by
  simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using sweepR table 2 [true] [true] [true] [false] 1 local2 n (([true,true,false,true]) ++ (rep [true] (n)) ++ ([true])) ([])

theorem phase3 (n : Nat) : run0 table 3 ⟨2,([true]) ++ (rep [false] (n)) ++ ([true,true,false,true]) ++ (rep [true] (n)) ++ ([true]),([true])⟩ = some ⟨3,([false,false,false,false]) ++ (rep [false] (n)) ++ ([true,true,false,true]) ++ (rep [true] (n)) ++ ([true]),[]⟩ := by rfl

theorem finalL (n : Nat) : ([false,false,false,false]) ++ (rep [false] (n)) ++ ([true,true,false,true]) ++ (rep [true] (n)) ++ ([true]) = ([false]) ++ (rep [false] (n)) ++ ([false,false,false,true,true,false,true]) ++ (rep [true] (n)) ++ ([true]) := by
  calc
    _ = ([false,false,false]) ++ (rep [false] (n)) ++ ([false,true,true,false,true]) ++ (rep [true] (n)) ++ ([true]) := by simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using moveCut (([false,false,false])) (([true,true,false,true]) ++ (rep [true] (n)) ++ ([true])) [] false n
    _ = ([false,false]) ++ (rep [false] (n)) ++ ([false,false,true,true,false,true]) ++ (rep [true] (n)) ++ ([true]) := by simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using moveCut (([false,false])) (([false,true,true,false,true]) ++ (rep [true] (n)) ++ ([true])) [] false n
    _ = ([false]) ++ (rep [false] (n)) ++ ([false,false,false,true,true,false,true]) ++ (rep [true] (n)) ++ ([true]) := by simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using moveCut (([false])) (([false,false,true,true,false,true]) ++ (rep [true] (n)) ++ ([true])) [] false n

theorem finalR (n : Nat) : ([] : List Bool) = [] := by
  rfl

theorem growth (n : Nat) : run0 table (16+2*n) (family n) = some (family (n+1)) := by
  have H := (join0 (join0 (join0 (phase0 n) (phase1 n)) (phase2 n)) (phase3 n))
  rw [finalL n] at H
  rw [show 1*n+13+1*n+3=16+2*n by omega] at H
  simpa only [family,rep,List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using H

theorem never (m : Machine) (hm : compatible table m) : NeverHalts m :=
  never_of_growth table family 17 (fun n => 16+2*n) entry (by intro n; omega) growth m hm

#print axioms never

end M1592

namespace M1633

-- 1RB1RB_1RC1LE_0RD0RC_1LD0RA_---0LF_1LF0LB

def table : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 0,true => some (some ⟨true,true,1⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 1,true => some (some ⟨true,false,4⟩)
  | 2,false => some (some ⟨false,true,3⟩)
  | 2,true => some (some ⟨false,true,2⟩)
  | 3,false => some (some ⟨true,false,3⟩)
  | 3,true => some (some ⟨false,true,0⟩)
  | 4,true => some (some ⟨false,false,5⟩)
  | 5,false => some (some ⟨true,false,5⟩)
  | 5,true => some (some ⟨false,false,1⟩)
  | _,_ => none

def family (n : Nat) : Z0 := ⟨3,(rep [false] (n)) ++ ([false,false,false,true,true,false,false]) ++ (rep [true] (n)) ++ ([true]),[]⟩

theorem entry : run0 table 27 ⟨0,[],[]⟩ = some (family 0) := by rfl

theorem local0 (L R : List Bool) : run0 table 1 ⟨3,([false]) ++ (L),(R)⟩ = some ⟨3,(L),([true]) ++ (R)⟩ := by rfl

theorem phase0 (n : Nat) : run0 table (1*n) ⟨3,(rep [false] (n)) ++ ([false,false,false,true,true,false,false]) ++ (rep [true] (n)) ++ ([true]),[]⟩ = some ⟨3,([false,false,false,true,true,false,false]) ++ (rep [true] (n)) ++ ([true]),(rep [true] (n))⟩ := by
  simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using sweepL table 3 [] [] [false] [true] 1 local0 n (([false,false,false,true,true,false,false]) ++ (rep [true] (n)) ++ ([true])) ([])

theorem phase1 (n : Nat) : run0 table 23 ⟨3,([false,false,false,true,true,false,false]) ++ (rep [true] (n)) ++ ([true]),(rep [true] (n))⟩ = some ⟨2,([true,true,true,false,false,true]) ++ (rep [true] (n)) ++ ([true]),([true]) ++ (rep [true] (n))⟩ := by rfl

theorem local2 (L R : List Bool) : run0 table 1 ⟨2,([true]) ++ (L),([true]) ++ ([true]) ++ (R)⟩ = some ⟨2,([true]) ++ ([false]) ++ (L),([true]) ++ (R)⟩ := by rfl

theorem phase2 (n : Nat) : run0 table (1*n) ⟨2,([true,true,true,false,false,true]) ++ (rep [true] (n)) ++ ([true]),([true]) ++ (rep [true] (n))⟩ = some ⟨2,([true]) ++ (rep [false] (n)) ++ ([true,true,false,false,true]) ++ (rep [true] (n)) ++ ([true]),([true])⟩ := by
  simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using sweepR table 2 [true] [true] [true] [false] 1 local2 n (([true,true,false,false,true]) ++ (rep [true] (n)) ++ ([true])) ([])

theorem phase3 (n : Nat) : run0 table 3 ⟨2,([true]) ++ (rep [false] (n)) ++ ([true,true,false,false,true]) ++ (rep [true] (n)) ++ ([true]),([true])⟩ = some ⟨3,([false,false,false,false]) ++ (rep [false] (n)) ++ ([true,true,false,false,true]) ++ (rep [true] (n)) ++ ([true]),[]⟩ := by rfl

theorem finalL (n : Nat) : ([false,false,false,false]) ++ (rep [false] (n)) ++ ([true,true,false,false,true]) ++ (rep [true] (n)) ++ ([true]) = ([false]) ++ (rep [false] (n)) ++ ([false,false,false,true,true,false,false,true]) ++ (rep [true] (n)) ++ ([true]) := by
  calc
    _ = ([false,false,false]) ++ (rep [false] (n)) ++ ([false,true,true,false,false,true]) ++ (rep [true] (n)) ++ ([true]) := by simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using moveCut (([false,false,false])) (([true,true,false,false,true]) ++ (rep [true] (n)) ++ ([true])) [] false n
    _ = ([false,false]) ++ (rep [false] (n)) ++ ([false,false,true,true,false,false,true]) ++ (rep [true] (n)) ++ ([true]) := by simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using moveCut (([false,false])) (([false,true,true,false,false,true]) ++ (rep [true] (n)) ++ ([true])) [] false n
    _ = ([false]) ++ (rep [false] (n)) ++ ([false,false,false,true,true,false,false,true]) ++ (rep [true] (n)) ++ ([true]) := by simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using moveCut (([false])) (([false,false,true,true,false,false,true]) ++ (rep [true] (n)) ++ ([true])) [] false n

theorem finalR (n : Nat) : ([] : List Bool) = [] := by
  rfl

theorem growth (n : Nat) : run0 table (26+2*n) (family n) = some (family (n+1)) := by
  have H := (join0 (join0 (join0 (phase0 n) (phase1 n)) (phase2 n)) (phase3 n))
  rw [finalL n] at H
  rw [show 1*n+23+1*n+3=26+2*n by omega] at H
  simpa only [family,rep,List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using H

theorem never (m : Machine) (hm : compatible table m) : NeverHalts m :=
  never_of_growth table family 27 (fun n => 26+2*n) entry (by intro n; omega) growth m hm

#print axioms never

end M1633

namespace M1667

-- 1RB1RB_1RC1LE_0RD1LC_1LD0RA_1LF0RB_0LB---

def table : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 0,true => some (some ⟨true,true,1⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 1,true => some (some ⟨true,false,4⟩)
  | 2,false => some (some ⟨false,true,3⟩)
  | 2,true => some (some ⟨true,false,2⟩)
  | 3,false => some (some ⟨true,false,3⟩)
  | 3,true => some (some ⟨false,true,0⟩)
  | 4,false => some (some ⟨true,false,5⟩)
  | 4,true => some (some ⟨false,true,1⟩)
  | 5,false => some (some ⟨false,false,1⟩)
  | _,_ => none

def family (n : Nat) : Z0 := ⟨1,([false,true,false]) ++ (rep [false,true,true,false,true,true] (n)) ++ ([false,true,true,false,true]),[]⟩

theorem entry : run0 table 44 ⟨0,[],[]⟩ = some (family 0) := by rfl

theorem phase0 (n : Nat) : run0 table 11 ⟨1,([false,true,false]) ++ (rep [false,true,true,false,true,true] (n)) ++ ([false,true,true,false,true]),[]⟩ = some ⟨1,([true,false]) ++ (rep [false,true,true,false,true,true] (n)) ++ ([false,true,true,false,true]),([false,true,true])⟩ := by rfl

theorem local1 (L R : List Bool) : run0 table 10 ⟨1,([true,false]) ++ ([false,true,true,false,true,true]) ++ (L),(R)⟩ = some ⟨1,([true,false]) ++ (L),([false,true,true,false,true,true]) ++ (R)⟩ := by rfl

theorem phase1 (n : Nat) : run0 table (10*n) ⟨1,([true,false]) ++ (rep [false,true,true,false,true,true] (n)) ++ ([false,true,true,false,true]),([false,true,true])⟩ = some ⟨1,([true,false,false,true,true,false,true]),(rep [false,true,true,false,true,true] (n)) ++ ([false,true,true])⟩ := by
  simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using sweepL table 1 [true,false] [] [false,true,true,false,true,true] [false,true,true,false,true,true] 10 local1 n (([false,true,true,false,true])) (([false,true,true]))

theorem phase2 (n : Nat) : run0 table 12 ⟨1,([true,false,false,true,true,false,true]),(rep [false,true,true,false,true,true] (n)) ++ ([false,true,true])⟩ = some ⟨2,([false,true]),([true,true,false,true,true,false,true,true]) ++ (rep [false,true,true,false,true,true] (n)) ++ ([false,true,true])⟩ := by rfl

theorem local3 (L R : List Bool) : run0 table 50 ⟨2,([false]) ++ (L),([true,true,false,true,true,false,true,true]) ++ ([false,true,true,false,true,true]) ++ (R)⟩ = some ⟨2,([false]) ++ ([true,true,false,true,true,false]) ++ (L),([true,true,false,true,true,false,true,true]) ++ (R)⟩ := by rfl

theorem phase3 (n : Nat) : run0 table (50*n) ⟨2,([false,true]),([true,true,false,true,true,false,true,true]) ++ (rep [false,true,true,false,true,true] (n)) ++ ([false,true,true])⟩ = some ⟨2,([false]) ++ (rep [true,true,false,true,true,false] (n)) ++ ([true]),([true,true,false,true,true,false,true,true,false,true,true])⟩ := by
  simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using sweepR table 2 [false] [true,true,false,true,true,false,true,true] [false,true,true,false,true,true] [true,true,false,true,true,false] 50 local3 n (([true])) (([false,true,true]))

theorem phase4 (n : Nat) : run0 table 78 ⟨2,([false]) ++ (rep [true,true,false,true,true,false] (n)) ++ ([true]),([true,true,false,true,true,false,true,true,false,true,true])⟩ = some ⟨1,([false,true,false,false,true,true,false,true,true,false,true,true,false]) ++ (rep [true,true,false,true,true,false] (n)) ++ ([true]),[]⟩ := by rfl

theorem finalL (n : Nat) : ([false,true,false,false,true,true,false,true,true,false,true,true,false]) ++ (rep [true,true,false,true,true,false] (n)) ++ ([true]) = ([false,true,false,false,true,true,false,true,true]) ++ (rep [false,true,true,false,true,true] (n)) ++ ([false,true,true,false,true]) := by
  calc
    _ = ([false,true,false,false,true,true,false,true,true,false,true,true]) ++ (rep [false,true,true,false,true,true] (n)) ++ ([false,true]) := by simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using moveCut (([false,true,false,false,true,true,false,true,true,false,true,true])) (([true])) [true,true,false,true,true] false n
    _ = ([false,true,false,false,true,true,false,true,true,false,true]) ++ (rep [true,false,true,true,false,true] (n)) ++ ([true,false,true]) := by simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using moveCut (([false,true,false,false,true,true,false,true,true,false,true])) (([false,true])) [false,true,true,false,true] true n
    _ = ([false,true,false,false,true,true,false,true,true,false]) ++ (rep [true,true,false,true,true,false] (n)) ++ ([true,true,false,true]) := by simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using moveCut (([false,true,false,false,true,true,false,true,true,false])) (([true,false,true])) [true,false,true,true,false] true n
    _ = ([false,true,false,false,true,true,false,true,true]) ++ (rep [false,true,true,false,true,true] (n)) ++ ([false,true,true,false,true]) := by simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using moveCut (([false,true,false,false,true,true,false,true,true])) (([true,true,false,true])) [true,true,false,true,true] false n

theorem finalR (n : Nat) : ([] : List Bool) = [] := by
  rfl

theorem growth (n : Nat) : run0 table (101+60*n) (family n) = some (family (n+1)) := by
  have H := (join0 (join0 (join0 (join0 (phase0 n) (phase1 n)) (phase2 n)) (phase3 n)) (phase4 n))
  rw [finalL n] at H
  rw [show 11+10*n+12+50*n+78=101+60*n by omega] at H
  simpa only [family,rep,List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using H

theorem never (m : Machine) (hm : compatible table m) : NeverHalts m :=
  never_of_growth table family 44 (fun n => 101+60*n) entry (by intro n; omega) growth m hm

#print axioms never

end M1667

end BB6.Agent11Raw39Pumps
