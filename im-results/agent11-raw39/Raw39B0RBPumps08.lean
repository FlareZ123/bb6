import SweepPumping
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedVariables false
namespace BB6.Agent11Raw39B0RBPumps
open BB6Coverage BB6Coverage.Agent31Pump


namespace M1175

-- 1RB0RB_1RC1LE_0RD1RF_1LD0RA_0LD---_0RC0RB

def table : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 0,true => some (some ⟨false,true,1⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 1,true => some (some ⟨true,false,4⟩)
  | 2,false => some (some ⟨false,true,3⟩)
  | 2,true => some (some ⟨true,true,5⟩)
  | 3,false => some (some ⟨true,false,3⟩)
  | 3,true => some (some ⟨false,true,0⟩)
  | 4,false => some (some ⟨false,false,3⟩)
  | 5,false => some (some ⟨false,true,2⟩)
  | 5,true => some (some ⟨false,true,1⟩)
  | _,_ => none

def family (n : Nat) : Z0 := ⟨1,([false]) ++ (rep [false,true] (n)) ++ ([true]) ++ (rep [false,false,false,false] (n)),[]⟩

theorem entry : run0 table 1 ⟨0,[],[]⟩ = some (family 0) := by rfl

theorem phase0 (n : Nat) : run0 table 2 ⟨1,([false]) ++ (rep [false,true] (n)) ++ ([true]) ++ (rep [false,false,false,false] (n)),[]⟩ = some ⟨3,([false,false,true]) ++ (rep [false,true] (n)) ++ ([true]) ++ (rep [false,false,false,false] (n)),[]⟩ := by rfl

theorem local1 (L R : List Bool) : run0 table 6 ⟨3,([false,false,true]) ++ ([false,true]) ++ (L),(R)⟩ = some ⟨3,([false,false,true]) ++ (L),([false,true]) ++ (R)⟩ := by rfl

theorem phase1 (n : Nat) : run0 table (6*n) ⟨3,([false,false,true]) ++ (rep [false,true] (n)) ++ ([true]) ++ (rep [false,false,false,false] (n)),[]⟩ = some ⟨3,([false,false,true,true]) ++ (rep [false,false,false,false] (n)),(rep [false,true] (n))⟩ := by
  simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using sweepL table 3 [false,false,true] [] [false,true] [false,true] 6 local1 n (([true]) ++ (rep [false,false,false,false] (n))) ([])

theorem phase2 (n : Nat) : run0 table 10 ⟨3,([false,false,true,true]) ++ (rep [false,false,false,false] (n)),(rep [false,true] (n))⟩ = some ⟨2,([true,true,false,false]) ++ (rep [false,false,false,false] (n)),(rep [false,true] (n))⟩ := by rfl

theorem local3 (L R : List Bool) : run0 table 2 ⟨2,([true]) ++ (L),([false,true]) ++ (R)⟩ = some ⟨2,([true]) ++ ([false,true]) ++ (L),(R)⟩ := by rfl

theorem phase3 (n : Nat) : run0 table (2*n) ⟨2,([true,true,false,false]) ++ (rep [false,false,false,false] (n)),(rep [false,true] (n))⟩ = some ⟨2,([true]) ++ (rep [false,true] (n)) ++ ([true,false,false]) ++ (rep [false,false,false,false] (n)),[]⟩ := by
  simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using sweepR table 2 [true] [] [false,true] [false,true] 2 local3 n (([true,false,false]) ++ (rep [false,false,false,false] (n))) ([])

theorem phase4 (n : Nat) : run0 table 4 ⟨2,([true]) ++ (rep [false,true] (n)) ++ ([true,false,false]) ++ (rep [false,false,false,false] (n)),[]⟩ = some ⟨3,([false,false,true]) ++ (rep [false,true] (n)) ++ ([true,false,false]) ++ (rep [false,false,false,false] (n)),([true])⟩ := by rfl

theorem local5 (L R : List Bool) : run0 table 6 ⟨3,([false,false,true]) ++ ([false,true]) ++ (L),(R)⟩ = some ⟨3,([false,false,true]) ++ (L),([false,true]) ++ (R)⟩ := by rfl

theorem phase5 (n : Nat) : run0 table (6*n) ⟨3,([false,false,true]) ++ (rep [false,true] (n)) ++ ([true,false,false]) ++ (rep [false,false,false,false] (n)),([true])⟩ = some ⟨3,([false,false,true,true,false,false]) ++ (rep [false,false,false,false] (n)),(rep [false,true] (n)) ++ ([true])⟩ := by
  simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using sweepL table 3 [false,false,true] [] [false,true] [false,true] 6 local5 n (([true,false,false]) ++ (rep [false,false,false,false] (n))) (([true]))

theorem phase6 (n : Nat) : run0 table 10 ⟨3,([false,false,true,true,false,false]) ++ (rep [false,false,false,false] (n)),(rep [false,true] (n)) ++ ([true])⟩ = some ⟨2,([true,true,false,false,false,false]) ++ (rep [false,false,false,false] (n)),(rep [false,true] (n)) ++ ([true])⟩ := by rfl

theorem local7 (L R : List Bool) : run0 table 2 ⟨2,([true]) ++ (L),([false,true]) ++ (R)⟩ = some ⟨2,([true]) ++ ([false,true]) ++ (L),(R)⟩ := by rfl

theorem phase7 (n : Nat) : run0 table (2*n) ⟨2,([true,true,false,false,false,false]) ++ (rep [false,false,false,false] (n)),(rep [false,true] (n)) ++ ([true])⟩ = some ⟨2,([true]) ++ (rep [false,true] (n)) ++ ([true,false,false,false,false]) ++ (rep [false,false,false,false] (n)),([true])⟩ := by
  simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using sweepR table 2 [true] [] [false,true] [false,true] 2 local7 n (([true,false,false,false,false]) ++ (rep [false,false,false,false] (n))) (([true]))

theorem phase8 (n : Nat) : run0 table 2 ⟨2,([true]) ++ (rep [false,true] (n)) ++ ([true,false,false,false,false]) ++ (rep [false,false,false,false] (n)),([true])⟩ = some ⟨1,([false,false,true]) ++ (rep [false,true] (n)) ++ ([true,false,false,false,false]) ++ (rep [false,false,false,false] (n)),[]⟩ := by rfl

theorem finalL (n : Nat) : ([false,false,true]) ++ (rep [false,true] (n)) ++ ([true,false,false,false,false]) ++ (rep [false,false,false,false] (n)) = ([false,false,true]) ++ (rep [false,true] (n)) ++ ([true,false,false,false,false]) ++ (rep [false,false,false,false] (n)) := by
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

end M1175

namespace M1181

-- 1RB0RB_1RC1LE_0RD0RC_1LD0RA_0LE1LF_0LB---

def table : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 0,true => some (some ⟨false,true,1⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 1,true => some (some ⟨true,false,4⟩)
  | 2,false => some (some ⟨false,true,3⟩)
  | 2,true => some (some ⟨false,true,2⟩)
  | 3,false => some (some ⟨true,false,3⟩)
  | 3,true => some (some ⟨false,true,0⟩)
  | 4,false => some (some ⟨false,false,4⟩)
  | 4,true => some (some ⟨true,false,5⟩)
  | 5,false => some (some ⟨false,false,1⟩)
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

end M1181

namespace M1183

-- 1RB0RB_1RC1LE_0RD0RC_1LD0RA_0LE1LF_1RD---

def table : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 0,true => some (some ⟨false,true,1⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 1,true => some (some ⟨true,false,4⟩)
  | 2,false => some (some ⟨false,true,3⟩)
  | 2,true => some (some ⟨false,true,2⟩)
  | 3,false => some (some ⟨true,false,3⟩)
  | 3,true => some (some ⟨false,true,0⟩)
  | 4,false => some (some ⟨false,false,4⟩)
  | 4,true => some (some ⟨true,false,5⟩)
  | 5,false => some (some ⟨true,true,3⟩)
  | _,_ => none

def family (n : Nat) : Z0 := ⟨2,([false,false]) ++ (rep [false] (n)) ++ ([true,true,false,true]) ++ (rep [true] (n)),[]⟩

theorem entry : run0 table 16 ⟨0,[],[]⟩ = some (family 0) := by rfl

theorem phase0 (n : Nat) : run0 table 1 ⟨2,([false,false]) ++ (rep [false] (n)) ++ ([true,true,false,true]) ++ (rep [true] (n)),[]⟩ = some ⟨3,([false,false,false]) ++ (rep [false] (n)) ++ ([true,true,false,true]) ++ (rep [true] (n)),[]⟩ := by rfl

theorem local1 (L R : List Bool) : run0 table 1 ⟨3,([false,false,false]) ++ ([false]) ++ (L),(R)⟩ = some ⟨3,([false,false,false]) ++ (L),([true]) ++ (R)⟩ := by rfl

theorem phase1 (n : Nat) : run0 table (1*n) ⟨3,([false,false,false]) ++ (rep [false] (n)) ++ ([true,true,false,true]) ++ (rep [true] (n)),[]⟩ = some ⟨3,([false,false,false,true,true,false,true]) ++ (rep [true] (n)),(rep [true] (n))⟩ := by
  simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using sweepL table 3 [false,false,false] [] [false] [true] 1 local1 n (([true,true,false,true]) ++ (rep [true] (n))) ([])

theorem phase2 (n : Nat) : run0 table 13 ⟨3,([false,false,false,true,true,false,true]) ++ (rep [true] (n)),(rep [true] (n))⟩ = some ⟨2,([true,true,true,false,true,true]) ++ (rep [true] (n)),([true]) ++ (rep [true] (n))⟩ := by rfl

theorem local3 (L R : List Bool) : run0 table 1 ⟨2,([true]) ++ (L),([true]) ++ ([true]) ++ (R)⟩ = some ⟨2,([true]) ++ ([false]) ++ (L),([true]) ++ (R)⟩ := by rfl

theorem phase3 (n : Nat) : run0 table (1*n) ⟨2,([true,true,true,false,true,true]) ++ (rep [true] (n)),([true]) ++ (rep [true] (n))⟩ = some ⟨2,([true]) ++ (rep [false] (n)) ++ ([true,true,false,true,true]) ++ (rep [true] (n)),([true])⟩ := by
  simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using sweepR table 2 [true] [true] [true] [false] 1 local3 n (([true,true,false,true,true]) ++ (rep [true] (n))) ([])

theorem phase4 (n : Nat) : run0 table 2 ⟨2,([true]) ++ (rep [false] (n)) ++ ([true,true,false,true,true]) ++ (rep [true] (n)),([true])⟩ = some ⟨2,([false,false,false]) ++ (rep [false] (n)) ++ ([true,true,false,true,true]) ++ (rep [true] (n)),[]⟩ := by rfl

theorem finalL (n : Nat) : ([false,false,false]) ++ (rep [false] (n)) ++ ([true,true,false,true,true]) ++ (rep [true] (n)) = ([false,false,false]) ++ (rep [false] (n)) ++ ([true,true,false,true,true]) ++ (rep [true] (n)) := by
  rfl

theorem finalR (n : Nat) : ([] : List Bool) = [] := by
  rfl

theorem growth (n : Nat) : run0 table (16+2*n) (family n) = some (family (n+1)) := by
  have H := (join0 (join0 (join0 (join0 (phase0 n) (phase1 n)) (phase2 n)) (phase3 n)) (phase4 n))
  rw [show 1+1*n+13+1*n+2=16+2*n by omega] at H
  simpa only [family,rep,List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using H

theorem never (m : Machine) (hm : compatible table m) : NeverHalts m :=
  never_of_growth table family 16 (fun n => 16+2*n) entry (by intro n; omega) growth m hm

#print axioms never

end M1183

namespace M1194

-- 1RB0RB_1RC1LE_0RD1RE_1LD0RA_0LF---_0LD1RD

def table : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 0,true => some (some ⟨false,true,1⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 1,true => some (some ⟨true,false,4⟩)
  | 2,false => some (some ⟨false,true,3⟩)
  | 2,true => some (some ⟨true,true,4⟩)
  | 3,false => some (some ⟨true,false,3⟩)
  | 3,true => some (some ⟨false,true,0⟩)
  | 4,false => some (some ⟨false,false,5⟩)
  | 5,false => some (some ⟨false,false,3⟩)
  | 5,true => some (some ⟨true,true,3⟩)
  | _,_ => none

def family (n : Nat) : Z0 := ⟨1,([false]) ++ (rep [false,false,true] (n)) ++ ([true]) ++ (rep [false] (n)),[]⟩

theorem entry : run0 table 1 ⟨0,[],[]⟩ = some (family 0) := by rfl

theorem phase0 (n : Nat) : run0 table 2 ⟨1,([false]) ++ (rep [false,false,true] (n)) ++ ([true]) ++ (rep [false] (n)),[]⟩ = some ⟨3,([false,false,true]) ++ (rep [false,false,true] (n)) ++ ([true]) ++ (rep [false] (n)),[]⟩ := by rfl

theorem local1 (L R : List Bool) : run0 table 7 ⟨3,([false,false,true]) ++ ([false,false,true]) ++ (L),(R)⟩ = some ⟨3,([false,false,true]) ++ (L),([false,false,true]) ++ (R)⟩ := by rfl

theorem phase1 (n : Nat) : run0 table (7*n) ⟨3,([false,false,true]) ++ (rep [false,false,true] (n)) ++ ([true]) ++ (rep [false] (n)),[]⟩ = some ⟨3,([false,false,true,true]) ++ (rep [false] (n)),(rep [false,false,true] (n))⟩ := by
  simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using sweepL table 3 [false,false,true] [] [false,false,true] [false,false,true] 7 local1 n (([true]) ++ (rep [false] (n))) ([])

theorem phase2 (n : Nat) : run0 table 9 ⟨3,([false,false,true,true]) ++ (rep [false] (n)),(rep [false,false,true] (n))⟩ = some ⟨1,([false,true,false]) ++ (rep [false] (n)),([true]) ++ (rep [false,false,true] (n))⟩ := by rfl

theorem local3 (L R : List Bool) : run0 table 7 ⟨1,([false]) ++ (L),([true]) ++ ([false,false,true]) ++ (R)⟩ = some ⟨1,([false]) ++ ([false,false,true]) ++ (L),([true]) ++ (R)⟩ := by rfl

theorem phase3 (n : Nat) : run0 table (7*n) ⟨1,([false,true,false]) ++ (rep [false] (n)),([true]) ++ (rep [false,false,true] (n))⟩ = some ⟨1,([false]) ++ (rep [false,false,true] (n)) ++ ([true,false]) ++ (rep [false] (n)),([true])⟩ := by
  simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using sweepR table 1 [false] [true] [false,false,true] [false,false,true] 7 local3 n (([true,false]) ++ (rep [false] (n))) ([])

theorem phase4 (n : Nat) : run0 table 7 ⟨1,([false]) ++ (rep [false,false,true] (n)) ++ ([true,false]) ++ (rep [false] (n)),([true])⟩ = some ⟨1,([false,false,false,true]) ++ (rep [false,false,true] (n)) ++ ([true,false]) ++ (rep [false] (n)),[]⟩ := by rfl

theorem finalL (n : Nat) : ([false,false,false,true]) ++ (rep [false,false,true] (n)) ++ ([true,false]) ++ (rep [false] (n)) = ([false,false,false,true]) ++ (rep [false,false,true] (n)) ++ ([true,false]) ++ (rep [false] (n)) := by
  rfl

theorem finalR (n : Nat) : ([] : List Bool) = [] := by
  rfl

theorem growth (n : Nat) : run0 table (18+14*n) (family n) = some (family (n+1)) := by
  have H := (join0 (join0 (join0 (join0 (phase0 n) (phase1 n)) (phase2 n)) (phase3 n)) (phase4 n))
  rw [show 2+7*n+9+7*n+7=18+14*n by omega] at H
  simpa only [family,rep,List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using H

theorem never (m : Machine) (hm : compatible table m) : NeverHalts m :=
  never_of_growth table family 1 (fun n => 18+14*n) entry (by intro n; omega) growth m hm

#print axioms never

end M1194

namespace M1221

-- 1RB0RB_1RC1LE_0RD0LE_1LD0RA_0LF1LC_1LA---

def table : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 0,true => some (some ⟨false,true,1⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 1,true => some (some ⟨true,false,4⟩)
  | 2,false => some (some ⟨false,true,3⟩)
  | 2,true => some (some ⟨false,false,4⟩)
  | 3,false => some (some ⟨true,false,3⟩)
  | 3,true => some (some ⟨false,true,0⟩)
  | 4,false => some (some ⟨false,false,5⟩)
  | 4,true => some (some ⟨true,false,2⟩)
  | 5,false => some (some ⟨true,false,0⟩)
  | _,_ => none

def family (n : Nat) : Z0 := ⟨1,([false,true,false,false,true,false,false,false]) ++ (rep [true,false,false,false] (n)),[]⟩

theorem entry : run0 table 42 ⟨0,[],[]⟩ = some (family 0) := by rfl

theorem phase0 (n : Nat) : run0 table 11 ⟨1,([false,true,false,false,true,false,false,false]) ++ (rep [true,false,false,false] (n)),[]⟩ = some ⟨4,([false,false,false,true,false,false,false]) ++ (rep [true,false,false,false] (n)),([true,false,true])⟩ := by rfl

theorem local1 (L R : List Bool) : run0 table 6 ⟨4,([false,false,false,true,false,false,false]) ++ ([true,false,false,false]) ++ (L),(R)⟩ = some ⟨4,([false,false,false,true,false,false,false]) ++ (L),([false,true,true,false]) ++ (R)⟩ := by rfl

theorem phase1 (n : Nat) : run0 table (6*n) ⟨4,([false,false,false,true,false,false,false]) ++ (rep [true,false,false,false] (n)),([true,false,true])⟩ = some ⟨4,([false,false,false,true,false,false,false]),(rep [false,true,true,false] (n)) ++ ([true,false,true])⟩ := by
  simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using sweepL table 4 [false,false,false,true,false,false,false] [] [true,false,false,false] [false,true,true,false] 6 local1 n ([]) (([true,false,true]))

theorem phase2 (n : Nat) : run0 table 12 ⟨4,([false,false,false,true,false,false,false]),(rep [false,true,true,false] (n)) ++ ([true,false,true])⟩ = some ⟨3,([true,false]),([true,false,false,true,true,false]) ++ (rep [false,true,true,false] (n)) ++ ([true,false,true])⟩ := by rfl

theorem local3 (L R : List Bool) : run0 table 4 ⟨3,([true]) ++ (L),([true,false,false,true,true,false]) ++ ([false,true,true,false]) ++ (R)⟩ = some ⟨3,([true]) ++ ([false,true,false,false]) ++ (L),([true,false,false,true,true,false]) ++ (R)⟩ := by rfl

theorem phase3 (n : Nat) : run0 table (4*n) ⟨3,([true,false]),([true,false,false,true,true,false]) ++ (rep [false,true,true,false] (n)) ++ ([true,false,true])⟩ = some ⟨3,([true]) ++ (rep [false,true,false,false] (n)) ++ ([false]),([true,false,false,true,true,false,true,false,true])⟩ := by
  simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using sweepR table 3 [true] [true,false,false,true,true,false] [false,true,true,false] [false,true,false,false] 4 local3 n (([false])) (([true,false,true]))

theorem phase4 (n : Nat) : run0 table 28 ⟨3,([true]) ++ (rep [false,true,false,false] (n)) ++ ([false]),([true,false,false,true,true,false,true,false,true])⟩ = some ⟨1,([false,true,false,false,true,false,false,false,true,false,false]) ++ (rep [false,true,false,false] (n)) ++ ([false]),[]⟩ := by rfl

theorem finalL (n : Nat) : ([false,true,false,false,true,false,false,false,true,false,false]) ++ (rep [false,true,false,false] (n)) ++ ([false]) = ([false,true,false,false,true,false,false,false,true,false,false,false]) ++ (rep [true,false,false,false] (n)) := by
  calc
    _ = ([false,true,false,false,true,false,false,false,true,false,false,false]) ++ (rep [true,false,false,false] (n)) := by symm; simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using moveCut (([false,true,false,false,true,false,false,false,true,false,false])) ([]) [true,false,false] false n

theorem finalR (n : Nat) : ([] : List Bool) = [] := by
  rfl

theorem growth (n : Nat) : run0 table (51+10*n) (family n) = some (family (n+1)) := by
  have H := (join0 (join0 (join0 (join0 (phase0 n) (phase1 n)) (phase2 n)) (phase3 n)) (phase4 n))
  rw [finalL n] at H
  rw [show 11+6*n+12+4*n+28=51+10*n by omega] at H
  simpa only [family,rep,List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using H

theorem never (m : Machine) (hm : compatible table m) : NeverHalts m :=
  never_of_growth table family 42 (fun n => 51+10*n) entry (by intro n; omega) growth m hm

#print axioms never

end M1221

namespace M1230

-- 1RB0RB_1RC1LE_0RD1RB_1LD0RA_0LF0LD_1LB---

def table : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 0,true => some (some ⟨false,true,1⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 1,true => some (some ⟨true,false,4⟩)
  | 2,false => some (some ⟨false,true,3⟩)
  | 2,true => some (some ⟨true,true,1⟩)
  | 3,false => some (some ⟨true,false,3⟩)
  | 3,true => some (some ⟨false,true,0⟩)
  | 4,false => some (some ⟨false,false,5⟩)
  | 4,true => some (some ⟨false,false,3⟩)
  | 5,false => some (some ⟨true,false,1⟩)
  | _,_ => none

def family (n : Nat) : Z0 := ⟨1,[],([true,false,true,true,false,true,true,false,true]) ++ (rep [true,false,true,true,false,true] (n)) ++ ([false,true])⟩

theorem entry : run0 table 95 ⟨0,[],[]⟩ = some (family 0) := by rfl

theorem phase0 (n : Nat) : run0 table 1 ⟨1,[],([true,false,true,true,false,true,true,false,true]) ++ (rep [true,false,true,true,false,true] (n)) ++ ([false,true])⟩ = some ⟨2,([true,true]),([false,true,true,false,true,true,false,true]) ++ (rep [true,false,true,true,false,true] (n)) ++ ([false,true])⟩ := by rfl

theorem local1 (L R : List Bool) : run0 table 26 ⟨2,([true]) ++ (L),([false,true,true,false,true,true,false,true]) ++ ([true,false,true,true,false,true]) ++ (R)⟩ = some ⟨2,([true]) ++ ([true,false,false,true,false,false]) ++ (L),([false,true,true,false,true,true,false,true]) ++ (R)⟩ := by rfl

theorem phase1 (n : Nat) : run0 table (26*n) ⟨2,([true,true]),([false,true,true,false,true,true,false,true]) ++ (rep [true,false,true,true,false,true] (n)) ++ ([false,true])⟩ = some ⟨2,([true]) ++ (rep [true,false,false,true,false,false] (n)) ++ ([true]),([false,true,true,false,true,true,false,true,false,true])⟩ := by
  simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using sweepR table 2 [true] [false,true,true,false,true,true,false,true] [true,false,true,true,false,true] [true,false,false,true,false,false] 26 local1 n (([true])) (([false,true]))

theorem phase2 (n : Nat) : run0 table 62 ⟨2,([true]) ++ (rep [true,false,false,true,false,false] (n)) ++ ([true]),([false,true,true,false,true,true,false,true,false,true])⟩ = some ⟨1,([true,false,false,true,false,false,true,false,false]) ++ (rep [true,false,false,true,false,false] (n)) ++ ([true]),([true,false,true,false,true])⟩ := by rfl

theorem local3 (L R : List Bool) : run0 table 6 ⟨1,([true,false,false,true,false,false,true,false,false]) ++ ([true,false,false,true,false,false]) ++ (L),(R)⟩ = some ⟨1,([true,false,false,true,false,false,true,false,false]) ++ (L),([true,false,true,true,false,true]) ++ (R)⟩ := by rfl

theorem phase3 (n : Nat) : run0 table (6*n) ⟨1,([true,false,false,true,false,false,true,false,false]) ++ (rep [true,false,false,true,false,false] (n)) ++ ([true]),([true,false,true,false,true])⟩ = some ⟨1,([true,false,false,true,false,false,true,false,false,true]),(rep [true,false,true,true,false,true] (n)) ++ ([true,false,true,false,true])⟩ := by
  simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using sweepL table 1 [true,false,false,true,false,false,true,false,false] [] [true,false,false,true,false,false] [true,false,true,true,false,true] 6 local3 n (([true])) (([true,false,true,false,true]))

theorem phase4 (n : Nat) : run0 table 12 ⟨1,([true,false,false,true,false,false,true,false,false,true]),(rep [true,false,true,true,false,true] (n)) ++ ([true,false,true,false,true])⟩ = some ⟨1,[],([true,false,true,true,false,true,true,false,true,true,false,true]) ++ (rep [true,false,true,true,false,true] (n)) ++ ([true,false,true,false,true])⟩ := by rfl

theorem finalL (n : Nat) : ([] : List Bool) = [] := by
  rfl

theorem finalR (n : Nat) : ([true,false,true,true,false,true,true,false,true,true,false,true]) ++ (rep [true,false,true,true,false,true] (n)) ++ ([true,false,true,false,true]) = ([true,false,true,true,false,true,true,false,true,true,false,true,true,false,true]) ++ (rep [true,false,true,true,false,true] (n)) ++ ([false,true]) := by
  calc
    _ = ([true,false,true,true,false,true,true,false,true,true,false,true,true]) ++ (rep [false,true,true,false,true,true] (n)) ++ ([false,true,false,true]) := by symm; simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using moveCut (([true,false,true,true,false,true,true,false,true,true,false,true])) (([false,true,false,true])) [false,true,true,false,true] true n
    _ = ([true,false,true,true,false,true,true,false,true,true,false,true,true,false]) ++ (rep [true,true,false,true,true,false] (n)) ++ ([true,false,true]) := by symm; simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using moveCut (([true,false,true,true,false,true,true,false,true,true,false,true,true])) (([true,false,true])) [true,true,false,true,true] false n
    _ = ([true,false,true,true,false,true,true,false,true,true,false,true,true,false,true]) ++ (rep [true,false,true,true,false,true] (n)) ++ ([false,true]) := by symm; simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using moveCut (([true,false,true,true,false,true,true,false,true,true,false,true,true,false])) (([false,true])) [true,false,true,true,false] true n

theorem growth (n : Nat) : run0 table (75+32*n) (family n) = some (family (n+1)) := by
  have H := (join0 (join0 (join0 (join0 (phase0 n) (phase1 n)) (phase2 n)) (phase3 n)) (phase4 n))
  rw [finalR n] at H
  rw [show 1+26*n+62+6*n+12=75+32*n by omega] at H
  simpa only [family,rep,List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using H

theorem never (m : Machine) (hm : compatible table m) : NeverHalts m :=
  never_of_growth table family 95 (fun n => 75+32*n) entry (by intro n; omega) growth m hm

#print axioms never

end M1230

namespace M1288

-- 1RB0RB_1RC1LE_0RD---_1LD0RA_1LA0LF_0LD0LA

def table : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 0,true => some (some ⟨false,true,1⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 1,true => some (some ⟨true,false,4⟩)
  | 2,false => some (some ⟨false,true,3⟩)
  | 3,false => some (some ⟨true,false,3⟩)
  | 3,true => some (some ⟨false,true,0⟩)
  | 4,false => some (some ⟨true,false,0⟩)
  | 4,true => some (some ⟨false,false,5⟩)
  | 5,false => some (some ⟨false,false,3⟩)
  | 5,true => some (some ⟨false,false,0⟩)
  | _,_ => none

def family (n : Nat) : Z0 := ⟨1,([false]) ++ (rep [false,false,false,true] (n)) ++ ([true]),[]⟩

theorem entry : run0 table 1 ⟨0,[],[]⟩ = some (family 0) := by rfl

theorem phase0 (n : Nat) : run0 table 2 ⟨1,([false]) ++ (rep [false,false,false,true] (n)) ++ ([true]),[]⟩ = some ⟨3,([false,false,true]) ++ (rep [false,false,false,true] (n)) ++ ([true]),[]⟩ := by rfl

theorem local1 (L R : List Bool) : run0 table 10 ⟨3,([false,false,true]) ++ ([false,false,false,true]) ++ (L),(R)⟩ = some ⟨3,([false,false,true]) ++ (L),([false,false,true,true]) ++ (R)⟩ := by rfl

theorem phase1 (n : Nat) : run0 table (10*n) ⟨3,([false,false,true]) ++ (rep [false,false,false,true] (n)) ++ ([true]),[]⟩ = some ⟨3,([false,false,true,true]),(rep [false,false,true,true] (n))⟩ := by
  simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using sweepL table 3 [false,false,true] [] [false,false,false,true] [false,false,true,true] 10 local1 n (([true])) ([])

theorem phase2 (n : Nat) : run0 table 11 ⟨3,([false,false,true,true]),(rep [false,false,true,true] (n))⟩ = some ⟨1,([false,true]),([false,true,true]) ++ (rep [false,false,true,true] (n))⟩ := by rfl

theorem local3 (L R : List Bool) : run0 table 4 ⟨1,([false]) ++ (L),([false,true,true]) ++ ([false,false,true,true]) ++ (R)⟩ = some ⟨1,([false]) ++ ([false,false,false,true]) ++ (L),([false,true,true]) ++ (R)⟩ := by rfl

theorem phase3 (n : Nat) : run0 table (4*n) ⟨1,([false,true]),([false,true,true]) ++ (rep [false,false,true,true] (n))⟩ = some ⟨1,([false]) ++ (rep [false,false,false,true] (n)) ++ ([true]),([false,true,true])⟩ := by
  simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using sweepR table 1 [false] [false,true,true] [false,false,true,true] [false,false,false,true] 4 local3 n (([true])) ([])

theorem phase4 (n : Nat) : run0 table 4 ⟨1,([false]) ++ (rep [false,false,false,true] (n)) ++ ([true]),([false,true,true])⟩ = some ⟨1,([false,false,false,false,true]) ++ (rep [false,false,false,true] (n)) ++ ([true]),[]⟩ := by rfl

theorem finalL (n : Nat) : ([false,false,false,false,true]) ++ (rep [false,false,false,true] (n)) ++ ([true]) = ([false,false,false,false,true]) ++ (rep [false,false,false,true] (n)) ++ ([true]) := by
  rfl

theorem finalR (n : Nat) : ([] : List Bool) = [] := by
  rfl

theorem growth (n : Nat) : run0 table (17+14*n) (family n) = some (family (n+1)) := by
  have H := (join0 (join0 (join0 (join0 (phase0 n) (phase1 n)) (phase2 n)) (phase3 n)) (phase4 n))
  rw [show 2+10*n+11+4*n+4=17+14*n by omega] at H
  simpa only [family,rep,List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using H

theorem never (m : Machine) (hm : compatible table m) : NeverHalts m :=
  never_of_growth table family 1 (fun n => 17+14*n) entry (by intro n; omega) growth m hm

#print axioms never

end M1288

namespace M1373

-- 1RB0RB_1RC1LE_0RD0RE_1LD0RA_1LF1LB_0LB---

def table : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 0,true => some (some ⟨false,true,1⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 1,true => some (some ⟨true,false,4⟩)
  | 2,false => some (some ⟨false,true,3⟩)
  | 2,true => some (some ⟨false,true,4⟩)
  | 3,false => some (some ⟨true,false,3⟩)
  | 3,true => some (some ⟨false,true,0⟩)
  | 4,false => some (some ⟨true,false,5⟩)
  | 4,true => some (some ⟨true,false,1⟩)
  | 5,false => some (some ⟨false,false,1⟩)
  | _,_ => none

def family (n : Nat) : Z0 := ⟨4,[],([true,true,true]) ++ (rep [true,true,true,true] (n)) ++ ([false,true,true,true,true])⟩

theorem entry : run0 table 54 ⟨0,[],[]⟩ = some (family 0) := by rfl

theorem phase0 (n : Nat) : run0 table 3 ⟨4,[],([true,true,true]) ++ (rep [true,true,true,true] (n)) ++ ([false,true,true,true,true])⟩ = some ⟨2,([false,true]),([true,true,true,true]) ++ (rep [true,true,true,true] (n)) ++ ([false,true,true,true,true])⟩ := by rfl

theorem local1 (L R : List Bool) : run0 table 28 ⟨2,([false]) ++ (L),([true,true,true,true]) ++ ([true,true,true,true]) ++ (R)⟩ = some ⟨2,([false]) ++ ([true,true,true,true]) ++ (L),([true,true,true,true]) ++ (R)⟩ := by rfl

theorem phase1 (n : Nat) : run0 table (28*n) ⟨2,([false,true]),([true,true,true,true]) ++ (rep [true,true,true,true] (n)) ++ ([false,true,true,true,true])⟩ = some ⟨2,([false]) ++ (rep [true,true,true,true] (n)) ++ ([true]),([true,true,true,true,false,true,true,true,true])⟩ := by
  simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using sweepR table 2 [false] [true,true,true,true] [true,true,true,true] [true,true,true,true] 28 local1 n (([true])) (([false,true,true,true,true]))

theorem phase2 (n : Nat) : run0 table 81 ⟨2,([false]) ++ (rep [true,true,true,true] (n)) ++ ([true]),([true,true,true,true,false,true,true,true,true])⟩ = some ⟨1,([true,true,true,true,true,true]) ++ (rep [true,true,true,true] (n)) ++ ([true]),([false,true,true,true,true])⟩ := by rfl

theorem local3 (L R : List Bool) : run0 table 4 ⟨1,([true,true,true,true,true,true]) ++ ([true,true,true,true]) ++ (L),(R)⟩ = some ⟨1,([true,true,true,true,true,true]) ++ (L),([true,true,true,true]) ++ (R)⟩ := by rfl

theorem phase3 (n : Nat) : run0 table (4*n) ⟨1,([true,true,true,true,true,true]) ++ (rep [true,true,true,true] (n)) ++ ([true]),([false,true,true,true,true])⟩ = some ⟨1,([true,true,true,true,true,true,true]),(rep [true,true,true,true] (n)) ++ ([false,true,true,true,true])⟩ := by
  simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using sweepL table 1 [true,true,true,true,true,true] [] [true,true,true,true] [true,true,true,true] 4 local3 n (([true])) (([false,true,true,true,true]))

theorem phase4 (n : Nat) : run0 table 7 ⟨1,([true,true,true,true,true,true,true]),(rep [true,true,true,true] (n)) ++ ([false,true,true,true,true])⟩ = some ⟨4,[],([true,true,true,true,true,true,true]) ++ (rep [true,true,true,true] (n)) ++ ([false,true,true,true,true])⟩ := by rfl

theorem finalL (n : Nat) : ([] : List Bool) = [] := by
  rfl

theorem finalR (n : Nat) : ([true,true,true,true,true,true,true]) ++ (rep [true,true,true,true] (n)) ++ ([false,true,true,true,true]) = ([true,true,true,true,true,true,true]) ++ (rep [true,true,true,true] (n)) ++ ([false,true,true,true,true]) := by
  rfl

theorem growth (n : Nat) : run0 table (91+32*n) (family n) = some (family (n+1)) := by
  have H := (join0 (join0 (join0 (join0 (phase0 n) (phase1 n)) (phase2 n)) (phase3 n)) (phase4 n))
  rw [show 3+28*n+81+4*n+7=91+32*n by omega] at H
  simpa only [family,rep,List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using H

theorem never (m : Machine) (hm : compatible table m) : NeverHalts m :=
  never_of_growth table family 54 (fun n => 91+32*n) entry (by intro n; omega) growth m hm

#print axioms never

end M1373

namespace M1374

-- 1RB0RB_1RC1LE_0RD1RC_1LD0RA_1LF0LC_0LB---

def table : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 0,true => some (some ⟨false,true,1⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 1,true => some (some ⟨true,false,4⟩)
  | 2,false => some (some ⟨false,true,3⟩)
  | 2,true => some (some ⟨true,true,2⟩)
  | 3,false => some (some ⟨true,false,3⟩)
  | 3,true => some (some ⟨false,true,0⟩)
  | 4,false => some (some ⟨true,false,5⟩)
  | 4,true => some (some ⟨false,false,2⟩)
  | 5,false => some (some ⟨false,false,1⟩)
  | _,_ => none

def family (n : Nat) : Z0 := ⟨2,([false,true,true,true,false,false,false,true]) ++ (rep [true,true,true] (n)),[]⟩

theorem entry : run0 table 20 ⟨0,[],[]⟩ = some (family 0) := by rfl

theorem phase0 (n : Nat) : run0 table 12 ⟨2,([false,true,true,true,false,false,false,true]) ++ (rep [true,true,true] (n)),[]⟩ = some ⟨3,([false,false,false,true]) ++ (rep [true,true,true] (n)),([true,true,false,true,true])⟩ := by rfl

theorem local1 (L R : List Bool) : run0 table 17 ⟨3,([false,false,false,true]) ++ ([true,true,true]) ++ (L),(R)⟩ = some ⟨3,([false,false,false,true]) ++ (L),([true,true,true]) ++ (R)⟩ := by rfl

theorem phase1 (n : Nat) : run0 table (17*n) ⟨3,([false,false,false,true]) ++ (rep [true,true,true] (n)),([true,true,false,true,true])⟩ = some ⟨3,([false,false,false,true]),(rep [true,true,true] (n)) ++ ([true,true,false,true,true])⟩ := by
  simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using sweepL table 3 [false,false,false,true] [] [true,true,true] [true,true,true] 17 local1 n ([]) (([true,true,false,true,true]))

theorem phase2 (n : Nat) : run0 table 9 ⟨3,([false,false,false,true]),(rep [true,true,true] (n)) ++ ([true,true,false,true,true])⟩ = some ⟨2,([false,true]),([true,true,true]) ++ (rep [true,true,true] (n)) ++ ([true,true,false,true,true])⟩ := by rfl

theorem local3 (L R : List Bool) : run0 table 21 ⟨2,([false]) ++ (L),([true,true,true]) ++ ([true,true,true]) ++ (R)⟩ = some ⟨2,([false]) ++ ([true,true,true]) ++ (L),([true,true,true]) ++ (R)⟩ := by rfl

theorem phase3 (n : Nat) : run0 table (21*n) ⟨2,([false,true]),([true,true,true]) ++ (rep [true,true,true] (n)) ++ ([true,true,false,true,true])⟩ = some ⟨2,([false]) ++ (rep [true,true,true] (n)) ++ ([true]),([true,true,true,true,true,false,true,true])⟩ := by
  simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using sweepR table 2 [false] [true,true,true] [true,true,true] [true,true,true] 21 local3 n (([true])) (([true,true,false,true,true]))

theorem phase4 (n : Nat) : run0 table 27 ⟨2,([false]) ++ (rep [true,true,true] (n)) ++ ([true]),([true,true,true,true,true,false,true,true])⟩ = some ⟨2,([false,true,true,true,false,false,false,true,true,true]) ++ (rep [true,true,true] (n)) ++ ([true]),[]⟩ := by rfl

theorem finalL (n : Nat) : ([false,true,true,true,false,false,false,true,true,true]) ++ (rep [true,true,true] (n)) ++ ([true]) = ([false,true,true,true,false,false,false,true,true,true,true]) ++ (rep [true,true,true] (n)) := by
  calc
    _ = ([false,true,true,true,false,false,false,true,true,true,true]) ++ (rep [true,true,true] (n)) := by symm; simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using moveCut (([false,true,true,true,false,false,false,true,true,true])) ([]) [true,true] true n

theorem finalR (n : Nat) : ([] : List Bool) = [] := by
  rfl

theorem growth (n : Nat) : run0 table (48+38*n) (family n) = some (family (n+1)) := by
  have H := (join0 (join0 (join0 (join0 (phase0 n) (phase1 n)) (phase2 n)) (phase3 n)) (phase4 n))
  rw [finalL n] at H
  rw [show 12+17*n+9+21*n+27=48+38*n by omega] at H
  simpa only [family,rep,List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using H

theorem never (m : Machine) (hm : compatible table m) : NeverHalts m :=
  never_of_growth table family 20 (fun n => 48+38*n) entry (by intro n; omega) growth m hm

#print axioms never

end M1374

namespace M1534

-- 1RB0RB_1RC1LF_0RD1RE_1LD0RA_0RC0RB_0LD---

def table : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 0,true => some (some ⟨false,true,1⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 1,true => some (some ⟨true,false,5⟩)
  | 2,false => some (some ⟨false,true,3⟩)
  | 2,true => some (some ⟨true,true,4⟩)
  | 3,false => some (some ⟨true,false,3⟩)
  | 3,true => some (some ⟨false,true,0⟩)
  | 4,false => some (some ⟨false,true,2⟩)
  | 4,true => some (some ⟨false,true,1⟩)
  | 5,false => some (some ⟨false,false,3⟩)
  | _,_ => none

def family (n : Nat) : Z0 := ⟨1,([false]) ++ (rep [false,true] (n)) ++ ([true]) ++ (rep [false,false,false,false] (n)),[]⟩

theorem entry : run0 table 1 ⟨0,[],[]⟩ = some (family 0) := by rfl

theorem phase0 (n : Nat) : run0 table 2 ⟨1,([false]) ++ (rep [false,true] (n)) ++ ([true]) ++ (rep [false,false,false,false] (n)),[]⟩ = some ⟨3,([false,false,true]) ++ (rep [false,true] (n)) ++ ([true]) ++ (rep [false,false,false,false] (n)),[]⟩ := by rfl

theorem local1 (L R : List Bool) : run0 table 6 ⟨3,([false,false,true]) ++ ([false,true]) ++ (L),(R)⟩ = some ⟨3,([false,false,true]) ++ (L),([false,true]) ++ (R)⟩ := by rfl

theorem phase1 (n : Nat) : run0 table (6*n) ⟨3,([false,false,true]) ++ (rep [false,true] (n)) ++ ([true]) ++ (rep [false,false,false,false] (n)),[]⟩ = some ⟨3,([false,false,true,true]) ++ (rep [false,false,false,false] (n)),(rep [false,true] (n))⟩ := by
  simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using sweepL table 3 [false,false,true] [] [false,true] [false,true] 6 local1 n (([true]) ++ (rep [false,false,false,false] (n))) ([])

theorem phase2 (n : Nat) : run0 table 10 ⟨3,([false,false,true,true]) ++ (rep [false,false,false,false] (n)),(rep [false,true] (n))⟩ = some ⟨2,([true,true,false,false]) ++ (rep [false,false,false,false] (n)),(rep [false,true] (n))⟩ := by rfl

theorem local3 (L R : List Bool) : run0 table 2 ⟨2,([true]) ++ (L),([false,true]) ++ (R)⟩ = some ⟨2,([true]) ++ ([false,true]) ++ (L),(R)⟩ := by rfl

theorem phase3 (n : Nat) : run0 table (2*n) ⟨2,([true,true,false,false]) ++ (rep [false,false,false,false] (n)),(rep [false,true] (n))⟩ = some ⟨2,([true]) ++ (rep [false,true] (n)) ++ ([true,false,false]) ++ (rep [false,false,false,false] (n)),[]⟩ := by
  simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using sweepR table 2 [true] [] [false,true] [false,true] 2 local3 n (([true,false,false]) ++ (rep [false,false,false,false] (n))) ([])

theorem phase4 (n : Nat) : run0 table 4 ⟨2,([true]) ++ (rep [false,true] (n)) ++ ([true,false,false]) ++ (rep [false,false,false,false] (n)),[]⟩ = some ⟨3,([false,false,true]) ++ (rep [false,true] (n)) ++ ([true,false,false]) ++ (rep [false,false,false,false] (n)),([true])⟩ := by rfl

theorem local5 (L R : List Bool) : run0 table 6 ⟨3,([false,false,true]) ++ ([false,true]) ++ (L),(R)⟩ = some ⟨3,([false,false,true]) ++ (L),([false,true]) ++ (R)⟩ := by rfl

theorem phase5 (n : Nat) : run0 table (6*n) ⟨3,([false,false,true]) ++ (rep [false,true] (n)) ++ ([true,false,false]) ++ (rep [false,false,false,false] (n)),([true])⟩ = some ⟨3,([false,false,true,true,false,false]) ++ (rep [false,false,false,false] (n)),(rep [false,true] (n)) ++ ([true])⟩ := by
  simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using sweepL table 3 [false,false,true] [] [false,true] [false,true] 6 local5 n (([true,false,false]) ++ (rep [false,false,false,false] (n))) (([true]))

theorem phase6 (n : Nat) : run0 table 10 ⟨3,([false,false,true,true,false,false]) ++ (rep [false,false,false,false] (n)),(rep [false,true] (n)) ++ ([true])⟩ = some ⟨2,([true,true,false,false,false,false]) ++ (rep [false,false,false,false] (n)),(rep [false,true] (n)) ++ ([true])⟩ := by rfl

theorem local7 (L R : List Bool) : run0 table 2 ⟨2,([true]) ++ (L),([false,true]) ++ (R)⟩ = some ⟨2,([true]) ++ ([false,true]) ++ (L),(R)⟩ := by rfl

theorem phase7 (n : Nat) : run0 table (2*n) ⟨2,([true,true,false,false,false,false]) ++ (rep [false,false,false,false] (n)),(rep [false,true] (n)) ++ ([true])⟩ = some ⟨2,([true]) ++ (rep [false,true] (n)) ++ ([true,false,false,false,false]) ++ (rep [false,false,false,false] (n)),([true])⟩ := by
  simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using sweepR table 2 [true] [] [false,true] [false,true] 2 local7 n (([true,false,false,false,false]) ++ (rep [false,false,false,false] (n))) (([true]))

theorem phase8 (n : Nat) : run0 table 2 ⟨2,([true]) ++ (rep [false,true] (n)) ++ ([true,false,false,false,false]) ++ (rep [false,false,false,false] (n)),([true])⟩ = some ⟨1,([false,false,true]) ++ (rep [false,true] (n)) ++ ([true,false,false,false,false]) ++ (rep [false,false,false,false] (n)),[]⟩ := by rfl

theorem finalL (n : Nat) : ([false,false,true]) ++ (rep [false,true] (n)) ++ ([true,false,false,false,false]) ++ (rep [false,false,false,false] (n)) = ([false,false,true]) ++ (rep [false,true] (n)) ++ ([true,false,false,false,false]) ++ (rep [false,false,false,false] (n)) := by
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

end M1534

end BB6.Agent11Raw39B0RBPumps
