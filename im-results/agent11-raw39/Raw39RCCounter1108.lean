import Raw39CounterCarry
open BB6Coverage BB6Coverage.Agent31Pump BB6.Agent11CounterCarry
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedVariables false
namespace BB6.Agent11Raw39RCCounter1108
namespace M1108

namespace MInit

-- 1RB0RC_1RC---_0RD1LE_1LD0RA_1LF0RE_0LF1RB

def table : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 0,true => some (some ⟨false,true,2⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 2,false => some (some ⟨false,true,3⟩)
  | 2,true => some (some ⟨true,false,4⟩)
  | 3,false => some (some ⟨true,false,3⟩)
  | 3,true => some (some ⟨false,true,0⟩)
  | 4,false => some (some ⟨true,false,5⟩)
  | 4,true => some (some ⟨false,true,4⟩)
  | 5,false => some (some ⟨false,false,5⟩)
  | 5,true => some (some ⟨true,true,1⟩)
  | _,_ => none

theorem phase0 (n : Nat) : run0 table 1 ⟨4,([false]) ++ (rep [false] (n)) ++ ([false,false,false,true]),[]⟩ = some ⟨5,(rep [false] (n)) ++ ([false,false,false,true]),([true])⟩ := by rfl

theorem local1 (L R : List Bool) : run0 table 1 ⟨5,([false]) ++ (L),(R)⟩ = some ⟨5,(L),([false]) ++ (R)⟩ := by rfl

theorem phase1 (n : Nat) : run0 table (1*n) ⟨5,(rep [false] (n)) ++ ([false,false,false,true]),([true])⟩ = some ⟨5,([false,false,false,true]),(rep [false] (n)) ++ ([true])⟩ := by
  simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using sweepL table 5 [] [] [false] [false] 1 local1 n (([false,false,false,true])) (([true]))

theorem phase2 (n : Nat) : run0 table 4 ⟨5,([false,false,false,true]),(rep [false] (n)) ++ ([true])⟩ = some ⟨1,([false,true]),([false,false]) ++ (rep [false] (n)) ++ ([true])⟩ := by rfl

theorem finalL (n : Nat) : ([false,true]) = ([false,true]) := by
  rfl

theorem finalR (n : Nat) : ([false,false]) ++ (rep [false] (n)) ++ ([true]) = ([false,false]) ++ (rep [false] (n)) ++ ([true]) := by
  rfl

theorem epoch (n : Nat) : run0 table (5+1*n) ⟨4,([false]) ++ (rep [false] (n)) ++ ([false,false,false,true]),[]⟩ = some ⟨1,([false,true]),([false,false]) ++ (rep [false] (n)) ++ ([true])⟩ := by
  have H := (join0 (join0 (phase0 n) (phase1 n)) (phase2 n))
  rw [show 1+1*n+4=5+1*n by omega] at H
  exact H

theorem canon (n : Nat) : run0 table (5+1*n) ⟨4,([false]) ++ (rep [false] (n)) ++ ([false,false,false,true]),[]⟩ = some ⟨1,([false,true]),([false,false]) ++ (rep [false] (n)) ++ ([true])⟩ := by
  exact epoch n

end MInit


namespace MFinish

-- 1RB0RC_1RC---_0RD1LE_1LD0RA_1LF0RE_0LF1RB

def table : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 0,true => some (some ⟨false,true,2⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 2,false => some (some ⟨false,true,3⟩)
  | 2,true => some (some ⟨true,false,4⟩)
  | 3,false => some (some ⟨true,false,3⟩)
  | 3,true => some (some ⟨false,true,0⟩)
  | 4,false => some (some ⟨true,false,5⟩)
  | 4,true => some (some ⟨false,true,4⟩)
  | 5,false => some (some ⟨false,false,5⟩)
  | 5,true => some (some ⟨true,true,1⟩)
  | _,_ => none

theorem phase0 (n : Nat) : run0 table 12 ⟨1,([false,true]),([false,false]) ++ (rep [true] (n)) ++ ([true])⟩ = some ⟨4,([true,true]),([true,true]) ++ (rep [true] (n)) ++ ([true])⟩ := by rfl

theorem local1 (L R : List Bool) : run0 table 1 ⟨4,([true]) ++ (L),([true,true]) ++ ([true]) ++ (R)⟩ = some ⟨4,([true]) ++ ([false]) ++ (L),([true,true]) ++ (R)⟩ := by rfl

theorem phase1 (n : Nat) : run0 table (1*n) ⟨4,([true,true]),([true,true]) ++ (rep [true] (n)) ++ ([true])⟩ = some ⟨4,([true]) ++ (rep [false] (n)) ++ ([true]),([true,true,true])⟩ := by
  simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using sweepR table 4 [true] [true,true] [true] [false] 1 local1 n (([true])) (([true]))

theorem phase2 (n : Nat) : run0 table 4 ⟨4,([true]) ++ (rep [false] (n)) ++ ([true]),([true,true,true])⟩ = some ⟨4,([false,false,false,false,false]) ++ (rep [false] (n)) ++ ([true]),[]⟩ := by rfl

theorem finalL (n : Nat) : ([false,false,false,false,false]) ++ (rep [false] (n)) ++ ([true]) = (rep [false] (n)) ++ ([false,false,false,false,false,true]) := by
  calc
    _ = ([false,false,false,false]) ++ (rep [false] (n)) ++ ([false,true]) := by simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using moveCut (([false,false,false,false])) (([true])) [] false n
    _ = ([false,false,false]) ++ (rep [false] (n)) ++ ([false,false,true]) := by simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using moveCut (([false,false,false])) (([false,true])) [] false n
    _ = ([false,false]) ++ (rep [false] (n)) ++ ([false,false,false,true]) := by simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using moveCut (([false,false])) (([false,false,true])) [] false n
    _ = ([false]) ++ (rep [false] (n)) ++ ([false,false,false,false,true]) := by simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using moveCut (([false])) (([false,false,false,true])) [] false n
    _ = (rep [false] (n)) ++ ([false,false,false,false,false,true]) := by simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using moveCut ([]) (([false,false,false,false,true])) [] false n

theorem finalR (n : Nat) : ([] : List Bool) = [] := by
  rfl

theorem epoch (n : Nat) : run0 table (16+1*n) ⟨1,([false,true]),([false,false]) ++ (rep [true] (n)) ++ ([true])⟩ = some ⟨4,(rep [false] (n)) ++ ([false,false,false,false,false,true]),[]⟩ := by
  have H := (join0 (join0 (phase0 n) (phase1 n)) (phase2 n))
  rw [finalL n] at H
  rw [show 12+1*n+4=16+1*n by omega] at H
  exact H

theorem eq1l (n : Nat) : (rep [false] (n)) ++ ([false,false,false,false,false,true]) = ([false,false]) ++ (rep [false] (n)) ++ ([false,false,false,true]) := by
  calc
    _ = ([false]) ++ (rep [false] (n)) ++ ([false,false,false,false,true]) := by symm; simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using moveCut ([]) (([false,false,false,false,true])) [] false n
    _ = ([false,false]) ++ (rep [false] (n)) ++ ([false,false,false,true]) := by symm; simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using moveCut (([false])) (([false,false,false,true])) [] false n

theorem canon (n : Nat) : run0 table (16+1*n) ⟨1,([false,true]),([false,false]) ++ (rep [true] (n)) ++ ([true])⟩ = some ⟨4,([false,false]) ++ (rep [false] (n)) ++ ([false,false,false,true]),[]⟩ := by
  simpa only [eq1l n] using epoch n

end MFinish


namespace MCarry

-- 1RB0RC_1RC---_0RD1LE_1LD0RA_1LF0RE_0LF1RB

def table : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 0,true => some (some ⟨false,true,2⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 2,false => some (some ⟨false,true,3⟩)
  | 2,true => some (some ⟨true,false,4⟩)
  | 3,false => some (some ⟨true,false,3⟩)
  | 3,true => some (some ⟨false,true,0⟩)
  | 4,false => some (some ⟨true,false,5⟩)
  | 4,true => some (some ⟨false,true,4⟩)
  | 5,false => some (some ⟨false,false,5⟩)
  | 5,true => some (some ⟨true,true,1⟩)
  | _,_ => none

theorem phase0 (n : Nat) (R : List Bool) : run0 table 12 ⟨1,([false,true]),([false,false]) ++ (rep [true] (n)) ++ ([true,false]) ++ (R)⟩ = some ⟨4,([true,true]),([true,true]) ++ (rep [true] (n)) ++ ([true,false]) ++ (R)⟩ := by rfl

theorem local1 (L R : List Bool) : run0 table 1 ⟨4,([true]) ++ (L),([true,true]) ++ ([true]) ++ (R)⟩ = some ⟨4,([true]) ++ ([false]) ++ (L),([true,true]) ++ (R)⟩ := by rfl

theorem phase1 (n : Nat) (R : List Bool) : run0 table (1*n) ⟨4,([true,true]),([true,true]) ++ (rep [true] (n)) ++ ([true,false]) ++ (R)⟩ = some ⟨4,([true]) ++ (rep [false] (n)) ++ ([true]),([true,true,true,false]) ++ (R)⟩ := by
  simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using sweepR table 4 [true] [true,true] [true] [false] 1 local1 n (([true])) (([true,false]) ++ (R))

theorem phase2 (n : Nat) (R : List Bool) : run0 table 5 ⟨4,([true]) ++ (rep [false] (n)) ++ ([true]),([true,true,true,false]) ++ (R)⟩ = some ⟨5,([false,false,false,false]) ++ (rep [false] (n)) ++ ([true]),([true]) ++ (R)⟩ := by rfl

theorem local3 (L R : List Bool) : run0 table 1 ⟨5,([false,false,false,false]) ++ ([false]) ++ (L),(R)⟩ = some ⟨5,([false,false,false,false]) ++ (L),([false]) ++ (R)⟩ := by rfl

theorem phase3 (n : Nat) (R : List Bool) : run0 table (1*n) ⟨5,([false,false,false,false]) ++ (rep [false] (n)) ++ ([true]),([true]) ++ (R)⟩ = some ⟨5,([false,false,false,false,true]),(rep [false] (n)) ++ ([true]) ++ (R)⟩ := by
  simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using sweepL table 5 [false,false,false,false] [] [false] [false] 1 local3 n (([true])) (([true]) ++ (R))

theorem phase4 (n : Nat) (R : List Bool) : run0 table 5 ⟨5,([false,false,false,false,true]),(rep [false] (n)) ++ ([true]) ++ (R)⟩ = some ⟨1,([false,true]),([false,false,false]) ++ (rep [false] (n)) ++ ([true]) ++ (R)⟩ := by rfl

theorem finalL (n : Nat) (R : List Bool) : ([false,true]) = ([false,true]) := by
  rfl

theorem finalR (n : Nat) (R : List Bool) : ([false,false,false]) ++ (rep [false] (n)) ++ ([true]) ++ (R) = ([false,false]) ++ (rep [false] (n)) ++ ([false,true]) ++ (R) := by
  calc
    _ = ([false,false]) ++ (rep [false] (n)) ++ ([false,true]) ++ (R) := by simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using moveCut (([false,false])) (([true]) ++ (R)) [] false n

theorem epoch (n : Nat) (R : List Bool) : run0 table (22+2*n) ⟨1,([false,true]),([false,false]) ++ (rep [true] (n)) ++ ([true,false]) ++ (R)⟩ = some ⟨1,([false,true]),([false,false]) ++ (rep [false] (n)) ++ ([false,true]) ++ (R)⟩ := by
  have H := (join0 (join0 (join0 (join0 (phase0 n R) (phase1 n R)) (phase2 n R)) (phase3 n R)) (phase4 n R))
  rw [finalR n R] at H
  rw [show 12+1*n+5+1*n+5=22+2*n by omega] at H
  exact H

theorem canon (n : Nat) (R : List Bool) : run0 table (22+2*n) ⟨1,([false,true]),([false,false]) ++ (rep [true] (n)) ++ ([true,false]) ++ (R)⟩ = some ⟨1,([false,true]),([false,false]) ++ (rep [false] (n)) ++ ([false,true]) ++ (R)⟩ := by
  exact epoch n R

end MCarry


abbrev table := MInit.table
abbrev A : List Bool := [true]
abbrev Z : List Bool := [false]
def Q (R : List Bool) : Z0 := ⟨1,[false,true],([false,false]) ++ (R)⟩
def family (n : Nat) : Z0 := ⟨4,([false]) ++ (rep [false] (n)) ++ ([false,false,false,true]),[]⟩
def carryCost (n : Nat) : Nat := 20+2*n

theorem carry (n : Nat) (R : List Bool) : run0 table (carryCost n) (Q (rep A n ++ Z ++ R)) = some (Q (rep Z n ++ A ++ R)) := by
  cases n with
  | zero => rfl
  | succ n =>
    have h := MCarry.canon n R
    rw [show MCarry.table = table from rfl] at h
    unfold carryCost
    rw [show 20+2*n.succ = 22+2*n by omega]
    rw [rep_succ_snoc A n,rep_succ_snoc Z n]
    simpa only [table,Q,A,Z,List.append_assoc,List.nil_append,List.append_nil,List.cons_append] using h

theorem entry : run0 table 16 ⟨0,[],[]⟩ = some (family 0) := by rfl


def cost (n : Nat) : Nat := (5+1*n) + fillCost carryCost (n+0) + (16+1*n)

theorem growth (n : Nat) : run0 table (cost n) (family n) = some (family (n+1)) := by
  have h1 := MInit.canon n
  have h2 := fill table Q A Z carryCost carry (n+0) [true]
  have h3 := MFinish.canon n
  rw [rep_add Z n 0,rep_add A n 0] at h2
  simp only [Q,A,Z,rep,List.append_assoc,List.nil_append,List.append_nil,List.cons_append] at h2
  have h := join0 (join0 h1 h2) h3
  simpa only [cost,family,rep,rep_succ_snoc,List.append_assoc,List.nil_append,List.append_nil,List.cons_append] using h


theorem never (m : Machine) (hm : compatible table m) : NeverHalts m :=
  never_of_growth table family 16 cost entry (by intro n; unfold cost; omega) growth m hm

#print axioms growth
#print axioms never
end M1108
namespace M1412

namespace MInit

-- 1RB0RC_1RC---_0RD1LF_1LD0RA_0LE1RB_1LE0RF

def table : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 0,true => some (some ⟨false,true,2⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 2,false => some (some ⟨false,true,3⟩)
  | 2,true => some (some ⟨true,false,5⟩)
  | 3,false => some (some ⟨true,false,3⟩)
  | 3,true => some (some ⟨false,true,0⟩)
  | 4,false => some (some ⟨false,false,4⟩)
  | 4,true => some (some ⟨true,true,1⟩)
  | 5,false => some (some ⟨true,false,4⟩)
  | 5,true => some (some ⟨false,true,5⟩)
  | _,_ => none

theorem phase0 (n : Nat) : run0 table 1 ⟨5,([false]) ++ (rep [false] (n)) ++ ([false,false,false,true]),[]⟩ = some ⟨4,(rep [false] (n)) ++ ([false,false,false,true]),([true])⟩ := by rfl

theorem local1 (L R : List Bool) : run0 table 1 ⟨4,([false]) ++ (L),(R)⟩ = some ⟨4,(L),([false]) ++ (R)⟩ := by rfl

theorem phase1 (n : Nat) : run0 table (1*n) ⟨4,(rep [false] (n)) ++ ([false,false,false,true]),([true])⟩ = some ⟨4,([false,false,false,true]),(rep [false] (n)) ++ ([true])⟩ := by
  simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using sweepL table 4 [] [] [false] [false] 1 local1 n (([false,false,false,true])) (([true]))

theorem phase2 (n : Nat) : run0 table 4 ⟨4,([false,false,false,true]),(rep [false] (n)) ++ ([true])⟩ = some ⟨1,([false,true]),([false,false]) ++ (rep [false] (n)) ++ ([true])⟩ := by rfl

theorem finalL (n : Nat) : ([false,true]) = ([false,true]) := by
  rfl

theorem finalR (n : Nat) : ([false,false]) ++ (rep [false] (n)) ++ ([true]) = ([false,false]) ++ (rep [false] (n)) ++ ([true]) := by
  rfl

theorem epoch (n : Nat) : run0 table (5+1*n) ⟨5,([false]) ++ (rep [false] (n)) ++ ([false,false,false,true]),[]⟩ = some ⟨1,([false,true]),([false,false]) ++ (rep [false] (n)) ++ ([true])⟩ := by
  have H := (join0 (join0 (phase0 n) (phase1 n)) (phase2 n))
  rw [show 1+1*n+4=5+1*n by omega] at H
  exact H

theorem canon (n : Nat) : run0 table (5+1*n) ⟨5,([false]) ++ (rep [false] (n)) ++ ([false,false,false,true]),[]⟩ = some ⟨1,([false,true]),([false,false]) ++ (rep [false] (n)) ++ ([true])⟩ := by
  exact epoch n

end MInit


namespace MFinish

-- 1RB0RC_1RC---_0RD1LF_1LD0RA_0LE1RB_1LE0RF

def table : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 0,true => some (some ⟨false,true,2⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 2,false => some (some ⟨false,true,3⟩)
  | 2,true => some (some ⟨true,false,5⟩)
  | 3,false => some (some ⟨true,false,3⟩)
  | 3,true => some (some ⟨false,true,0⟩)
  | 4,false => some (some ⟨false,false,4⟩)
  | 4,true => some (some ⟨true,true,1⟩)
  | 5,false => some (some ⟨true,false,4⟩)
  | 5,true => some (some ⟨false,true,5⟩)
  | _,_ => none

theorem phase0 (n : Nat) : run0 table 12 ⟨1,([false,true]),([false,false]) ++ (rep [true] (n)) ++ ([true])⟩ = some ⟨5,([true,true]),([true,true]) ++ (rep [true] (n)) ++ ([true])⟩ := by rfl

theorem local1 (L R : List Bool) : run0 table 1 ⟨5,([true]) ++ (L),([true,true]) ++ ([true]) ++ (R)⟩ = some ⟨5,([true]) ++ ([false]) ++ (L),([true,true]) ++ (R)⟩ := by rfl

theorem phase1 (n : Nat) : run0 table (1*n) ⟨5,([true,true]),([true,true]) ++ (rep [true] (n)) ++ ([true])⟩ = some ⟨5,([true]) ++ (rep [false] (n)) ++ ([true]),([true,true,true])⟩ := by
  simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using sweepR table 5 [true] [true,true] [true] [false] 1 local1 n (([true])) (([true]))

theorem phase2 (n : Nat) : run0 table 4 ⟨5,([true]) ++ (rep [false] (n)) ++ ([true]),([true,true,true])⟩ = some ⟨5,([false,false,false,false,false]) ++ (rep [false] (n)) ++ ([true]),[]⟩ := by rfl

theorem finalL (n : Nat) : ([false,false,false,false,false]) ++ (rep [false] (n)) ++ ([true]) = (rep [false] (n)) ++ ([false,false,false,false,false,true]) := by
  calc
    _ = ([false,false,false,false]) ++ (rep [false] (n)) ++ ([false,true]) := by simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using moveCut (([false,false,false,false])) (([true])) [] false n
    _ = ([false,false,false]) ++ (rep [false] (n)) ++ ([false,false,true]) := by simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using moveCut (([false,false,false])) (([false,true])) [] false n
    _ = ([false,false]) ++ (rep [false] (n)) ++ ([false,false,false,true]) := by simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using moveCut (([false,false])) (([false,false,true])) [] false n
    _ = ([false]) ++ (rep [false] (n)) ++ ([false,false,false,false,true]) := by simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using moveCut (([false])) (([false,false,false,true])) [] false n
    _ = (rep [false] (n)) ++ ([false,false,false,false,false,true]) := by simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using moveCut ([]) (([false,false,false,false,true])) [] false n

theorem finalR (n : Nat) : ([] : List Bool) = [] := by
  rfl

theorem epoch (n : Nat) : run0 table (16+1*n) ⟨1,([false,true]),([false,false]) ++ (rep [true] (n)) ++ ([true])⟩ = some ⟨5,(rep [false] (n)) ++ ([false,false,false,false,false,true]),[]⟩ := by
  have H := (join0 (join0 (phase0 n) (phase1 n)) (phase2 n))
  rw [finalL n] at H
  rw [show 12+1*n+4=16+1*n by omega] at H
  exact H

theorem eq1l (n : Nat) : (rep [false] (n)) ++ ([false,false,false,false,false,true]) = ([false,false]) ++ (rep [false] (n)) ++ ([false,false,false,true]) := by
  calc
    _ = ([false]) ++ (rep [false] (n)) ++ ([false,false,false,false,true]) := by symm; simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using moveCut ([]) (([false,false,false,false,true])) [] false n
    _ = ([false,false]) ++ (rep [false] (n)) ++ ([false,false,false,true]) := by symm; simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using moveCut (([false])) (([false,false,false,true])) [] false n

theorem canon (n : Nat) : run0 table (16+1*n) ⟨1,([false,true]),([false,false]) ++ (rep [true] (n)) ++ ([true])⟩ = some ⟨5,([false,false]) ++ (rep [false] (n)) ++ ([false,false,false,true]),[]⟩ := by
  simpa only [eq1l n] using epoch n

end MFinish


namespace MCarry

-- 1RB0RC_1RC---_0RD1LF_1LD0RA_0LE1RB_1LE0RF

def table : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 0,true => some (some ⟨false,true,2⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 2,false => some (some ⟨false,true,3⟩)
  | 2,true => some (some ⟨true,false,5⟩)
  | 3,false => some (some ⟨true,false,3⟩)
  | 3,true => some (some ⟨false,true,0⟩)
  | 4,false => some (some ⟨false,false,4⟩)
  | 4,true => some (some ⟨true,true,1⟩)
  | 5,false => some (some ⟨true,false,4⟩)
  | 5,true => some (some ⟨false,true,5⟩)
  | _,_ => none

theorem phase0 (n : Nat) (R : List Bool) : run0 table 12 ⟨1,([false,true]),([false,false]) ++ (rep [true] (n)) ++ ([true,false]) ++ (R)⟩ = some ⟨5,([true,true]),([true,true]) ++ (rep [true] (n)) ++ ([true,false]) ++ (R)⟩ := by rfl

theorem local1 (L R : List Bool) : run0 table 1 ⟨5,([true]) ++ (L),([true,true]) ++ ([true]) ++ (R)⟩ = some ⟨5,([true]) ++ ([false]) ++ (L),([true,true]) ++ (R)⟩ := by rfl

theorem phase1 (n : Nat) (R : List Bool) : run0 table (1*n) ⟨5,([true,true]),([true,true]) ++ (rep [true] (n)) ++ ([true,false]) ++ (R)⟩ = some ⟨5,([true]) ++ (rep [false] (n)) ++ ([true]),([true,true,true,false]) ++ (R)⟩ := by
  simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using sweepR table 5 [true] [true,true] [true] [false] 1 local1 n (([true])) (([true,false]) ++ (R))

theorem phase2 (n : Nat) (R : List Bool) : run0 table 5 ⟨5,([true]) ++ (rep [false] (n)) ++ ([true]),([true,true,true,false]) ++ (R)⟩ = some ⟨4,([false,false,false,false]) ++ (rep [false] (n)) ++ ([true]),([true]) ++ (R)⟩ := by rfl

theorem local3 (L R : List Bool) : run0 table 1 ⟨4,([false,false,false,false]) ++ ([false]) ++ (L),(R)⟩ = some ⟨4,([false,false,false,false]) ++ (L),([false]) ++ (R)⟩ := by rfl

theorem phase3 (n : Nat) (R : List Bool) : run0 table (1*n) ⟨4,([false,false,false,false]) ++ (rep [false] (n)) ++ ([true]),([true]) ++ (R)⟩ = some ⟨4,([false,false,false,false,true]),(rep [false] (n)) ++ ([true]) ++ (R)⟩ := by
  simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using sweepL table 4 [false,false,false,false] [] [false] [false] 1 local3 n (([true])) (([true]) ++ (R))

theorem phase4 (n : Nat) (R : List Bool) : run0 table 5 ⟨4,([false,false,false,false,true]),(rep [false] (n)) ++ ([true]) ++ (R)⟩ = some ⟨1,([false,true]),([false,false,false]) ++ (rep [false] (n)) ++ ([true]) ++ (R)⟩ := by rfl

theorem finalL (n : Nat) (R : List Bool) : ([false,true]) = ([false,true]) := by
  rfl

theorem finalR (n : Nat) (R : List Bool) : ([false,false,false]) ++ (rep [false] (n)) ++ ([true]) ++ (R) = ([false,false]) ++ (rep [false] (n)) ++ ([false,true]) ++ (R) := by
  calc
    _ = ([false,false]) ++ (rep [false] (n)) ++ ([false,true]) ++ (R) := by simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using moveCut (([false,false])) (([true]) ++ (R)) [] false n

theorem epoch (n : Nat) (R : List Bool) : run0 table (22+2*n) ⟨1,([false,true]),([false,false]) ++ (rep [true] (n)) ++ ([true,false]) ++ (R)⟩ = some ⟨1,([false,true]),([false,false]) ++ (rep [false] (n)) ++ ([false,true]) ++ (R)⟩ := by
  have H := (join0 (join0 (join0 (join0 (phase0 n R) (phase1 n R)) (phase2 n R)) (phase3 n R)) (phase4 n R))
  rw [finalR n R] at H
  rw [show 12+1*n+5+1*n+5=22+2*n by omega] at H
  exact H

theorem canon (n : Nat) (R : List Bool) : run0 table (22+2*n) ⟨1,([false,true]),([false,false]) ++ (rep [true] (n)) ++ ([true,false]) ++ (R)⟩ = some ⟨1,([false,true]),([false,false]) ++ (rep [false] (n)) ++ ([false,true]) ++ (R)⟩ := by
  exact epoch n R

end MCarry


abbrev table := MInit.table
abbrev A : List Bool := [true]
abbrev Z : List Bool := [false]
def Q (R : List Bool) : Z0 := ⟨1,[false,true],([false,false]) ++ (R)⟩
def family (n : Nat) : Z0 := ⟨5,([false]) ++ (rep [false] (n)) ++ ([false,false,false,true]),[]⟩
def carryCost (n : Nat) : Nat := 20+2*n

theorem carry (n : Nat) (R : List Bool) : run0 table (carryCost n) (Q (rep A n ++ Z ++ R)) = some (Q (rep Z n ++ A ++ R)) := by
  cases n with
  | zero => rfl
  | succ n =>
    have h := MCarry.canon n R
    rw [show MCarry.table = table from rfl] at h
    unfold carryCost
    rw [show 20+2*n.succ = 22+2*n by omega]
    rw [rep_succ_snoc A n,rep_succ_snoc Z n]
    simpa only [table,Q,A,Z,List.append_assoc,List.nil_append,List.append_nil,List.cons_append] using h

theorem entry : run0 table 16 ⟨0,[],[]⟩ = some (family 0) := by rfl


def cost (n : Nat) : Nat := (5+1*n) + fillCost carryCost (n+0) + (16+1*n)

theorem growth (n : Nat) : run0 table (cost n) (family n) = some (family (n+1)) := by
  have h1 := MInit.canon n
  have h2 := fill table Q A Z carryCost carry (n+0) [true]
  have h3 := MFinish.canon n
  rw [rep_add Z n 0,rep_add A n 0] at h2
  simp only [Q,A,Z,rep,List.append_assoc,List.nil_append,List.append_nil,List.cons_append] at h2
  have h := join0 (join0 h1 h2) h3
  simpa only [cost,family,rep,rep_succ_snoc,List.append_assoc,List.nil_append,List.append_nil,List.cons_append] using h


theorem never (m : Machine) (hm : compatible table m) : NeverHalts m :=
  never_of_growth table family 16 cost entry (by intro n; unfold cost; omega) growth m hm

#print axioms growth
#print axioms never
end M1412

end BB6.Agent11Raw39RCCounter1108
