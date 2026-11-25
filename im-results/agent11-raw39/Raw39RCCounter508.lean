import Raw39CounterCarry
open BB6Coverage BB6Coverage.Agent31Pump BB6.Agent11CounterCarry
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedVariables false
namespace BB6.Agent11Raw39RCCounter508
namespace M508

namespace MInit

-- 1RB0RC_1RC0LE_0RD0RF_1LD0RA_1LB---_0RC1LE

def table : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 0,true => some (some ⟨false,true,2⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 1,true => some (some ⟨false,false,4⟩)
  | 2,false => some (some ⟨false,true,3⟩)
  | 2,true => some (some ⟨false,true,5⟩)
  | 3,false => some (some ⟨true,false,3⟩)
  | 3,true => some (some ⟨false,true,0⟩)
  | 4,false => some (some ⟨true,false,1⟩)
  | 5,false => some (some ⟨false,true,2⟩)
  | 5,true => some (some ⟨true,false,4⟩)
  | _,_ => none

theorem phase0 (n : Nat) : run0 table 1 ⟨1,[],([true,false]) ++ (rep [true,false] (n)) ++ ([true,true,true,true,true])⟩ = some ⟨2,([true,true]),([false]) ++ (rep [true,false] (n)) ++ ([true,true,true,true,true])⟩ := by rfl

theorem local1 (L R : List Bool) : run0 table 2 ⟨2,([true]) ++ (L),([false]) ++ ([true,false]) ++ (R)⟩ = some ⟨2,([true]) ++ ([false,false]) ++ (L),([false]) ++ (R)⟩ := by rfl

theorem phase1 (n : Nat) : run0 table (2*n) ⟨2,([true,true]),([false]) ++ (rep [true,false] (n)) ++ ([true,true,true,true,true])⟩ = some ⟨2,([true]) ++ (rep [false,false] (n)) ++ ([true]),([false,true,true,true,true,true])⟩ := by
  simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using sweepR table 2 [true] [false] [true,false] [false,false] 2 local1 n (([true])) (([true,true,true,true,true]))

theorem phase2 (n : Nat) : run0 table 5 ⟨2,([true]) ++ (rep [false,false] (n)) ++ ([true]),([false,true,true,true,true,true])⟩ = some ⟨1,([false,false]) ++ (rep [false,false] (n)) ++ ([true]),([true,true,true,true,true])⟩ := by rfl

theorem finalL (n : Nat) : ([false,false]) ++ (rep [false,false] (n)) ++ ([true]) = (rep [false,false] (n)) ++ ([false,false,true]) := by
  calc
    _ = ([false]) ++ (rep [false,false] (n)) ++ ([false,true]) := by simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using moveCut (([false])) (([true])) [false] false n
    _ = (rep [false,false] (n)) ++ ([false,false,true]) := by simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using moveCut ([]) (([false,true])) [false] false n

theorem finalR (n : Nat) : ([true,true,true,true,true]) = ([true,true,true,true,true]) := by
  rfl

theorem epoch (n : Nat) : run0 table (6+2*n) ⟨1,[],([true,false]) ++ (rep [true,false] (n)) ++ ([true,true,true,true,true])⟩ = some ⟨1,(rep [false,false] (n)) ++ ([false,false,true]),([true,true,true,true,true])⟩ := by
  have H := (join0 (join0 (phase0 n) (phase1 n)) (phase2 n))
  rw [finalL n] at H
  rw [show 1+2*n+5=6+2*n by omega] at H
  exact H

theorem canon (n : Nat) : run0 table (6+2*n) ⟨1,[],([true,false]) ++ (rep [true,false] (n)) ++ ([true,true,true,true,true])⟩ = some ⟨1,(rep [false,false] (n)) ++ ([false,false,true]),([true,true,true,true,true])⟩ := by
  exact epoch n

end MInit


namespace MFinish

-- 1RB0RC_1RC0LE_0RD0RF_1LD0RA_1LB---_0RC1LE

def table : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 0,true => some (some ⟨false,true,2⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 1,true => some (some ⟨false,false,4⟩)
  | 2,false => some (some ⟨false,true,3⟩)
  | 2,true => some (some ⟨false,true,5⟩)
  | 3,false => some (some ⟨true,false,3⟩)
  | 3,true => some (some ⟨false,true,0⟩)
  | 4,false => some (some ⟨true,false,1⟩)
  | 5,false => some (some ⟨false,true,2⟩)
  | 5,true => some (some ⟨true,false,4⟩)
  | _,_ => none

theorem local0 (L R : List Bool) : run0 table 2 ⟨1,([true,false]) ++ (L),(R)⟩ = some ⟨1,(L),([true,false]) ++ (R)⟩ := by rfl

theorem phase0 (n : Nat) : run0 table (2*n) ⟨1,(rep [true,false] (n)) ++ ([true,false,true]),([true,true,true,true,true])⟩ = some ⟨1,([true,false,true]),(rep [true,false] (n)) ++ ([true,true,true,true,true])⟩ := by
  simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using sweepL table 1 [] [] [true,false] [true,false] 2 local0 n (([true,false,true])) (([true,true,true,true,true]))

theorem phase1 (n : Nat) : run0 table 4 ⟨1,([true,false,true]),(rep [true,false] (n)) ++ ([true,true,true,true,true])⟩ = some ⟨1,[],([true,false,true,false]) ++ (rep [true,false] (n)) ++ ([true,true,true,true,true])⟩ := by rfl

theorem finalL (n : Nat) : ([] : List Bool) = [] := by
  rfl

theorem finalR (n : Nat) : ([true,false,true,false]) ++ (rep [true,false] (n)) ++ ([true,true,true,true,true]) = (rep [true,false] (n)) ++ ([true,false,true,false,true,true,true,true,true]) := by
  calc
    _ = ([true,false,true]) ++ (rep [false,true] (n)) ++ ([false,true,true,true,true,true]) := by simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using moveCut (([true,false,true])) (([true,true,true,true,true])) [true] false n
    _ = ([true,false]) ++ (rep [true,false] (n)) ++ ([true,false,true,true,true,true,true]) := by simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using moveCut (([true,false])) (([false,true,true,true,true,true])) [false] true n
    _ = ([true]) ++ (rep [false,true] (n)) ++ ([false,true,false,true,true,true,true,true]) := by simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using moveCut (([true])) (([true,false,true,true,true,true,true])) [true] false n
    _ = (rep [true,false] (n)) ++ ([true,false,true,false,true,true,true,true,true]) := by simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using moveCut ([]) (([false,true,false,true,true,true,true,true])) [false] true n

theorem epoch (n : Nat) : run0 table (4+2*n) ⟨1,(rep [true,false] (n)) ++ ([true,false,true]),([true,true,true,true,true])⟩ = some ⟨1,[],(rep [true,false] (n)) ++ ([true,false,true,false,true,true,true,true,true])⟩ := by
  have H := (join0 (phase0 n) (phase1 n))
  rw [finalR n] at H
  rw [show 2*n+4=4+2*n by omega] at H
  exact H

theorem eq1r (n : Nat) : (rep [true,false] (n)) ++ ([true,false,true,false,true,true,true,true,true]) = ([true,false,true,false]) ++ (rep [true,false] (n)) ++ ([true,true,true,true,true]) := by
  calc
    _ = ([true]) ++ (rep [false,true] (n)) ++ ([false,true,false,true,true,true,true,true]) := by symm; simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using moveCut ([]) (([false,true,false,true,true,true,true,true])) [false] true n
    _ = ([true,false]) ++ (rep [true,false] (n)) ++ ([true,false,true,true,true,true,true]) := by symm; simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using moveCut (([true])) (([true,false,true,true,true,true,true])) [true] false n
    _ = ([true,false,true]) ++ (rep [false,true] (n)) ++ ([false,true,true,true,true,true]) := by symm; simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using moveCut (([true,false])) (([false,true,true,true,true,true])) [false] true n
    _ = ([true,false,true,false]) ++ (rep [true,false] (n)) ++ ([true,true,true,true,true]) := by symm; simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using moveCut (([true,false,true])) (([true,true,true,true,true])) [true] false n

theorem canon (n : Nat) : run0 table (4+2*n) ⟨1,(rep [true,false] (n)) ++ ([true,false,true]),([true,true,true,true,true])⟩ = some ⟨1,[],([true,false,true,false]) ++ (rep [true,false] (n)) ++ ([true,true,true,true,true])⟩ := by
  simpa only [eq1r n] using epoch n

end MFinish


namespace MCarry

-- 1RB0RC_1RC0LE_0RD0RF_1LD0RA_1LB---_0RC1LE

def table : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 0,true => some (some ⟨false,true,2⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 1,true => some (some ⟨false,false,4⟩)
  | 2,false => some (some ⟨false,true,3⟩)
  | 2,true => some (some ⟨false,true,5⟩)
  | 3,false => some (some ⟨true,false,3⟩)
  | 3,true => some (some ⟨false,true,0⟩)
  | 4,false => some (some ⟨true,false,1⟩)
  | 5,false => some (some ⟨false,true,2⟩)
  | 5,true => some (some ⟨true,false,4⟩)
  | _,_ => none

theorem local0 (L R : List Bool) : run0 table 2 ⟨1,([true,false]) ++ (L),(R)⟩ = some ⟨1,(L),([true,false]) ++ (R)⟩ := by rfl

theorem phase0 (n : Nat) (R : List Bool) : run0 table (2*n) ⟨1,(rep [true,false] (n)) ++ ([true,false,false,false]) ++ (R),([true,true,true,true,true])⟩ = some ⟨1,([true,false,false,false]) ++ (R),(rep [true,false] (n)) ++ ([true,true,true,true,true])⟩ := by
  simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using sweepL table 1 [] [] [true,false] [true,false] 2 local0 n (([true,false,false,false]) ++ (R)) (([true,true,true,true,true]))

theorem phase1 (n : Nat) (R : List Bool) : run0 table 3 ⟨1,([true,false,false,false]) ++ (R),(rep [true,false] (n)) ++ ([true,true,true,true,true])⟩ = some ⟨2,([true,true,false]) ++ (R),([false]) ++ (rep [true,false] (n)) ++ ([true,true,true,true,true])⟩ := by rfl

theorem local2 (L R : List Bool) : run0 table 2 ⟨2,([true]) ++ (L),([false]) ++ ([true,false]) ++ (R)⟩ = some ⟨2,([true]) ++ ([false,false]) ++ (L),([false]) ++ (R)⟩ := by rfl

theorem phase2 (n : Nat) (R : List Bool) : run0 table (2*n) ⟨2,([true,true,false]) ++ (R),([false]) ++ (rep [true,false] (n)) ++ ([true,true,true,true,true])⟩ = some ⟨2,([true]) ++ (rep [false,false] (n)) ++ ([true,false]) ++ (R),([false,true,true,true,true,true])⟩ := by
  simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using sweepR table 2 [true] [false] [true,false] [false,false] 2 local2 n (([true,false]) ++ (R)) (([true,true,true,true,true]))

theorem phase3 (n : Nat) (R : List Bool) : run0 table 5 ⟨2,([true]) ++ (rep [false,false] (n)) ++ ([true,false]) ++ (R),([false,true,true,true,true,true])⟩ = some ⟨1,([false,false]) ++ (rep [false,false] (n)) ++ ([true,false]) ++ (R),([true,true,true,true,true])⟩ := by rfl

theorem finalL (n : Nat) (R : List Bool) : ([false,false]) ++ (rep [false,false] (n)) ++ ([true,false]) ++ (R) = (rep [false,false] (n)) ++ ([false,false,true,false]) ++ (R) := by
  calc
    _ = ([false]) ++ (rep [false,false] (n)) ++ ([false,true,false]) ++ (R) := by simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using moveCut (([false])) (([true,false]) ++ (R)) [false] false n
    _ = (rep [false,false] (n)) ++ ([false,false,true,false]) ++ (R) := by simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using moveCut ([]) (([false,true,false]) ++ (R)) [false] false n

theorem finalR (n : Nat) (R : List Bool) : ([true,true,true,true,true]) = ([true,true,true,true,true]) := by
  rfl

theorem epoch (n : Nat) (R : List Bool) : run0 table (8+4*n) ⟨1,(rep [true,false] (n)) ++ ([true,false,false,false]) ++ (R),([true,true,true,true,true])⟩ = some ⟨1,(rep [false,false] (n)) ++ ([false,false,true,false]) ++ (R),([true,true,true,true,true])⟩ := by
  have H := (join0 (join0 (join0 (phase0 n R) (phase1 n R)) (phase2 n R)) (phase3 n R))
  rw [finalL n R] at H
  rw [show 2*n+3+2*n+5=8+4*n by omega] at H
  exact H

theorem canon (n : Nat) (R : List Bool) : run0 table (8+4*n) ⟨1,(rep [true,false] (n)) ++ ([true,false,false,false]) ++ (R),([true,true,true,true,true])⟩ = some ⟨1,(rep [false,false] (n)) ++ ([false,false,true,false]) ++ (R),([true,true,true,true,true])⟩ := by
  exact epoch n R

end MCarry


abbrev table := MInit.table
abbrev A : List Bool := [true,false]
abbrev Z : List Bool := [false,false]
def Q (R : List Bool) : Z0 := ⟨1,(R),[true,true,true,true,true]⟩
def family (n : Nat) : Z0 := ⟨1,[],([true,false]) ++ (rep [true,false] (n)) ++ ([true,true,true,true,true])⟩
def carryCost (n : Nat) : Nat := 4+4*n

theorem carry (n : Nat) (R : List Bool) : run0 table (carryCost n) (Q (rep A n ++ Z ++ R)) = some (Q (rep Z n ++ A ++ R)) := by
  cases n with
  | zero => rfl
  | succ n =>
    have h := MCarry.canon n R
    rw [show MCarry.table = table from rfl] at h
    unfold carryCost
    rw [show 4+4*n.succ = 8+4*n by omega]
    rw [rep_succ_snoc A n,rep_succ_snoc Z n]
    simpa only [table,Q,A,Z,List.append_assoc,List.nil_append,List.append_nil,List.cons_append] using h

theorem entry : run0 table 27 ⟨0,[],[]⟩ = some (family 0) := by rfl


def cost (n : Nat) : Nat := (6+2*n) + fillCost carryCost (n+1) + (4+2*n)

theorem growth (n : Nat) : run0 table (cost n) (family n) = some (family (n+1)) := by
  have h1 := MInit.canon n
  have h2 := fill table Q A Z carryCost carry (n+1) [true]
  have h3 := MFinish.canon n
  rw [rep_add Z n 1,rep_add A n 1] at h2
  simp only [Q,A,Z,rep,List.append_assoc,List.nil_append,List.append_nil,List.cons_append] at h2
  have h := join0 (join0 h1 h2) h3
  simpa only [cost,family,rep,rep_succ_snoc,List.append_assoc,List.nil_append,List.append_nil,List.cons_append] using h


theorem never (m : Machine) (hm : compatible table m) : NeverHalts m :=
  never_of_growth table family 27 cost entry (by intro n; unfold cost; omega) growth m hm

#print axioms growth
#print axioms never
end M508
namespace M270

namespace MInit

-- 1RB0RC_1RC0LF_0RD0RE_1LD0RA_0RC1LF_1LB---

def table : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 0,true => some (some ⟨false,true,2⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 1,true => some (some ⟨false,false,5⟩)
  | 2,false => some (some ⟨false,true,3⟩)
  | 2,true => some (some ⟨false,true,4⟩)
  | 3,false => some (some ⟨true,false,3⟩)
  | 3,true => some (some ⟨false,true,0⟩)
  | 4,false => some (some ⟨false,true,2⟩)
  | 4,true => some (some ⟨true,false,5⟩)
  | 5,false => some (some ⟨true,false,1⟩)
  | _,_ => none

theorem phase0 (n : Nat) : run0 table 1 ⟨1,[],([true,false]) ++ (rep [true,false] (n)) ++ ([true,true,true,true,true])⟩ = some ⟨2,([true,true]),([false]) ++ (rep [true,false] (n)) ++ ([true,true,true,true,true])⟩ := by rfl

theorem local1 (L R : List Bool) : run0 table 2 ⟨2,([true]) ++ (L),([false]) ++ ([true,false]) ++ (R)⟩ = some ⟨2,([true]) ++ ([false,false]) ++ (L),([false]) ++ (R)⟩ := by rfl

theorem phase1 (n : Nat) : run0 table (2*n) ⟨2,([true,true]),([false]) ++ (rep [true,false] (n)) ++ ([true,true,true,true,true])⟩ = some ⟨2,([true]) ++ (rep [false,false] (n)) ++ ([true]),([false,true,true,true,true,true])⟩ := by
  simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using sweepR table 2 [true] [false] [true,false] [false,false] 2 local1 n (([true])) (([true,true,true,true,true]))

theorem phase2 (n : Nat) : run0 table 5 ⟨2,([true]) ++ (rep [false,false] (n)) ++ ([true]),([false,true,true,true,true,true])⟩ = some ⟨1,([false,false]) ++ (rep [false,false] (n)) ++ ([true]),([true,true,true,true,true])⟩ := by rfl

theorem finalL (n : Nat) : ([false,false]) ++ (rep [false,false] (n)) ++ ([true]) = (rep [false,false] (n)) ++ ([false,false,true]) := by
  calc
    _ = ([false]) ++ (rep [false,false] (n)) ++ ([false,true]) := by simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using moveCut (([false])) (([true])) [false] false n
    _ = (rep [false,false] (n)) ++ ([false,false,true]) := by simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using moveCut ([]) (([false,true])) [false] false n

theorem finalR (n : Nat) : ([true,true,true,true,true]) = ([true,true,true,true,true]) := by
  rfl

theorem epoch (n : Nat) : run0 table (6+2*n) ⟨1,[],([true,false]) ++ (rep [true,false] (n)) ++ ([true,true,true,true,true])⟩ = some ⟨1,(rep [false,false] (n)) ++ ([false,false,true]),([true,true,true,true,true])⟩ := by
  have H := (join0 (join0 (phase0 n) (phase1 n)) (phase2 n))
  rw [finalL n] at H
  rw [show 1+2*n+5=6+2*n by omega] at H
  exact H

theorem canon (n : Nat) : run0 table (6+2*n) ⟨1,[],([true,false]) ++ (rep [true,false] (n)) ++ ([true,true,true,true,true])⟩ = some ⟨1,(rep [false,false] (n)) ++ ([false,false,true]),([true,true,true,true,true])⟩ := by
  exact epoch n

end MInit


namespace MFinish

-- 1RB0RC_1RC0LF_0RD0RE_1LD0RA_0RC1LF_1LB---

def table : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 0,true => some (some ⟨false,true,2⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 1,true => some (some ⟨false,false,5⟩)
  | 2,false => some (some ⟨false,true,3⟩)
  | 2,true => some (some ⟨false,true,4⟩)
  | 3,false => some (some ⟨true,false,3⟩)
  | 3,true => some (some ⟨false,true,0⟩)
  | 4,false => some (some ⟨false,true,2⟩)
  | 4,true => some (some ⟨true,false,5⟩)
  | 5,false => some (some ⟨true,false,1⟩)
  | _,_ => none

theorem local0 (L R : List Bool) : run0 table 2 ⟨1,([true,false]) ++ (L),(R)⟩ = some ⟨1,(L),([true,false]) ++ (R)⟩ := by rfl

theorem phase0 (n : Nat) : run0 table (2*n) ⟨1,(rep [true,false] (n)) ++ ([true,false,true]),([true,true,true,true,true])⟩ = some ⟨1,([true,false,true]),(rep [true,false] (n)) ++ ([true,true,true,true,true])⟩ := by
  simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using sweepL table 1 [] [] [true,false] [true,false] 2 local0 n (([true,false,true])) (([true,true,true,true,true]))

theorem phase1 (n : Nat) : run0 table 4 ⟨1,([true,false,true]),(rep [true,false] (n)) ++ ([true,true,true,true,true])⟩ = some ⟨1,[],([true,false,true,false]) ++ (rep [true,false] (n)) ++ ([true,true,true,true,true])⟩ := by rfl

theorem finalL (n : Nat) : ([] : List Bool) = [] := by
  rfl

theorem finalR (n : Nat) : ([true,false,true,false]) ++ (rep [true,false] (n)) ++ ([true,true,true,true,true]) = (rep [true,false] (n)) ++ ([true,false,true,false,true,true,true,true,true]) := by
  calc
    _ = ([true,false,true]) ++ (rep [false,true] (n)) ++ ([false,true,true,true,true,true]) := by simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using moveCut (([true,false,true])) (([true,true,true,true,true])) [true] false n
    _ = ([true,false]) ++ (rep [true,false] (n)) ++ ([true,false,true,true,true,true,true]) := by simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using moveCut (([true,false])) (([false,true,true,true,true,true])) [false] true n
    _ = ([true]) ++ (rep [false,true] (n)) ++ ([false,true,false,true,true,true,true,true]) := by simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using moveCut (([true])) (([true,false,true,true,true,true,true])) [true] false n
    _ = (rep [true,false] (n)) ++ ([true,false,true,false,true,true,true,true,true]) := by simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using moveCut ([]) (([false,true,false,true,true,true,true,true])) [false] true n

theorem epoch (n : Nat) : run0 table (4+2*n) ⟨1,(rep [true,false] (n)) ++ ([true,false,true]),([true,true,true,true,true])⟩ = some ⟨1,[],(rep [true,false] (n)) ++ ([true,false,true,false,true,true,true,true,true])⟩ := by
  have H := (join0 (phase0 n) (phase1 n))
  rw [finalR n] at H
  rw [show 2*n+4=4+2*n by omega] at H
  exact H

theorem eq1r (n : Nat) : (rep [true,false] (n)) ++ ([true,false,true,false,true,true,true,true,true]) = ([true,false,true,false]) ++ (rep [true,false] (n)) ++ ([true,true,true,true,true]) := by
  calc
    _ = ([true]) ++ (rep [false,true] (n)) ++ ([false,true,false,true,true,true,true,true]) := by symm; simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using moveCut ([]) (([false,true,false,true,true,true,true,true])) [false] true n
    _ = ([true,false]) ++ (rep [true,false] (n)) ++ ([true,false,true,true,true,true,true]) := by symm; simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using moveCut (([true])) (([true,false,true,true,true,true,true])) [true] false n
    _ = ([true,false,true]) ++ (rep [false,true] (n)) ++ ([false,true,true,true,true,true]) := by symm; simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using moveCut (([true,false])) (([false,true,true,true,true,true])) [false] true n
    _ = ([true,false,true,false]) ++ (rep [true,false] (n)) ++ ([true,true,true,true,true]) := by symm; simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using moveCut (([true,false,true])) (([true,true,true,true,true])) [true] false n

theorem canon (n : Nat) : run0 table (4+2*n) ⟨1,(rep [true,false] (n)) ++ ([true,false,true]),([true,true,true,true,true])⟩ = some ⟨1,[],([true,false,true,false]) ++ (rep [true,false] (n)) ++ ([true,true,true,true,true])⟩ := by
  simpa only [eq1r n] using epoch n

end MFinish


namespace MCarry

-- 1RB0RC_1RC0LF_0RD0RE_1LD0RA_0RC1LF_1LB---

def table : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 0,true => some (some ⟨false,true,2⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 1,true => some (some ⟨false,false,5⟩)
  | 2,false => some (some ⟨false,true,3⟩)
  | 2,true => some (some ⟨false,true,4⟩)
  | 3,false => some (some ⟨true,false,3⟩)
  | 3,true => some (some ⟨false,true,0⟩)
  | 4,false => some (some ⟨false,true,2⟩)
  | 4,true => some (some ⟨true,false,5⟩)
  | 5,false => some (some ⟨true,false,1⟩)
  | _,_ => none

theorem local0 (L R : List Bool) : run0 table 2 ⟨1,([true,false]) ++ (L),(R)⟩ = some ⟨1,(L),([true,false]) ++ (R)⟩ := by rfl

theorem phase0 (n : Nat) (R : List Bool) : run0 table (2*n) ⟨1,(rep [true,false] (n)) ++ ([true,false,false,false]) ++ (R),([true,true,true,true,true])⟩ = some ⟨1,([true,false,false,false]) ++ (R),(rep [true,false] (n)) ++ ([true,true,true,true,true])⟩ := by
  simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using sweepL table 1 [] [] [true,false] [true,false] 2 local0 n (([true,false,false,false]) ++ (R)) (([true,true,true,true,true]))

theorem phase1 (n : Nat) (R : List Bool) : run0 table 3 ⟨1,([true,false,false,false]) ++ (R),(rep [true,false] (n)) ++ ([true,true,true,true,true])⟩ = some ⟨2,([true,true,false]) ++ (R),([false]) ++ (rep [true,false] (n)) ++ ([true,true,true,true,true])⟩ := by rfl

theorem local2 (L R : List Bool) : run0 table 2 ⟨2,([true]) ++ (L),([false]) ++ ([true,false]) ++ (R)⟩ = some ⟨2,([true]) ++ ([false,false]) ++ (L),([false]) ++ (R)⟩ := by rfl

theorem phase2 (n : Nat) (R : List Bool) : run0 table (2*n) ⟨2,([true,true,false]) ++ (R),([false]) ++ (rep [true,false] (n)) ++ ([true,true,true,true,true])⟩ = some ⟨2,([true]) ++ (rep [false,false] (n)) ++ ([true,false]) ++ (R),([false,true,true,true,true,true])⟩ := by
  simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using sweepR table 2 [true] [false] [true,false] [false,false] 2 local2 n (([true,false]) ++ (R)) (([true,true,true,true,true]))

theorem phase3 (n : Nat) (R : List Bool) : run0 table 5 ⟨2,([true]) ++ (rep [false,false] (n)) ++ ([true,false]) ++ (R),([false,true,true,true,true,true])⟩ = some ⟨1,([false,false]) ++ (rep [false,false] (n)) ++ ([true,false]) ++ (R),([true,true,true,true,true])⟩ := by rfl

theorem finalL (n : Nat) (R : List Bool) : ([false,false]) ++ (rep [false,false] (n)) ++ ([true,false]) ++ (R) = (rep [false,false] (n)) ++ ([false,false,true,false]) ++ (R) := by
  calc
    _ = ([false]) ++ (rep [false,false] (n)) ++ ([false,true,false]) ++ (R) := by simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using moveCut (([false])) (([true,false]) ++ (R)) [false] false n
    _ = (rep [false,false] (n)) ++ ([false,false,true,false]) ++ (R) := by simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using moveCut ([]) (([false,true,false]) ++ (R)) [false] false n

theorem finalR (n : Nat) (R : List Bool) : ([true,true,true,true,true]) = ([true,true,true,true,true]) := by
  rfl

theorem epoch (n : Nat) (R : List Bool) : run0 table (8+4*n) ⟨1,(rep [true,false] (n)) ++ ([true,false,false,false]) ++ (R),([true,true,true,true,true])⟩ = some ⟨1,(rep [false,false] (n)) ++ ([false,false,true,false]) ++ (R),([true,true,true,true,true])⟩ := by
  have H := (join0 (join0 (join0 (phase0 n R) (phase1 n R)) (phase2 n R)) (phase3 n R))
  rw [finalL n R] at H
  rw [show 2*n+3+2*n+5=8+4*n by omega] at H
  exact H

theorem canon (n : Nat) (R : List Bool) : run0 table (8+4*n) ⟨1,(rep [true,false] (n)) ++ ([true,false,false,false]) ++ (R),([true,true,true,true,true])⟩ = some ⟨1,(rep [false,false] (n)) ++ ([false,false,true,false]) ++ (R),([true,true,true,true,true])⟩ := by
  exact epoch n R

end MCarry


abbrev table := MInit.table
abbrev A : List Bool := [true,false]
abbrev Z : List Bool := [false,false]
def Q (R : List Bool) : Z0 := ⟨1,(R),[true,true,true,true,true]⟩
def family (n : Nat) : Z0 := ⟨1,[],([true,false]) ++ (rep [true,false] (n)) ++ ([true,true,true,true,true])⟩
def carryCost (n : Nat) : Nat := 4+4*n

theorem carry (n : Nat) (R : List Bool) : run0 table (carryCost n) (Q (rep A n ++ Z ++ R)) = some (Q (rep Z n ++ A ++ R)) := by
  cases n with
  | zero => rfl
  | succ n =>
    have h := MCarry.canon n R
    rw [show MCarry.table = table from rfl] at h
    unfold carryCost
    rw [show 4+4*n.succ = 8+4*n by omega]
    rw [rep_succ_snoc A n,rep_succ_snoc Z n]
    simpa only [table,Q,A,Z,List.append_assoc,List.nil_append,List.append_nil,List.cons_append] using h

theorem entry : run0 table 27 ⟨0,[],[]⟩ = some (family 0) := by rfl


def cost (n : Nat) : Nat := (6+2*n) + fillCost carryCost (n+1) + (4+2*n)

theorem growth (n : Nat) : run0 table (cost n) (family n) = some (family (n+1)) := by
  have h1 := MInit.canon n
  have h2 := fill table Q A Z carryCost carry (n+1) [true]
  have h3 := MFinish.canon n
  rw [rep_add Z n 1,rep_add A n 1] at h2
  simp only [Q,A,Z,rep,List.append_assoc,List.nil_append,List.append_nil,List.cons_append] at h2
  have h := join0 (join0 h1 h2) h3
  simpa only [cost,family,rep,rep_succ_snoc,List.append_assoc,List.nil_append,List.append_nil,List.cons_append] using h


theorem never (m : Machine) (hm : compatible table m) : NeverHalts m :=
  never_of_growth table family 27 cost entry (by intro n; unfold cost; omega) growth m hm

#print axioms growth
#print axioms never
end M270

end BB6.Agent11Raw39RCCounter508
