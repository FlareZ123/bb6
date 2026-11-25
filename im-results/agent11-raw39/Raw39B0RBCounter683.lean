import Raw39CounterCarry
open BB6Coverage BB6Coverage.Agent31Pump BB6.Agent11CounterCarry
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedVariables false
namespace BB6.Agent11Raw39B0RBCounter683
namespace M683

namespace MInit

-- 1RB0RB_1RC0RE_0RD---_1LD0RA_1LF0RB_0LF1RB

def table : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 0,true => some (some ⟨false,true,1⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 1,true => some (some ⟨false,true,4⟩)
  | 2,false => some (some ⟨false,true,3⟩)
  | 3,false => some (some ⟨true,false,3⟩)
  | 3,true => some (some ⟨false,true,0⟩)
  | 4,false => some (some ⟨true,false,5⟩)
  | 4,true => some (some ⟨false,true,1⟩)
  | 5,false => some (some ⟨false,false,5⟩)
  | 5,true => some (some ⟨true,true,1⟩)
  | _,_ => none

theorem phase0 (n : Nat) : run0 table 8 ⟨1,([false]) ++ (rep [false,false,false,false] (n)) ++ ([true]),[]⟩ = some ⟨5,([false,false,false]) ++ (rep [false,false,false,false] (n)) ++ ([true]),([true])⟩ := by rfl

theorem local1 (L R : List Bool) : run0 table 4 ⟨5,([false,false,false]) ++ ([false,false,false,false]) ++ (L),(R)⟩ = some ⟨5,([false,false,false]) ++ (L),([false,false,false,false]) ++ (R)⟩ := by rfl

theorem phase1 (n : Nat) : run0 table (4*n) ⟨5,([false,false,false]) ++ (rep [false,false,false,false] (n)) ++ ([true]),([true])⟩ = some ⟨5,([false,false,false,true]),(rep [false,false,false,false] (n)) ++ ([true])⟩ := by
  simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using sweepL table 5 [false,false,false] [] [false,false,false,false] [false,false,false,false] 4 local1 n (([true])) (([true]))

theorem finalL (n : Nat) : ([false,false,false,true]) = ([false,false,false,true]) := by
  rfl

theorem finalR (n : Nat) : (rep [false,false,false,false] (n)) ++ ([true]) = (rep [false,false,false,false] (n)) ++ ([true]) := by
  rfl

theorem epoch (n : Nat) : run0 table (8+4*n) ⟨1,([false]) ++ (rep [false,false,false,false] (n)) ++ ([true]),[]⟩ = some ⟨5,([false,false,false,true]),(rep [false,false,false,false] (n)) ++ ([true])⟩ := by
  have H := (join0 (phase0 n) (phase1 n))
  rw [show 8+4*n=8+4*n by omega] at H
  exact H

theorem canon (n : Nat) : run0 table (8+4*n) ⟨1,([false]) ++ (rep [false,false,false,false] (n)) ++ ([true]),[]⟩ = some ⟨5,([false,false,false,true]),(rep [false,false,false,false] (n)) ++ ([true])⟩ := by
  exact epoch n

end MInit


namespace MFinish

-- 1RB0RB_1RC0RE_0RD---_1LD0RA_1LF0RB_0LF1RB

def table : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 0,true => some (some ⟨false,true,1⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 1,true => some (some ⟨false,true,4⟩)
  | 2,false => some (some ⟨false,true,3⟩)
  | 3,false => some (some ⟨true,false,3⟩)
  | 3,true => some (some ⟨false,true,0⟩)
  | 4,false => some (some ⟨true,false,5⟩)
  | 4,true => some (some ⟨false,true,1⟩)
  | 5,false => some (some ⟨false,false,5⟩)
  | 5,true => some (some ⟨true,true,1⟩)
  | _,_ => none

theorem phase0 (n : Nat) : run0 table 4 ⟨5,([false,false,false,true]),(rep [true,false,false,false] (n)) ++ ([true])⟩ = some ⟨1,([false,true]),([false,false]) ++ (rep [true,false,false,false] (n)) ++ ([true])⟩ := by rfl

theorem local1 (L R : List Bool) : run0 table 8 ⟨1,([false]) ++ (L),([false,false]) ++ ([true,false,false,false]) ++ (R)⟩ = some ⟨1,([false]) ++ ([false,false,false,false]) ++ (L),([false,false]) ++ (R)⟩ := by rfl

theorem phase1 (n : Nat) : run0 table (8*n) ⟨1,([false,true]),([false,false]) ++ (rep [true,false,false,false] (n)) ++ ([true])⟩ = some ⟨1,([false]) ++ (rep [false,false,false,false] (n)) ++ ([true]),([false,false,true])⟩ := by
  simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using sweepR table 1 [false] [false,false] [true,false,false,false] [false,false,false,false] 8 local1 n (([true])) (([true]))

theorem phase2 (n : Nat) : run0 table 8 ⟨1,([false]) ++ (rep [false,false,false,false] (n)) ++ ([true]),([false,false,true])⟩ = some ⟨1,([false,false,false,false,false]) ++ (rep [false,false,false,false] (n)) ++ ([true]),[]⟩ := by rfl

theorem finalL (n : Nat) : ([false,false,false,false,false]) ++ (rep [false,false,false,false] (n)) ++ ([true]) = ([false]) ++ (rep [false,false,false,false] (n)) ++ ([false,false,false,false,true]) := by
  calc
    _ = ([false,false,false,false]) ++ (rep [false,false,false,false] (n)) ++ ([false,true]) := by simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using moveCut (([false,false,false,false])) (([true])) [false,false,false] false n
    _ = ([false,false,false]) ++ (rep [false,false,false,false] (n)) ++ ([false,false,true]) := by simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using moveCut (([false,false,false])) (([false,true])) [false,false,false] false n
    _ = ([false,false]) ++ (rep [false,false,false,false] (n)) ++ ([false,false,false,true]) := by simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using moveCut (([false,false])) (([false,false,true])) [false,false,false] false n
    _ = ([false]) ++ (rep [false,false,false,false] (n)) ++ ([false,false,false,false,true]) := by simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using moveCut (([false])) (([false,false,false,true])) [false,false,false] false n

theorem finalR (n : Nat) : ([] : List Bool) = [] := by
  rfl

theorem epoch (n : Nat) : run0 table (12+8*n) ⟨5,([false,false,false,true]),(rep [true,false,false,false] (n)) ++ ([true])⟩ = some ⟨1,([false]) ++ (rep [false,false,false,false] (n)) ++ ([false,false,false,false,true]),[]⟩ := by
  have H := (join0 (join0 (phase0 n) (phase1 n)) (phase2 n))
  rw [finalL n] at H
  rw [show 4+8*n+8=12+8*n by omega] at H
  exact H

theorem eq1l (n : Nat) : ([false]) ++ (rep [false,false,false,false] (n)) ++ ([false,false,false,false,true]) = ([false,false,false,false,false]) ++ (rep [false,false,false,false] (n)) ++ ([true]) := by
  calc
    _ = ([false,false]) ++ (rep [false,false,false,false] (n)) ++ ([false,false,false,true]) := by symm; simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using moveCut (([false])) (([false,false,false,true])) [false,false,false] false n
    _ = ([false,false,false]) ++ (rep [false,false,false,false] (n)) ++ ([false,false,true]) := by symm; simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using moveCut (([false,false])) (([false,false,true])) [false,false,false] false n
    _ = ([false,false,false,false]) ++ (rep [false,false,false,false] (n)) ++ ([false,true]) := by symm; simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using moveCut (([false,false,false])) (([false,true])) [false,false,false] false n
    _ = ([false,false,false,false,false]) ++ (rep [false,false,false,false] (n)) ++ ([true]) := by symm; simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using moveCut (([false,false,false,false])) (([true])) [false,false,false] false n

theorem canon (n : Nat) : run0 table (12+8*n) ⟨5,([false,false,false,true]),(rep [true,false,false,false] (n)) ++ ([true])⟩ = some ⟨1,([false,false,false,false,false]) ++ (rep [false,false,false,false] (n)) ++ ([true]),[]⟩ := by
  simpa only [eq1l n] using epoch n

end MFinish


namespace MCarry

-- 1RB0RB_1RC0RE_0RD---_1LD0RA_1LF0RB_0LF1RB

def table : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 0,true => some (some ⟨false,true,1⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 1,true => some (some ⟨false,true,4⟩)
  | 2,false => some (some ⟨false,true,3⟩)
  | 3,false => some (some ⟨true,false,3⟩)
  | 3,true => some (some ⟨false,true,0⟩)
  | 4,false => some (some ⟨true,false,5⟩)
  | 4,true => some (some ⟨false,true,1⟩)
  | 5,false => some (some ⟨false,false,5⟩)
  | 5,true => some (some ⟨true,true,1⟩)
  | _,_ => none

theorem phase0 (n : Nat) (R : List Bool) : run0 table 4 ⟨5,([false,false,false,true]),(rep [true,false,false,false] (n)) ++ ([true,false,false,false,false,false,false,false]) ++ (R)⟩ = some ⟨1,([false,true]),([false,false]) ++ (rep [true,false,false,false] (n)) ++ ([true,false,false,false,false,false,false,false]) ++ (R)⟩ := by rfl

theorem local1 (L R : List Bool) : run0 table 8 ⟨1,([false]) ++ (L),([false,false]) ++ ([true,false,false,false]) ++ (R)⟩ = some ⟨1,([false]) ++ ([false,false,false,false]) ++ (L),([false,false]) ++ (R)⟩ := by rfl

theorem phase1 (n : Nat) (R : List Bool) : run0 table (8*n) ⟨1,([false,true]),([false,false]) ++ (rep [true,false,false,false] (n)) ++ ([true,false,false,false,false,false,false,false]) ++ (R)⟩ = some ⟨1,([false]) ++ (rep [false,false,false,false] (n)) ++ ([true]),([false,false,true,false,false,false,false,false,false,false]) ++ (R)⟩ := by
  simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using sweepR table 1 [false] [false,false] [true,false,false,false] [false,false,false,false] 8 local1 n (([true])) (([true,false,false,false,false,false,false,false]) ++ (R))

theorem phase2 (n : Nat) (R : List Bool) : run0 table 16 ⟨1,([false]) ++ (rep [false,false,false,false] (n)) ++ ([true]),([false,false,true,false,false,false,false,false,false,false]) ++ (R)⟩ = some ⟨5,([false,false,false,false,false,false,false]) ++ (rep [false,false,false,false] (n)) ++ ([true]),([true,false,false,false]) ++ (R)⟩ := by rfl

theorem local3 (L R : List Bool) : run0 table 4 ⟨5,([false,false,false,false,false,false,false]) ++ ([false,false,false,false]) ++ (L),(R)⟩ = some ⟨5,([false,false,false,false,false,false,false]) ++ (L),([false,false,false,false]) ++ (R)⟩ := by rfl

theorem phase3 (n : Nat) (R : List Bool) : run0 table (4*n) ⟨5,([false,false,false,false,false,false,false]) ++ (rep [false,false,false,false] (n)) ++ ([true]),([true,false,false,false]) ++ (R)⟩ = some ⟨5,([false,false,false,false,false,false,false,true]),(rep [false,false,false,false] (n)) ++ ([true,false,false,false]) ++ (R)⟩ := by
  simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using sweepL table 5 [false,false,false,false,false,false,false] [] [false,false,false,false] [false,false,false,false] 4 local3 n (([true])) (([true,false,false,false]) ++ (R))

theorem phase4 (n : Nat) (R : List Bool) : run0 table 4 ⟨5,([false,false,false,false,false,false,false,true]),(rep [false,false,false,false] (n)) ++ ([true,false,false,false]) ++ (R)⟩ = some ⟨5,([false,false,false,true]),([false,false,false,false]) ++ (rep [false,false,false,false] (n)) ++ ([true,false,false,false]) ++ (R)⟩ := by rfl

theorem finalL (n : Nat) (R : List Bool) : ([false,false,false,true]) = ([false,false,false,true]) := by
  rfl

theorem finalR (n : Nat) (R : List Bool) : ([false,false,false,false]) ++ (rep [false,false,false,false] (n)) ++ ([true,false,false,false]) ++ (R) = (rep [false,false,false,false] (n)) ++ ([false,false,false,false,true,false,false,false]) ++ (R) := by
  calc
    _ = ([false,false,false]) ++ (rep [false,false,false,false] (n)) ++ ([false,true,false,false,false]) ++ (R) := by simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using moveCut (([false,false,false])) (([true,false,false,false]) ++ (R)) [false,false,false] false n
    _ = ([false,false]) ++ (rep [false,false,false,false] (n)) ++ ([false,false,true,false,false,false]) ++ (R) := by simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using moveCut (([false,false])) (([false,true,false,false,false]) ++ (R)) [false,false,false] false n
    _ = ([false]) ++ (rep [false,false,false,false] (n)) ++ ([false,false,false,true,false,false,false]) ++ (R) := by simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using moveCut (([false])) (([false,false,true,false,false,false]) ++ (R)) [false,false,false] false n
    _ = (rep [false,false,false,false] (n)) ++ ([false,false,false,false,true,false,false,false]) ++ (R) := by simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using moveCut ([]) (([false,false,false,true,false,false,false]) ++ (R)) [false,false,false] false n

theorem epoch (n : Nat) (R : List Bool) : run0 table (24+12*n) ⟨5,([false,false,false,true]),(rep [true,false,false,false] (n)) ++ ([true,false,false,false,false,false,false,false]) ++ (R)⟩ = some ⟨5,([false,false,false,true]),(rep [false,false,false,false] (n)) ++ ([false,false,false,false,true,false,false,false]) ++ (R)⟩ := by
  have H := (join0 (join0 (join0 (join0 (phase0 n R) (phase1 n R)) (phase2 n R)) (phase3 n R)) (phase4 n R))
  rw [finalR n R] at H
  rw [show 4+8*n+16+4*n+4=24+12*n by omega] at H
  exact H

theorem canon (n : Nat) (R : List Bool) : run0 table (24+12*n) ⟨5,([false,false,false,true]),(rep [true,false,false,false] (n)) ++ ([true,false,false,false,false,false,false,false]) ++ (R)⟩ = some ⟨5,([false,false,false,true]),(rep [false,false,false,false] (n)) ++ ([false,false,false,false,true,false,false,false]) ++ (R)⟩ := by
  exact epoch n R

end MCarry


abbrev table := MInit.table
abbrev A : List Bool := [true,false,false,false]
abbrev Z : List Bool := [false,false,false,false]
def Q (R : List Bool) : Z0 := ⟨5,[false,false,false,true],(R)⟩
def family (n : Nat) : Z0 := ⟨1,([false]) ++ (rep [false,false,false,false] (n)) ++ ([true]),[]⟩
def carryCost (n : Nat) : Nat := 12+12*n

theorem carry (n : Nat) (R : List Bool) : run0 table (carryCost n) (Q (rep A n ++ Z ++ R)) = some (Q (rep Z n ++ A ++ R)) := by
  cases n with
  | zero => rfl
  | succ n =>
    have h := MCarry.canon n R
    rw [show MCarry.table = table from rfl] at h
    unfold carryCost
    rw [show 12+12*n.succ = 24+12*n by omega]
    rw [rep_succ_snoc A n,rep_succ_snoc Z n]
    simpa only [table,Q,A,Z,List.append_assoc,List.nil_append,List.append_nil,List.cons_append] using h

theorem entry : run0 table 1 ⟨0,[],[]⟩ = some (family 0) := by rfl


def cost (n : Nat) : Nat := (8+4*n) + fillCost carryCost (n+0) + (12+8*n)
theorem growth (n : Nat) : run0 table (cost n) (family n) = some (family (n+1)) := by
  have h1 := MInit.canon n
  have h2 := fill table Q A Z carryCost carry (n+0) [true]
  have h3 := MFinish.canon n
  rw [rep_add Z n 0,rep_add A n 0] at h2
  simp only [Q,A,Z,rep,List.append_assoc,List.nil_append,List.append_nil,List.cons_append] at h2
  have h := join0 (join0 h1 h2) h3
  simpa only [cost,family,rep,rep_succ_snoc,List.append_assoc,List.nil_append,List.append_nil,List.cons_append] using h

theorem never (m : Machine) (hm : compatible table m) : NeverHalts m :=
  never_of_growth table family 1 cost entry (by intro n; unfold cost; omega) growth m hm

#print axioms growth
#print axioms never
end M683

end BB6.Agent11Raw39B0RBCounter683
