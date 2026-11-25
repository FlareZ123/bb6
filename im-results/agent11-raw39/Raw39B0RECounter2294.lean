import Raw39CounterCarry
open BB6Coverage BB6Coverage.Agent31Pump BB6.Agent11CounterCarry
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedVariables false
namespace BB6.Agent11Raw39B0RECounter2294
namespace M2294

namespace MInit

-- 1RB0RE_1RC---_0RD0LD_1LD0RA_1LF1RD_0LF1LB

def table : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 0,true => some (some ⟨false,true,4⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 2,false => some (some ⟨false,true,3⟩)
  | 2,true => some (some ⟨false,false,3⟩)
  | 3,false => some (some ⟨true,false,3⟩)
  | 3,true => some (some ⟨false,true,0⟩)
  | 4,false => some (some ⟨true,false,5⟩)
  | 4,true => some (some ⟨true,true,3⟩)
  | 5,false => some (some ⟨false,false,5⟩)
  | 5,true => some (some ⟨true,false,1⟩)
  | _,_ => none

theorem phase0 (n : Nat) : run0 table 4 ⟨3,([false,true,false,false,false,false]) ++ (rep [false,false] (n)) ++ ([true,false]),[]⟩ = some ⟨5,([false,false,false,false,false,false]) ++ (rep [false,false] (n)) ++ ([true,false]),([true])⟩ := by rfl

theorem local1 (L R : List Bool) : run0 table 2 ⟨5,([false,false,false,false,false,false]) ++ ([false,false]) ++ (L),(R)⟩ = some ⟨5,([false,false,false,false,false,false]) ++ (L),([false,false]) ++ (R)⟩ := by rfl

theorem phase1 (n : Nat) : run0 table (2*n) ⟨5,([false,false,false,false,false,false]) ++ (rep [false,false] (n)) ++ ([true,false]),([true])⟩ = some ⟨5,([false,false,false,false,false,false,true,false]),(rep [false,false] (n)) ++ ([true])⟩ := by
  simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using sweepL table 5 [false,false,false,false,false,false] [] [false,false] [false,false] 2 local1 n (([true,false])) (([true]))

theorem finalL (n : Nat) : ([false,false,false,false,false,false,true,false]) = ([false,false,false,false,false,false,true,false]) := by
  rfl

theorem finalR (n : Nat) : (rep [false,false] (n)) ++ ([true]) = (rep [false,false] (n)) ++ ([true]) := by
  rfl

theorem epoch (n : Nat) : run0 table (4+2*n) ⟨3,([false,true,false,false,false,false]) ++ (rep [false,false] (n)) ++ ([true,false]),[]⟩ = some ⟨5,([false,false,false,false,false,false,true,false]),(rep [false,false] (n)) ++ ([true])⟩ := by
  have H := (join0 (phase0 n) (phase1 n))
  rw [show 4+2*n=4+2*n by omega] at H
  exact H

theorem canon (n : Nat) : run0 table (4+2*n) ⟨3,([false,true,false,false,false,false]) ++ (rep [false,false] (n)) ++ ([true,false]),[]⟩ = some ⟨5,([false,false,false,false,false,false,true,false]),(rep [false,false] (n)) ++ ([true])⟩ := by
  exact epoch n

end MInit


namespace MFinish

-- 1RB0RE_1RC---_0RD0LD_1LD0RA_1LF1RD_0LF1LB

def table : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 0,true => some (some ⟨false,true,4⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 2,false => some (some ⟨false,true,3⟩)
  | 2,true => some (some ⟨false,false,3⟩)
  | 3,false => some (some ⟨true,false,3⟩)
  | 3,true => some (some ⟨false,true,0⟩)
  | 4,false => some (some ⟨true,false,5⟩)
  | 4,true => some (some ⟨true,true,3⟩)
  | 5,false => some (some ⟨false,false,5⟩)
  | 5,true => some (some ⟨true,false,1⟩)
  | _,_ => none

theorem phase0 (n : Nat) : run0 table 34 ⟨5,([false,false,false,false,false,false,true,false]),(rep [true,false] (n)) ++ ([true])⟩ = some ⟨3,([false,true,true,false]),([true,false,true,false]) ++ (rep [true,false] (n)) ++ ([true])⟩ := by rfl

theorem local1 (L R : List Bool) : run0 table 4 ⟨3,([false,true]) ++ (L),([true,false,true,false]) ++ ([true,false]) ++ (R)⟩ = some ⟨3,([false,true]) ++ ([false,false]) ++ (L),([true,false,true,false]) ++ (R)⟩ := by rfl

theorem phase1 (n : Nat) : run0 table (4*n) ⟨3,([false,true,true,false]),([true,false,true,false]) ++ (rep [true,false] (n)) ++ ([true])⟩ = some ⟨3,([false,true]) ++ (rep [false,false] (n)) ++ ([true,false]),([true,false,true,false,true])⟩ := by
  simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using sweepR table 3 [false,true] [true,false,true,false] [true,false] [false,false] 4 local1 n (([true,false])) (([true]))

theorem phase2 (n : Nat) : run0 table 12 ⟨3,([false,true]) ++ (rep [false,false] (n)) ++ ([true,false]),([true,false,true,false,true])⟩ = some ⟨3,([false,true,false,false,false,false,false,false]) ++ (rep [false,false] (n)) ++ ([true,false]),[]⟩ := by rfl

theorem finalL (n : Nat) : ([false,true,false,false,false,false,false,false]) ++ (rep [false,false] (n)) ++ ([true,false]) = ([false,true,false,false,false,false]) ++ (rep [false,false] (n)) ++ ([false,false,true,false]) := by
  calc
    _ = ([false,true,false,false,false,false,false]) ++ (rep [false,false] (n)) ++ ([false,true,false]) := by simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using moveCut (([false,true,false,false,false,false,false])) (([true,false])) [false] false n
    _ = ([false,true,false,false,false,false]) ++ (rep [false,false] (n)) ++ ([false,false,true,false]) := by simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using moveCut (([false,true,false,false,false,false])) (([false,true,false])) [false] false n

theorem finalR (n : Nat) : ([] : List Bool) = [] := by
  rfl

theorem epoch (n : Nat) : run0 table (46+4*n) ⟨5,([false,false,false,false,false,false,true,false]),(rep [true,false] (n)) ++ ([true])⟩ = some ⟨3,([false,true,false,false,false,false]) ++ (rep [false,false] (n)) ++ ([false,false,true,false]),[]⟩ := by
  have H := (join0 (join0 (phase0 n) (phase1 n)) (phase2 n))
  rw [finalL n] at H
  rw [show 34+4*n+12=46+4*n by omega] at H
  exact H

theorem eq1l (n : Nat) : ([false,true,false,false,false,false]) ++ (rep [false,false] (n)) ++ ([false,false,true,false]) = ([false,true,false,false,false,false,false,false]) ++ (rep [false,false] (n)) ++ ([true,false]) := by
  calc
    _ = ([false,true,false,false,false,false,false]) ++ (rep [false,false] (n)) ++ ([false,true,false]) := by symm; simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using moveCut (([false,true,false,false,false,false])) (([false,true,false])) [false] false n
    _ = ([false,true,false,false,false,false,false,false]) ++ (rep [false,false] (n)) ++ ([true,false]) := by symm; simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using moveCut (([false,true,false,false,false,false,false])) (([true,false])) [false] false n

theorem canon (n : Nat) : run0 table (46+4*n) ⟨5,([false,false,false,false,false,false,true,false]),(rep [true,false] (n)) ++ ([true])⟩ = some ⟨3,([false,true,false,false,false,false,false,false]) ++ (rep [false,false] (n)) ++ ([true,false]),[]⟩ := by
  simpa only [eq1l n] using epoch n

end MFinish


namespace MCarry

-- 1RB0RE_1RC---_0RD0LD_1LD0RA_1LF1RD_0LF1LB

def table : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 0,true => some (some ⟨false,true,4⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 2,false => some (some ⟨false,true,3⟩)
  | 2,true => some (some ⟨false,false,3⟩)
  | 3,false => some (some ⟨true,false,3⟩)
  | 3,true => some (some ⟨false,true,0⟩)
  | 4,false => some (some ⟨true,false,5⟩)
  | 4,true => some (some ⟨true,true,3⟩)
  | 5,false => some (some ⟨false,false,5⟩)
  | 5,true => some (some ⟨true,false,1⟩)
  | _,_ => none

theorem phase0 (n : Nat) (R : List Bool) : run0 table 34 ⟨5,([false,false,false,false,false,false,true,false]),(rep [true,false] (n)) ++ ([true,false,false,false]) ++ (R)⟩ = some ⟨3,([false,true,true,false]),([true,false,true,false]) ++ (rep [true,false] (n)) ++ ([true,false,false,false]) ++ (R)⟩ := by rfl

theorem local1 (L R : List Bool) : run0 table 4 ⟨3,([false,true]) ++ (L),([true,false,true,false]) ++ ([true,false]) ++ (R)⟩ = some ⟨3,([false,true]) ++ ([false,false]) ++ (L),([true,false,true,false]) ++ (R)⟩ := by rfl

theorem phase1 (n : Nat) (R : List Bool) : run0 table (4*n) ⟨3,([false,true,true,false]),([true,false,true,false]) ++ (rep [true,false] (n)) ++ ([true,false,false,false]) ++ (R)⟩ = some ⟨3,([false,true]) ++ (rep [false,false] (n)) ++ ([true,false]),([true,false,true,false,true,false,false,false]) ++ (R)⟩ := by
  simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using sweepR table 3 [false,true] [true,false,true,false] [true,false] [false,false] 4 local1 n (([true,false])) (([true,false,false,false]) ++ (R))

theorem phase2 (n : Nat) (R : List Bool) : run0 table 16 ⟨3,([false,true]) ++ (rep [false,false] (n)) ++ ([true,false]),([true,false,true,false,true,false,false,false]) ++ (R)⟩ = some ⟨5,([false,false,false,false,false,false,false,false]) ++ (rep [false,false] (n)) ++ ([true,false]),([true,false]) ++ (R)⟩ := by rfl

theorem local3 (L R : List Bool) : run0 table 2 ⟨5,([false,false,false,false,false,false,false,false]) ++ ([false,false]) ++ (L),(R)⟩ = some ⟨5,([false,false,false,false,false,false,false,false]) ++ (L),([false,false]) ++ (R)⟩ := by rfl

theorem phase3 (n : Nat) (R : List Bool) : run0 table (2*n) ⟨5,([false,false,false,false,false,false,false,false]) ++ (rep [false,false] (n)) ++ ([true,false]),([true,false]) ++ (R)⟩ = some ⟨5,([false,false,false,false,false,false,false,false,true,false]),(rep [false,false] (n)) ++ ([true,false]) ++ (R)⟩ := by
  simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using sweepL table 5 [false,false,false,false,false,false,false,false] [] [false,false] [false,false] 2 local3 n (([true,false])) (([true,false]) ++ (R))

theorem phase4 (n : Nat) (R : List Bool) : run0 table 2 ⟨5,([false,false,false,false,false,false,false,false,true,false]),(rep [false,false] (n)) ++ ([true,false]) ++ (R)⟩ = some ⟨5,([false,false,false,false,false,false,true,false]),([false,false]) ++ (rep [false,false] (n)) ++ ([true,false]) ++ (R)⟩ := by rfl

theorem finalL (n : Nat) (R : List Bool) : ([false,false,false,false,false,false,true,false]) = ([false,false,false,false,false,false,true,false]) := by
  rfl

theorem finalR (n : Nat) (R : List Bool) : ([false,false]) ++ (rep [false,false] (n)) ++ ([true,false]) ++ (R) = (rep [false,false] (n)) ++ ([false,false,true,false]) ++ (R) := by
  calc
    _ = ([false]) ++ (rep [false,false] (n)) ++ ([false,true,false]) ++ (R) := by simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using moveCut (([false])) (([true,false]) ++ (R)) [false] false n
    _ = (rep [false,false] (n)) ++ ([false,false,true,false]) ++ (R) := by simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using moveCut ([]) (([false,true,false]) ++ (R)) [false] false n

theorem epoch (n : Nat) (R : List Bool) : run0 table (52+6*n) ⟨5,([false,false,false,false,false,false,true,false]),(rep [true,false] (n)) ++ ([true,false,false,false]) ++ (R)⟩ = some ⟨5,([false,false,false,false,false,false,true,false]),(rep [false,false] (n)) ++ ([false,false,true,false]) ++ (R)⟩ := by
  have H := (join0 (join0 (join0 (join0 (phase0 n R) (phase1 n R)) (phase2 n R)) (phase3 n R)) (phase4 n R))
  rw [finalR n R] at H
  rw [show 34+4*n+16+2*n+2=52+6*n by omega] at H
  exact H

theorem canon (n : Nat) (R : List Bool) : run0 table (52+6*n) ⟨5,([false,false,false,false,false,false,true,false]),(rep [true,false] (n)) ++ ([true,false,false,false]) ++ (R)⟩ = some ⟨5,([false,false,false,false,false,false,true,false]),(rep [false,false] (n)) ++ ([false,false,true,false]) ++ (R)⟩ := by
  exact epoch n R

end MCarry


abbrev table := MInit.table
abbrev A : List Bool := [true,false]
abbrev Z : List Bool := [false,false]
def Q (R : List Bool) : Z0 := ⟨5,[false,false,false,false,false,false,true,false],(R)⟩
def family (n : Nat) : Z0 := ⟨3,([false,true,false,false,false,false]) ++ (rep [false,false] (n)) ++ ([true,false]),[]⟩
def carryCost (n : Nat) : Nat := 46+6*n

theorem carry (n : Nat) (R : List Bool) : run0 table (carryCost n) (Q (rep A n ++ Z ++ R)) = some (Q (rep Z n ++ A ++ R)) := by
  cases n with
  | zero => rfl
  | succ n =>
    have h := MCarry.canon n R
    rw [show MCarry.table = table from rfl] at h
    unfold carryCost
    rw [show 46+6*n.succ = 52+6*n by omega]
    rw [rep_succ_snoc A n,rep_succ_snoc Z n]
    simpa only [table,Q,A,Z,List.append_assoc,List.nil_append,List.append_nil,List.cons_append] using h

theorem entry : run0 table 32 ⟨0,[],[]⟩ = some (family 0) := by rfl


def cost (n : Nat) : Nat := (4+2*n) + fillCost carryCost (n+0) + (46+4*n)
theorem growth (n : Nat) : run0 table (cost n) (family n) = some (family (n+1)) := by
  have h1 := MInit.canon n
  have h2 := fill table Q A Z carryCost carry (n+0) [true]
  have h3 := MFinish.canon n
  rw [rep_add Z n 0,rep_add A n 0] at h2
  simp only [Q,A,Z,rep,List.append_assoc,List.nil_append,List.append_nil,List.cons_append] at h2
  have h := join0 (join0 h1 h2) h3
  simpa only [cost,family,rep,rep_succ_snoc,List.append_assoc,List.nil_append,List.append_nil,List.cons_append] using h

theorem never (m : Machine) (hm : compatible table m) : NeverHalts m :=
  never_of_growth table family 32 cost entry (by intro n; unfold cost; omega) growth m hm

#print axioms growth
#print axioms never
end M2294

end BB6.Agent11Raw39B0RECounter2294
