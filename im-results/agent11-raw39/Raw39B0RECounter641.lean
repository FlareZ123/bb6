import Raw39CounterCarry
open BB6Coverage BB6Coverage.Agent31Pump BB6.Agent11CounterCarry
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedVariables false
namespace BB6.Agent11Raw39B0RECounter641
namespace M641

namespace MInit

-- 1RB0RE_1RC---_0RD0LD_1LD0RA_1LF0RE_0LF1LB

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
  | 4,true => some (some ⟨false,true,4⟩)
  | 5,false => some (some ⟨false,false,5⟩)
  | 5,true => some (some ⟨true,false,1⟩)
  | _,_ => none

theorem phase0 (n : Nat) : run0 table 1 ⟨4,([false,false,false,false,false]) ++ (rep [false] (n)) ++ ([true,false]),[]⟩ = some ⟨5,([false,false,false,false]) ++ (rep [false] (n)) ++ ([true,false]),([true])⟩ := by rfl

theorem local1 (L R : List Bool) : run0 table 1 ⟨5,([false,false,false,false]) ++ ([false]) ++ (L),(R)⟩ = some ⟨5,([false,false,false,false]) ++ (L),([false]) ++ (R)⟩ := by rfl

theorem phase1 (n : Nat) : run0 table (1*n) ⟨5,([false,false,false,false]) ++ (rep [false] (n)) ++ ([true,false]),([true])⟩ = some ⟨5,([false,false,false,false,true,false]),(rep [false] (n)) ++ ([true])⟩ := by
  simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using sweepL table 5 [false,false,false,false] [] [false] [false] 1 local1 n (([true,false])) (([true]))

theorem finalL (n : Nat) : ([false,false,false,false,true,false]) = ([false,false,false,false,true,false]) := by
  rfl

theorem finalR (n : Nat) : (rep [false] (n)) ++ ([true]) = (rep [false] (n)) ++ ([true]) := by
  rfl

theorem epoch (n : Nat) : run0 table (1+1*n) ⟨4,([false,false,false,false,false]) ++ (rep [false] (n)) ++ ([true,false]),[]⟩ = some ⟨5,([false,false,false,false,true,false]),(rep [false] (n)) ++ ([true])⟩ := by
  have H := (join0 (phase0 n) (phase1 n))
  rw [show 1+1*n=1+1*n by omega] at H
  exact H

theorem canon (n : Nat) : run0 table (1+1*n) ⟨4,([false,false,false,false,false]) ++ (rep [false] (n)) ++ ([true,false]),[]⟩ = some ⟨5,([false,false,false,false,true,false]),(rep [false] (n)) ++ ([true])⟩ := by
  exact epoch n

end MInit


namespace MFinish

-- 1RB0RE_1RC---_0RD0LD_1LD0RA_1LF0RE_0LF1LB

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
  | 4,true => some (some ⟨false,true,4⟩)
  | 5,false => some (some ⟨false,false,5⟩)
  | 5,true => some (some ⟨true,false,1⟩)
  | _,_ => none

theorem phase0 (n : Nat) : run0 table 31 ⟨5,([false,false,false,false,true,false]),(rep [true] (n)) ++ ([true])⟩ = some ⟨4,([true,false,false,true,false]),([true]) ++ (rep [true] (n)) ++ ([true])⟩ := by rfl

theorem local1 (L R : List Bool) : run0 table 1 ⟨4,([true]) ++ (L),([true]) ++ ([true]) ++ (R)⟩ = some ⟨4,([true]) ++ ([false]) ++ (L),([true]) ++ (R)⟩ := by rfl

theorem phase1 (n : Nat) : run0 table (1*n) ⟨4,([true,false,false,true,false]),([true]) ++ (rep [true] (n)) ++ ([true])⟩ = some ⟨4,([true]) ++ (rep [false] (n)) ++ ([false,false,true,false]),([true,true])⟩ := by
  simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using sweepR table 4 [true] [true] [true] [false] 1 local1 n (([false,false,true,false])) (([true]))

theorem phase2 (n : Nat) : run0 table 3 ⟨4,([true]) ++ (rep [false] (n)) ++ ([false,false,true,false]),([true,true])⟩ = some ⟨4,([false,false,false,false]) ++ (rep [false] (n)) ++ ([false,false,true,false]),[]⟩ := by rfl

theorem finalL (n : Nat) : ([false,false,false,false]) ++ (rep [false] (n)) ++ ([false,false,true,false]) = ([false,false,false,false,false]) ++ (rep [false] (n)) ++ ([false,true,false]) := by
  calc
    _ = ([false,false,false,false,false]) ++ (rep [false] (n)) ++ ([false,true,false]) := by symm; simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using moveCut (([false,false,false,false])) (([false,true,false])) [] false n

theorem finalR (n : Nat) : ([] : List Bool) = [] := by
  rfl

theorem epoch (n : Nat) : run0 table (34+1*n) ⟨5,([false,false,false,false,true,false]),(rep [true] (n)) ++ ([true])⟩ = some ⟨4,([false,false,false,false,false]) ++ (rep [false] (n)) ++ ([false,true,false]),[]⟩ := by
  have H := (join0 (join0 (phase0 n) (phase1 n)) (phase2 n))
  rw [finalL n] at H
  rw [show 31+1*n+3=34+1*n by omega] at H
  exact H

theorem eq1l (n : Nat) : ([false,false,false,false,false]) ++ (rep [false] (n)) ++ ([false,true,false]) = ([false,false,false,false,false,false]) ++ (rep [false] (n)) ++ ([true,false]) := by
  calc
    _ = ([false,false,false,false,false,false]) ++ (rep [false] (n)) ++ ([true,false]) := by symm; simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using moveCut (([false,false,false,false,false])) (([true,false])) [] false n

theorem canon (n : Nat) : run0 table (34+1*n) ⟨5,([false,false,false,false,true,false]),(rep [true] (n)) ++ ([true])⟩ = some ⟨4,([false,false,false,false,false,false]) ++ (rep [false] (n)) ++ ([true,false]),[]⟩ := by
  simpa only [eq1l n] using epoch n

end MFinish


namespace MCarry

-- 1RB0RE_1RC---_0RD0LD_1LD0RA_1LF0RE_0LF1LB

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
  | 4,true => some (some ⟨false,true,4⟩)
  | 5,false => some (some ⟨false,false,5⟩)
  | 5,true => some (some ⟨true,false,1⟩)
  | _,_ => none

theorem phase0 (n : Nat) (R : List Bool) : run0 table 31 ⟨5,([false,false,false,false,true,false]),(rep [true] (n)) ++ ([true,false]) ++ (R)⟩ = some ⟨4,([true,false,false,true,false]),([true]) ++ (rep [true] (n)) ++ ([true,false]) ++ (R)⟩ := by rfl

theorem local1 (L R : List Bool) : run0 table 1 ⟨4,([true]) ++ (L),([true]) ++ ([true]) ++ (R)⟩ = some ⟨4,([true]) ++ ([false]) ++ (L),([true]) ++ (R)⟩ := by rfl

theorem phase1 (n : Nat) (R : List Bool) : run0 table (1*n) ⟨4,([true,false,false,true,false]),([true]) ++ (rep [true] (n)) ++ ([true,false]) ++ (R)⟩ = some ⟨4,([true]) ++ (rep [false] (n)) ++ ([false,false,true,false]),([true,true,false]) ++ (R)⟩ := by
  simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using sweepR table 4 [true] [true] [true] [false] 1 local1 n (([false,false,true,false])) (([true,false]) ++ (R))

theorem phase2 (n : Nat) (R : List Bool) : run0 table 4 ⟨4,([true]) ++ (rep [false] (n)) ++ ([false,false,true,false]),([true,true,false]) ++ (R)⟩ = some ⟨5,([false,false,false]) ++ (rep [false] (n)) ++ ([false,false,true,false]),([true]) ++ (R)⟩ := by rfl

theorem local3 (L R : List Bool) : run0 table 1 ⟨5,([false,false,false]) ++ ([false]) ++ (L),(R)⟩ = some ⟨5,([false,false,false]) ++ (L),([false]) ++ (R)⟩ := by rfl

theorem phase3 (n : Nat) (R : List Bool) : run0 table (1*n) ⟨5,([false,false,false]) ++ (rep [false] (n)) ++ ([false,false,true,false]),([true]) ++ (R)⟩ = some ⟨5,([false,false,false,false,false,true,false]),(rep [false] (n)) ++ ([true]) ++ (R)⟩ := by
  simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using sweepL table 5 [false,false,false] [] [false] [false] 1 local3 n (([false,false,true,false])) (([true]) ++ (R))

theorem phase4 (n : Nat) (R : List Bool) : run0 table 1 ⟨5,([false,false,false,false,false,true,false]),(rep [false] (n)) ++ ([true]) ++ (R)⟩ = some ⟨5,([false,false,false,false,true,false]),([false]) ++ (rep [false] (n)) ++ ([true]) ++ (R)⟩ := by rfl

theorem finalL (n : Nat) (R : List Bool) : ([false,false,false,false,true,false]) = ([false,false,false,false,true,false]) := by
  rfl

theorem finalR (n : Nat) (R : List Bool) : ([false]) ++ (rep [false] (n)) ++ ([true]) ++ (R) = (rep [false] (n)) ++ ([false,true]) ++ (R) := by
  calc
    _ = (rep [false] (n)) ++ ([false,true]) ++ (R) := by simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using moveCut ([]) (([true]) ++ (R)) [] false n

theorem epoch (n : Nat) (R : List Bool) : run0 table (36+2*n) ⟨5,([false,false,false,false,true,false]),(rep [true] (n)) ++ ([true,false]) ++ (R)⟩ = some ⟨5,([false,false,false,false,true,false]),(rep [false] (n)) ++ ([false,true]) ++ (R)⟩ := by
  have H := (join0 (join0 (join0 (join0 (phase0 n R) (phase1 n R)) (phase2 n R)) (phase3 n R)) (phase4 n R))
  rw [finalR n R] at H
  rw [show 31+1*n+4+1*n+1=36+2*n by omega] at H
  exact H

theorem canon (n : Nat) (R : List Bool) : run0 table (36+2*n) ⟨5,([false,false,false,false,true,false]),(rep [true] (n)) ++ ([true,false]) ++ (R)⟩ = some ⟨5,([false,false,false,false,true,false]),(rep [false] (n)) ++ ([false,true]) ++ (R)⟩ := by
  exact epoch n R

end MCarry


abbrev table := MInit.table
abbrev A : List Bool := [true]
abbrev Z : List Bool := [false]
def Q (R : List Bool) : Z0 := ⟨5,[false,false,false,false,true,false],(R)⟩
def family (n : Nat) : Z0 := ⟨4,([false,false,false,false,false]) ++ (rep [false] (n)) ++ ([true,false]),[]⟩
def carryCost (n : Nat) : Nat := 34+2*n

theorem carry (n : Nat) (R : List Bool) : run0 table (carryCost n) (Q (rep A n ++ Z ++ R)) = some (Q (rep Z n ++ A ++ R)) := by
  cases n with
  | zero => rfl
  | succ n =>
    have h := MCarry.canon n R
    rw [show MCarry.table = table from rfl] at h
    unfold carryCost
    rw [show 34+2*n.succ = 36+2*n by omega]
    rw [rep_succ_snoc A n,rep_succ_snoc Z n]
    simpa only [table,Q,A,Z,List.append_assoc,List.nil_append,List.append_nil,List.cons_append] using h

theorem entry : run0 table 25 ⟨0,[],[]⟩ = some (family 0) := by rfl


def cost (n : Nat) : Nat := (1+1*n) + fillCost carryCost (n+0) + (34+1*n)
theorem growth (n : Nat) : run0 table (cost n) (family n) = some (family (n+1)) := by
  have h1 := MInit.canon n
  have h2 := fill table Q A Z carryCost carry (n+0) [true]
  have h3 := MFinish.canon n
  rw [rep_add Z n 0,rep_add A n 0] at h2
  simp only [Q,A,Z,rep,List.append_assoc,List.nil_append,List.append_nil,List.cons_append] at h2
  have h := join0 (join0 h1 h2) h3
  simpa only [cost,family,rep,rep_succ_snoc,List.append_assoc,List.nil_append,List.append_nil,List.cons_append] using h

theorem never (m : Machine) (hm : compatible table m) : NeverHalts m :=
  never_of_growth table family 25 cost entry (by intro n; unfold cost; omega) growth m hm

#print axioms growth
#print axioms never
end M641

end BB6.Agent11Raw39B0RECounter641
