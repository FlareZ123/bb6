import Raw39CounterCarry
open BB6Coverage BB6Coverage.Agent31Pump BB6.Agent11CounterCarry
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedVariables false
namespace BB6.Agent11Raw39RCCounter383
namespace M383

namespace MInit

-- 1RB0RC_1RC---_0RD0RE_1LD0RA_1LF1RC_0LF1RB

def table : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 0,true => some (some ⟨false,true,2⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 2,false => some (some ⟨false,true,3⟩)
  | 2,true => some (some ⟨false,true,4⟩)
  | 3,false => some (some ⟨true,false,3⟩)
  | 3,true => some (some ⟨false,true,0⟩)
  | 4,false => some (some ⟨true,false,5⟩)
  | 4,true => some (some ⟨true,true,2⟩)
  | 5,false => some (some ⟨false,false,5⟩)
  | 5,true => some (some ⟨true,true,1⟩)
  | _,_ => none

theorem phase0 (n : Nat) : run0 table 1 ⟨4,([false]) ++ (rep [false,false,false] (n)) ++ ([false,false,false,true]),[]⟩ = some ⟨5,(rep [false,false,false] (n)) ++ ([false,false,false,true]),([true])⟩ := by rfl

theorem local1 (L R : List Bool) : run0 table 3 ⟨5,([false,false,false]) ++ (L),(R)⟩ = some ⟨5,(L),([false,false,false]) ++ (R)⟩ := by rfl

theorem phase1 (n : Nat) : run0 table (3*n) ⟨5,(rep [false,false,false] (n)) ++ ([false,false,false,true]),([true])⟩ = some ⟨5,([false,false,false,true]),(rep [false,false,false] (n)) ++ ([true])⟩ := by
  simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using sweepL table 5 [] [] [false,false,false] [false,false,false] 3 local1 n (([false,false,false,true])) (([true]))

theorem phase2 (n : Nat) : run0 table 4 ⟨5,([false,false,false,true]),(rep [false,false,false] (n)) ++ ([true])⟩ = some ⟨1,([false,true]),([false,false]) ++ (rep [false,false,false] (n)) ++ ([true])⟩ := by rfl

theorem finalL (n : Nat) : ([false,true]) = ([false,true]) := by
  rfl

theorem finalR (n : Nat) : ([false,false]) ++ (rep [false,false,false] (n)) ++ ([true]) = (rep [false,false,false] (n)) ++ ([false,false,true]) := by
  calc
    _ = ([false]) ++ (rep [false,false,false] (n)) ++ ([false,true]) := by simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using moveCut (([false])) (([true])) [false,false] false n
    _ = (rep [false,false,false] (n)) ++ ([false,false,true]) := by simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using moveCut ([]) (([false,true])) [false,false] false n

theorem epoch (n : Nat) : run0 table (5+3*n) ⟨4,([false]) ++ (rep [false,false,false] (n)) ++ ([false,false,false,true]),[]⟩ = some ⟨1,([false,true]),(rep [false,false,false] (n)) ++ ([false,false,true])⟩ := by
  have H := (join0 (join0 (phase0 n) (phase1 n)) (phase2 n))
  rw [finalR n] at H
  rw [show 1+3*n+4=5+3*n by omega] at H
  exact H

theorem canon (n : Nat) : run0 table (5+3*n) ⟨4,([false]) ++ (rep [false,false,false] (n)) ++ ([false,false,false,true]),[]⟩ = some ⟨1,([false,true]),(rep [false,false,false] (n)) ++ ([false,false,true])⟩ := by
  exact epoch n

end MInit


namespace MFinish

-- 1RB0RC_1RC---_0RD0RE_1LD0RA_1LF1RC_0LF1RB

def table : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 0,true => some (some ⟨false,true,2⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 2,false => some (some ⟨false,true,3⟩)
  | 2,true => some (some ⟨false,true,4⟩)
  | 3,false => some (some ⟨true,false,3⟩)
  | 3,true => some (some ⟨false,true,0⟩)
  | 4,false => some (some ⟨true,false,5⟩)
  | 4,true => some (some ⟨true,true,2⟩)
  | 5,false => some (some ⟨false,false,5⟩)
  | 5,true => some (some ⟨true,true,1⟩)
  | _,_ => none

theorem phase0 (n : Nat) : run0 table 1 ⟨1,([false,true]),([false,false,true]) ++ (rep [false,false,true] (n))⟩ = some ⟨2,([false,true,true]),([false,true]) ++ (rep [false,false,true] (n))⟩ := by rfl

theorem local1 (L R : List Bool) : run0 table 7 ⟨2,([false,true]) ++ (L),([false,true]) ++ ([false,false,true]) ++ (R)⟩ = some ⟨2,([false,true]) ++ ([false,false,false]) ++ (L),([false,true]) ++ (R)⟩ := by rfl

theorem phase1 (n : Nat) : run0 table (7*n) ⟨2,([false,true,true]),([false,true]) ++ (rep [false,false,true] (n))⟩ = some ⟨2,([false,true]) ++ (rep [false,false,false] (n)) ++ ([true]),([false,true])⟩ := by
  simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using sweepR table 2 [false,true] [false,true] [false,false,true] [false,false,false] 7 local1 n (([true])) ([])

theorem phase2 (n : Nat) : run0 table 13 ⟨2,([false,true]) ++ (rep [false,false,false] (n)) ++ ([true]),([false,true])⟩ = some ⟨4,([false,false,false,false,false,false,false]) ++ (rep [false,false,false] (n)) ++ ([true]),[]⟩ := by rfl

theorem finalL (n : Nat) : ([false,false,false,false,false,false,false]) ++ (rep [false,false,false] (n)) ++ ([true]) = (rep [false,false,false] (n)) ++ ([false,false,false,false,false,false,false,true]) := by
  calc
    _ = ([false,false,false,false,false,false]) ++ (rep [false,false,false] (n)) ++ ([false,true]) := by simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using moveCut (([false,false,false,false,false,false])) (([true])) [false,false] false n
    _ = ([false,false,false,false,false]) ++ (rep [false,false,false] (n)) ++ ([false,false,true]) := by simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using moveCut (([false,false,false,false,false])) (([false,true])) [false,false] false n
    _ = ([false,false,false,false]) ++ (rep [false,false,false] (n)) ++ ([false,false,false,true]) := by simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using moveCut (([false,false,false,false])) (([false,false,true])) [false,false] false n
    _ = ([false,false,false]) ++ (rep [false,false,false] (n)) ++ ([false,false,false,false,true]) := by simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using moveCut (([false,false,false])) (([false,false,false,true])) [false,false] false n
    _ = ([false,false]) ++ (rep [false,false,false] (n)) ++ ([false,false,false,false,false,true]) := by simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using moveCut (([false,false])) (([false,false,false,false,true])) [false,false] false n
    _ = ([false]) ++ (rep [false,false,false] (n)) ++ ([false,false,false,false,false,false,true]) := by simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using moveCut (([false])) (([false,false,false,false,false,true])) [false,false] false n
    _ = (rep [false,false,false] (n)) ++ ([false,false,false,false,false,false,false,true]) := by simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using moveCut ([]) (([false,false,false,false,false,false,true])) [false,false] false n

theorem finalR (n : Nat) : ([] : List Bool) = [] := by
  rfl

theorem epoch (n : Nat) : run0 table (14+7*n) ⟨1,([false,true]),([false,false,true]) ++ (rep [false,false,true] (n))⟩ = some ⟨4,(rep [false,false,false] (n)) ++ ([false,false,false,false,false,false,false,true]),[]⟩ := by
  have H := (join0 (join0 (phase0 n) (phase1 n)) (phase2 n))
  rw [finalL n] at H
  rw [show 1+7*n+13=14+7*n by omega] at H
  exact H

theorem eq0r (n : Nat) : ([false,false,true]) ++ (rep [false,false,true] (n)) = (rep [false,false,true] (n)) ++ ([false,false,true]) := by
  calc
    _ = ([false,false]) ++ (rep [true,false,false] (n)) ++ ([true]) := by simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using moveCut (([false,false])) ([]) [false,false] true n
    _ = ([false]) ++ (rep [false,true,false] (n)) ++ ([false,true]) := by simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using moveCut (([false])) (([true])) [true,false] false n
    _ = (rep [false,false,true] (n)) ++ ([false,false,true]) := by simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using moveCut ([]) (([false,true])) [false,true] false n

theorem eq1l (n : Nat) : (rep [false,false,false] (n)) ++ ([false,false,false,false,false,false,false,true]) = ([false,false,false,false]) ++ (rep [false,false,false] (n)) ++ ([false,false,false,true]) := by
  calc
    _ = ([false]) ++ (rep [false,false,false] (n)) ++ ([false,false,false,false,false,false,true]) := by symm; simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using moveCut ([]) (([false,false,false,false,false,false,true])) [false,false] false n
    _ = ([false,false]) ++ (rep [false,false,false] (n)) ++ ([false,false,false,false,false,true]) := by symm; simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using moveCut (([false])) (([false,false,false,false,false,true])) [false,false] false n
    _ = ([false,false,false]) ++ (rep [false,false,false] (n)) ++ ([false,false,false,false,true]) := by symm; simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using moveCut (([false,false])) (([false,false,false,false,true])) [false,false] false n
    _ = ([false,false,false,false]) ++ (rep [false,false,false] (n)) ++ ([false,false,false,true]) := by symm; simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using moveCut (([false,false,false])) (([false,false,false,true])) [false,false] false n

theorem canon (n : Nat) : run0 table (14+7*n) ⟨1,([false,true]),(rep [false,false,true] (n)) ++ ([false,false,true])⟩ = some ⟨4,([false,false,false,false]) ++ (rep [false,false,false] (n)) ++ ([false,false,false,true]),[]⟩ := by
  simpa only [eq0r n, eq1l n] using epoch n

end MFinish


namespace MCarry

-- 1RB0RC_1RC---_0RD0RE_1LD0RA_1LF1RC_0LF1RB

def table : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 0,true => some (some ⟨false,true,2⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 2,false => some (some ⟨false,true,3⟩)
  | 2,true => some (some ⟨false,true,4⟩)
  | 3,false => some (some ⟨true,false,3⟩)
  | 3,true => some (some ⟨false,true,0⟩)
  | 4,false => some (some ⟨true,false,5⟩)
  | 4,true => some (some ⟨true,true,2⟩)
  | 5,false => some (some ⟨false,false,5⟩)
  | 5,true => some (some ⟨true,true,1⟩)
  | _,_ => none

theorem phase0 (n : Nat) (R : List Bool) : run0 table 1 ⟨1,([false,true]),([false,false,true]) ++ (rep [false,false,true] (n)) ++ ([false,false,false]) ++ (R)⟩ = some ⟨2,([false,true,true]),([false,true]) ++ (rep [false,false,true] (n)) ++ ([false,false,false]) ++ (R)⟩ := by rfl

theorem local1 (L R : List Bool) : run0 table 7 ⟨2,([false,true]) ++ (L),([false,true]) ++ ([false,false,true]) ++ (R)⟩ = some ⟨2,([false,true]) ++ ([false,false,false]) ++ (L),([false,true]) ++ (R)⟩ := by rfl

theorem phase1 (n : Nat) (R : List Bool) : run0 table (7*n) ⟨2,([false,true,true]),([false,true]) ++ (rep [false,false,true] (n)) ++ ([false,false,false]) ++ (R)⟩ = some ⟨2,([false,true]) ++ (rep [false,false,false] (n)) ++ ([true]),([false,true,false,false,false]) ++ (R)⟩ := by
  simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using sweepR table 2 [false,true] [false,true] [false,false,true] [false,false,false] 7 local1 n (([true])) (([false,false,false]) ++ (R))

theorem phase2 (n : Nat) (R : List Bool) : run0 table 14 ⟨2,([false,true]) ++ (rep [false,false,false] (n)) ++ ([true]),([false,true,false,false,false]) ++ (R)⟩ = some ⟨5,([false,false,false,false,false,false]) ++ (rep [false,false,false] (n)) ++ ([true]),([true]) ++ (R)⟩ := by rfl

theorem local3 (L R : List Bool) : run0 table 3 ⟨5,([false,false,false,false,false,false]) ++ ([false,false,false]) ++ (L),(R)⟩ = some ⟨5,([false,false,false,false,false,false]) ++ (L),([false,false,false]) ++ (R)⟩ := by rfl

theorem phase3 (n : Nat) (R : List Bool) : run0 table (3*n) ⟨5,([false,false,false,false,false,false]) ++ (rep [false,false,false] (n)) ++ ([true]),([true]) ++ (R)⟩ = some ⟨5,([false,false,false,false,false,false,true]),(rep [false,false,false] (n)) ++ ([true]) ++ (R)⟩ := by
  simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using sweepL table 5 [false,false,false,false,false,false] [] [false,false,false] [false,false,false] 3 local3 n (([true])) (([true]) ++ (R))

theorem phase4 (n : Nat) (R : List Bool) : run0 table 7 ⟨5,([false,false,false,false,false,false,true]),(rep [false,false,false] (n)) ++ ([true]) ++ (R)⟩ = some ⟨1,([false,true]),([false,false,false,false,false]) ++ (rep [false,false,false] (n)) ++ ([true]) ++ (R)⟩ := by rfl

theorem finalL (n : Nat) (R : List Bool) : ([false,true]) = ([false,true]) := by
  rfl

theorem finalR (n : Nat) (R : List Bool) : ([false,false,false,false,false]) ++ (rep [false,false,false] (n)) ++ ([true]) ++ (R) = (rep [false,false,false] (n)) ++ ([false,false,false,false,false,true]) ++ (R) := by
  calc
    _ = ([false,false,false,false]) ++ (rep [false,false,false] (n)) ++ ([false,true]) ++ (R) := by simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using moveCut (([false,false,false,false])) (([true]) ++ (R)) [false,false] false n
    _ = ([false,false,false]) ++ (rep [false,false,false] (n)) ++ ([false,false,true]) ++ (R) := by simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using moveCut (([false,false,false])) (([false,true]) ++ (R)) [false,false] false n
    _ = ([false,false]) ++ (rep [false,false,false] (n)) ++ ([false,false,false,true]) ++ (R) := by simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using moveCut (([false,false])) (([false,false,true]) ++ (R)) [false,false] false n
    _ = ([false]) ++ (rep [false,false,false] (n)) ++ ([false,false,false,false,true]) ++ (R) := by simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using moveCut (([false])) (([false,false,false,true]) ++ (R)) [false,false] false n
    _ = (rep [false,false,false] (n)) ++ ([false,false,false,false,false,true]) ++ (R) := by simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using moveCut ([]) (([false,false,false,false,true]) ++ (R)) [false,false] false n

theorem epoch (n : Nat) (R : List Bool) : run0 table (22+10*n) ⟨1,([false,true]),([false,false,true]) ++ (rep [false,false,true] (n)) ++ ([false,false,false]) ++ (R)⟩ = some ⟨1,([false,true]),(rep [false,false,false] (n)) ++ ([false,false,false,false,false,true]) ++ (R)⟩ := by
  have H := (join0 (join0 (join0 (join0 (phase0 n R) (phase1 n R)) (phase2 n R)) (phase3 n R)) (phase4 n R))
  rw [finalR n R] at H
  rw [show 1+7*n+14+3*n+7=22+10*n by omega] at H
  exact H

theorem eq0r (n : Nat) (R : List Bool) : ([false,false,true]) ++ (rep [false,false,true] (n)) ++ ([false,false,false]) ++ (R) = (rep [false,false,true] (n)) ++ ([false,false,true,false,false,false]) ++ (R) := by
  calc
    _ = ([false,false]) ++ (rep [true,false,false] (n)) ++ ([true,false,false,false]) ++ (R) := by simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using moveCut (([false,false])) (([false,false,false]) ++ (R)) [false,false] true n
    _ = ([false]) ++ (rep [false,true,false] (n)) ++ ([false,true,false,false,false]) ++ (R) := by simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using moveCut (([false])) (([true,false,false,false]) ++ (R)) [true,false] false n
    _ = (rep [false,false,true] (n)) ++ ([false,false,true,false,false,false]) ++ (R) := by simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using moveCut ([]) (([false,true,false,false,false]) ++ (R)) [false,true] false n

theorem canon (n : Nat) (R : List Bool) : run0 table (22+10*n) ⟨1,([false,true]),(rep [false,false,true] (n)) ++ ([false,false,true,false,false,false]) ++ (R)⟩ = some ⟨1,([false,true]),(rep [false,false,false] (n)) ++ ([false,false,false,false,false,true]) ++ (R)⟩ := by
  simpa only [eq0r n R] using epoch n R

end MCarry


abbrev table := MInit.table
abbrev A : List Bool := [false,false,true]
abbrev Z : List Bool := [false,false,false]
def Q (R : List Bool) : Z0 := ⟨1,[false,true],(R)⟩
def family (n : Nat) : Z0 := ⟨4,([false]) ++ (rep [false,false,false] (n)) ++ ([false,false,false,true]),[]⟩
def carryCost (n : Nat) : Nat := 12+10*n

theorem carry (n : Nat) (R : List Bool) : run0 table (carryCost n) (Q (rep A n ++ Z ++ R)) = some (Q (rep Z n ++ A ++ R)) := by
  cases n with
  | zero => rfl
  | succ n =>
    have h := MCarry.canon n R
    rw [show MCarry.table = table from rfl] at h
    unfold carryCost
    rw [show 12+10*n.succ = 22+10*n by omega]
    rw [rep_succ_snoc A n,rep_succ_snoc Z n]
    simpa only [table,Q,A,Z,List.append_assoc,List.nil_append,List.append_nil,List.cons_append] using h

theorem entry : run0 table 8 ⟨0,[],[]⟩ = some (family 0) := by rfl


def cost (n : Nat) : Nat := (5+3*n) + fillCost carryCost (n+0) + (14+7*n)

theorem growth (n : Nat) : run0 table (cost n) (family n) = some (family (n+1)) := by
  have h1 := MInit.canon n
  have h2 := fill table Q A Z carryCost carry (n+0) [false,false,true]
  have h3 := MFinish.canon n
  rw [rep_add Z n 0,rep_add A n 0] at h2
  simp only [Q,A,Z,rep,List.append_assoc,List.nil_append,List.append_nil,List.cons_append] at h2
  have h := join0 (join0 h1 h2) h3
  simpa only [cost,family,rep,rep_succ_snoc,List.append_assoc,List.nil_append,List.append_nil,List.cons_append] using h


theorem never (m : Machine) (hm : compatible table m) : NeverHalts m :=
  never_of_growth table family 8 cost entry (by intro n; unfold cost; omega) growth m hm

#print axioms growth
#print axioms never
end M383
namespace M589

namespace MInit

-- 1RB0RC_1RC---_0RD0RF_1LD0RA_0LE1RB_1LE1RC

def table : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 0,true => some (some ⟨false,true,2⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 2,false => some (some ⟨false,true,3⟩)
  | 2,true => some (some ⟨false,true,5⟩)
  | 3,false => some (some ⟨true,false,3⟩)
  | 3,true => some (some ⟨false,true,0⟩)
  | 4,false => some (some ⟨false,false,4⟩)
  | 4,true => some (some ⟨true,true,1⟩)
  | 5,false => some (some ⟨true,false,4⟩)
  | 5,true => some (some ⟨true,true,2⟩)
  | _,_ => none

theorem phase0 (n : Nat) : run0 table 1 ⟨5,([false]) ++ (rep [false,false,false] (n)) ++ ([false,false,false,true]),[]⟩ = some ⟨4,(rep [false,false,false] (n)) ++ ([false,false,false,true]),([true])⟩ := by rfl

theorem local1 (L R : List Bool) : run0 table 3 ⟨4,([false,false,false]) ++ (L),(R)⟩ = some ⟨4,(L),([false,false,false]) ++ (R)⟩ := by rfl

theorem phase1 (n : Nat) : run0 table (3*n) ⟨4,(rep [false,false,false] (n)) ++ ([false,false,false,true]),([true])⟩ = some ⟨4,([false,false,false,true]),(rep [false,false,false] (n)) ++ ([true])⟩ := by
  simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using sweepL table 4 [] [] [false,false,false] [false,false,false] 3 local1 n (([false,false,false,true])) (([true]))

theorem phase2 (n : Nat) : run0 table 4 ⟨4,([false,false,false,true]),(rep [false,false,false] (n)) ++ ([true])⟩ = some ⟨1,([false,true]),([false,false]) ++ (rep [false,false,false] (n)) ++ ([true])⟩ := by rfl

theorem finalL (n : Nat) : ([false,true]) = ([false,true]) := by
  rfl

theorem finalR (n : Nat) : ([false,false]) ++ (rep [false,false,false] (n)) ++ ([true]) = (rep [false,false,false] (n)) ++ ([false,false,true]) := by
  calc
    _ = ([false]) ++ (rep [false,false,false] (n)) ++ ([false,true]) := by simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using moveCut (([false])) (([true])) [false,false] false n
    _ = (rep [false,false,false] (n)) ++ ([false,false,true]) := by simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using moveCut ([]) (([false,true])) [false,false] false n

theorem epoch (n : Nat) : run0 table (5+3*n) ⟨5,([false]) ++ (rep [false,false,false] (n)) ++ ([false,false,false,true]),[]⟩ = some ⟨1,([false,true]),(rep [false,false,false] (n)) ++ ([false,false,true])⟩ := by
  have H := (join0 (join0 (phase0 n) (phase1 n)) (phase2 n))
  rw [finalR n] at H
  rw [show 1+3*n+4=5+3*n by omega] at H
  exact H

theorem canon (n : Nat) : run0 table (5+3*n) ⟨5,([false]) ++ (rep [false,false,false] (n)) ++ ([false,false,false,true]),[]⟩ = some ⟨1,([false,true]),(rep [false,false,false] (n)) ++ ([false,false,true])⟩ := by
  exact epoch n

end MInit


namespace MFinish

-- 1RB0RC_1RC---_0RD0RF_1LD0RA_0LE1RB_1LE1RC

def table : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 0,true => some (some ⟨false,true,2⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 2,false => some (some ⟨false,true,3⟩)
  | 2,true => some (some ⟨false,true,5⟩)
  | 3,false => some (some ⟨true,false,3⟩)
  | 3,true => some (some ⟨false,true,0⟩)
  | 4,false => some (some ⟨false,false,4⟩)
  | 4,true => some (some ⟨true,true,1⟩)
  | 5,false => some (some ⟨true,false,4⟩)
  | 5,true => some (some ⟨true,true,2⟩)
  | _,_ => none

theorem phase0 (n : Nat) : run0 table 1 ⟨1,([false,true]),([false,false,true]) ++ (rep [false,false,true] (n))⟩ = some ⟨2,([false,true,true]),([false,true]) ++ (rep [false,false,true] (n))⟩ := by rfl

theorem local1 (L R : List Bool) : run0 table 7 ⟨2,([false,true]) ++ (L),([false,true]) ++ ([false,false,true]) ++ (R)⟩ = some ⟨2,([false,true]) ++ ([false,false,false]) ++ (L),([false,true]) ++ (R)⟩ := by rfl

theorem phase1 (n : Nat) : run0 table (7*n) ⟨2,([false,true,true]),([false,true]) ++ (rep [false,false,true] (n))⟩ = some ⟨2,([false,true]) ++ (rep [false,false,false] (n)) ++ ([true]),([false,true])⟩ := by
  simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using sweepR table 2 [false,true] [false,true] [false,false,true] [false,false,false] 7 local1 n (([true])) ([])

theorem phase2 (n : Nat) : run0 table 13 ⟨2,([false,true]) ++ (rep [false,false,false] (n)) ++ ([true]),([false,true])⟩ = some ⟨5,([false,false,false,false,false,false,false]) ++ (rep [false,false,false] (n)) ++ ([true]),[]⟩ := by rfl

theorem finalL (n : Nat) : ([false,false,false,false,false,false,false]) ++ (rep [false,false,false] (n)) ++ ([true]) = (rep [false,false,false] (n)) ++ ([false,false,false,false,false,false,false,true]) := by
  calc
    _ = ([false,false,false,false,false,false]) ++ (rep [false,false,false] (n)) ++ ([false,true]) := by simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using moveCut (([false,false,false,false,false,false])) (([true])) [false,false] false n
    _ = ([false,false,false,false,false]) ++ (rep [false,false,false] (n)) ++ ([false,false,true]) := by simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using moveCut (([false,false,false,false,false])) (([false,true])) [false,false] false n
    _ = ([false,false,false,false]) ++ (rep [false,false,false] (n)) ++ ([false,false,false,true]) := by simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using moveCut (([false,false,false,false])) (([false,false,true])) [false,false] false n
    _ = ([false,false,false]) ++ (rep [false,false,false] (n)) ++ ([false,false,false,false,true]) := by simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using moveCut (([false,false,false])) (([false,false,false,true])) [false,false] false n
    _ = ([false,false]) ++ (rep [false,false,false] (n)) ++ ([false,false,false,false,false,true]) := by simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using moveCut (([false,false])) (([false,false,false,false,true])) [false,false] false n
    _ = ([false]) ++ (rep [false,false,false] (n)) ++ ([false,false,false,false,false,false,true]) := by simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using moveCut (([false])) (([false,false,false,false,false,true])) [false,false] false n
    _ = (rep [false,false,false] (n)) ++ ([false,false,false,false,false,false,false,true]) := by simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using moveCut ([]) (([false,false,false,false,false,false,true])) [false,false] false n

theorem finalR (n : Nat) : ([] : List Bool) = [] := by
  rfl

theorem epoch (n : Nat) : run0 table (14+7*n) ⟨1,([false,true]),([false,false,true]) ++ (rep [false,false,true] (n))⟩ = some ⟨5,(rep [false,false,false] (n)) ++ ([false,false,false,false,false,false,false,true]),[]⟩ := by
  have H := (join0 (join0 (phase0 n) (phase1 n)) (phase2 n))
  rw [finalL n] at H
  rw [show 1+7*n+13=14+7*n by omega] at H
  exact H

theorem eq0r (n : Nat) : ([false,false,true]) ++ (rep [false,false,true] (n)) = (rep [false,false,true] (n)) ++ ([false,false,true]) := by
  calc
    _ = ([false,false]) ++ (rep [true,false,false] (n)) ++ ([true]) := by simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using moveCut (([false,false])) ([]) [false,false] true n
    _ = ([false]) ++ (rep [false,true,false] (n)) ++ ([false,true]) := by simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using moveCut (([false])) (([true])) [true,false] false n
    _ = (rep [false,false,true] (n)) ++ ([false,false,true]) := by simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using moveCut ([]) (([false,true])) [false,true] false n

theorem eq1l (n : Nat) : (rep [false,false,false] (n)) ++ ([false,false,false,false,false,false,false,true]) = ([false,false,false,false]) ++ (rep [false,false,false] (n)) ++ ([false,false,false,true]) := by
  calc
    _ = ([false]) ++ (rep [false,false,false] (n)) ++ ([false,false,false,false,false,false,true]) := by symm; simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using moveCut ([]) (([false,false,false,false,false,false,true])) [false,false] false n
    _ = ([false,false]) ++ (rep [false,false,false] (n)) ++ ([false,false,false,false,false,true]) := by symm; simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using moveCut (([false])) (([false,false,false,false,false,true])) [false,false] false n
    _ = ([false,false,false]) ++ (rep [false,false,false] (n)) ++ ([false,false,false,false,true]) := by symm; simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using moveCut (([false,false])) (([false,false,false,false,true])) [false,false] false n
    _ = ([false,false,false,false]) ++ (rep [false,false,false] (n)) ++ ([false,false,false,true]) := by symm; simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using moveCut (([false,false,false])) (([false,false,false,true])) [false,false] false n

theorem canon (n : Nat) : run0 table (14+7*n) ⟨1,([false,true]),(rep [false,false,true] (n)) ++ ([false,false,true])⟩ = some ⟨5,([false,false,false,false]) ++ (rep [false,false,false] (n)) ++ ([false,false,false,true]),[]⟩ := by
  simpa only [eq0r n, eq1l n] using epoch n

end MFinish


namespace MCarry

-- 1RB0RC_1RC---_0RD0RF_1LD0RA_0LE1RB_1LE1RC

def table : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 0,true => some (some ⟨false,true,2⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 2,false => some (some ⟨false,true,3⟩)
  | 2,true => some (some ⟨false,true,5⟩)
  | 3,false => some (some ⟨true,false,3⟩)
  | 3,true => some (some ⟨false,true,0⟩)
  | 4,false => some (some ⟨false,false,4⟩)
  | 4,true => some (some ⟨true,true,1⟩)
  | 5,false => some (some ⟨true,false,4⟩)
  | 5,true => some (some ⟨true,true,2⟩)
  | _,_ => none

theorem phase0 (n : Nat) (R : List Bool) : run0 table 1 ⟨1,([false,true]),([false,false,true]) ++ (rep [false,false,true] (n)) ++ ([false,false,false]) ++ (R)⟩ = some ⟨2,([false,true,true]),([false,true]) ++ (rep [false,false,true] (n)) ++ ([false,false,false]) ++ (R)⟩ := by rfl

theorem local1 (L R : List Bool) : run0 table 7 ⟨2,([false,true]) ++ (L),([false,true]) ++ ([false,false,true]) ++ (R)⟩ = some ⟨2,([false,true]) ++ ([false,false,false]) ++ (L),([false,true]) ++ (R)⟩ := by rfl

theorem phase1 (n : Nat) (R : List Bool) : run0 table (7*n) ⟨2,([false,true,true]),([false,true]) ++ (rep [false,false,true] (n)) ++ ([false,false,false]) ++ (R)⟩ = some ⟨2,([false,true]) ++ (rep [false,false,false] (n)) ++ ([true]),([false,true,false,false,false]) ++ (R)⟩ := by
  simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using sweepR table 2 [false,true] [false,true] [false,false,true] [false,false,false] 7 local1 n (([true])) (([false,false,false]) ++ (R))

theorem phase2 (n : Nat) (R : List Bool) : run0 table 14 ⟨2,([false,true]) ++ (rep [false,false,false] (n)) ++ ([true]),([false,true,false,false,false]) ++ (R)⟩ = some ⟨4,([false,false,false,false,false,false]) ++ (rep [false,false,false] (n)) ++ ([true]),([true]) ++ (R)⟩ := by rfl

theorem local3 (L R : List Bool) : run0 table 3 ⟨4,([false,false,false,false,false,false]) ++ ([false,false,false]) ++ (L),(R)⟩ = some ⟨4,([false,false,false,false,false,false]) ++ (L),([false,false,false]) ++ (R)⟩ := by rfl

theorem phase3 (n : Nat) (R : List Bool) : run0 table (3*n) ⟨4,([false,false,false,false,false,false]) ++ (rep [false,false,false] (n)) ++ ([true]),([true]) ++ (R)⟩ = some ⟨4,([false,false,false,false,false,false,true]),(rep [false,false,false] (n)) ++ ([true]) ++ (R)⟩ := by
  simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using sweepL table 4 [false,false,false,false,false,false] [] [false,false,false] [false,false,false] 3 local3 n (([true])) (([true]) ++ (R))

theorem phase4 (n : Nat) (R : List Bool) : run0 table 7 ⟨4,([false,false,false,false,false,false,true]),(rep [false,false,false] (n)) ++ ([true]) ++ (R)⟩ = some ⟨1,([false,true]),([false,false,false,false,false]) ++ (rep [false,false,false] (n)) ++ ([true]) ++ (R)⟩ := by rfl

theorem finalL (n : Nat) (R : List Bool) : ([false,true]) = ([false,true]) := by
  rfl

theorem finalR (n : Nat) (R : List Bool) : ([false,false,false,false,false]) ++ (rep [false,false,false] (n)) ++ ([true]) ++ (R) = (rep [false,false,false] (n)) ++ ([false,false,false,false,false,true]) ++ (R) := by
  calc
    _ = ([false,false,false,false]) ++ (rep [false,false,false] (n)) ++ ([false,true]) ++ (R) := by simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using moveCut (([false,false,false,false])) (([true]) ++ (R)) [false,false] false n
    _ = ([false,false,false]) ++ (rep [false,false,false] (n)) ++ ([false,false,true]) ++ (R) := by simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using moveCut (([false,false,false])) (([false,true]) ++ (R)) [false,false] false n
    _ = ([false,false]) ++ (rep [false,false,false] (n)) ++ ([false,false,false,true]) ++ (R) := by simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using moveCut (([false,false])) (([false,false,true]) ++ (R)) [false,false] false n
    _ = ([false]) ++ (rep [false,false,false] (n)) ++ ([false,false,false,false,true]) ++ (R) := by simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using moveCut (([false])) (([false,false,false,true]) ++ (R)) [false,false] false n
    _ = (rep [false,false,false] (n)) ++ ([false,false,false,false,false,true]) ++ (R) := by simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using moveCut ([]) (([false,false,false,false,true]) ++ (R)) [false,false] false n

theorem epoch (n : Nat) (R : List Bool) : run0 table (22+10*n) ⟨1,([false,true]),([false,false,true]) ++ (rep [false,false,true] (n)) ++ ([false,false,false]) ++ (R)⟩ = some ⟨1,([false,true]),(rep [false,false,false] (n)) ++ ([false,false,false,false,false,true]) ++ (R)⟩ := by
  have H := (join0 (join0 (join0 (join0 (phase0 n R) (phase1 n R)) (phase2 n R)) (phase3 n R)) (phase4 n R))
  rw [finalR n R] at H
  rw [show 1+7*n+14+3*n+7=22+10*n by omega] at H
  exact H

theorem eq0r (n : Nat) (R : List Bool) : ([false,false,true]) ++ (rep [false,false,true] (n)) ++ ([false,false,false]) ++ (R) = (rep [false,false,true] (n)) ++ ([false,false,true,false,false,false]) ++ (R) := by
  calc
    _ = ([false,false]) ++ (rep [true,false,false] (n)) ++ ([true,false,false,false]) ++ (R) := by simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using moveCut (([false,false])) (([false,false,false]) ++ (R)) [false,false] true n
    _ = ([false]) ++ (rep [false,true,false] (n)) ++ ([false,true,false,false,false]) ++ (R) := by simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using moveCut (([false])) (([true,false,false,false]) ++ (R)) [true,false] false n
    _ = (rep [false,false,true] (n)) ++ ([false,false,true,false,false,false]) ++ (R) := by simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using moveCut ([]) (([false,true,false,false,false]) ++ (R)) [false,true] false n

theorem canon (n : Nat) (R : List Bool) : run0 table (22+10*n) ⟨1,([false,true]),(rep [false,false,true] (n)) ++ ([false,false,true,false,false,false]) ++ (R)⟩ = some ⟨1,([false,true]),(rep [false,false,false] (n)) ++ ([false,false,false,false,false,true]) ++ (R)⟩ := by
  simpa only [eq0r n R] using epoch n R

end MCarry


abbrev table := MInit.table
abbrev A : List Bool := [false,false,true]
abbrev Z : List Bool := [false,false,false]
def Q (R : List Bool) : Z0 := ⟨1,[false,true],(R)⟩
def family (n : Nat) : Z0 := ⟨5,([false]) ++ (rep [false,false,false] (n)) ++ ([false,false,false,true]),[]⟩
def carryCost (n : Nat) : Nat := 12+10*n

theorem carry (n : Nat) (R : List Bool) : run0 table (carryCost n) (Q (rep A n ++ Z ++ R)) = some (Q (rep Z n ++ A ++ R)) := by
  cases n with
  | zero => rfl
  | succ n =>
    have h := MCarry.canon n R
    rw [show MCarry.table = table from rfl] at h
    unfold carryCost
    rw [show 12+10*n.succ = 22+10*n by omega]
    rw [rep_succ_snoc A n,rep_succ_snoc Z n]
    simpa only [table,Q,A,Z,List.append_assoc,List.nil_append,List.append_nil,List.cons_append] using h

theorem entry : run0 table 8 ⟨0,[],[]⟩ = some (family 0) := by rfl


def cost (n : Nat) : Nat := (5+3*n) + fillCost carryCost (n+0) + (14+7*n)

theorem growth (n : Nat) : run0 table (cost n) (family n) = some (family (n+1)) := by
  have h1 := MInit.canon n
  have h2 := fill table Q A Z carryCost carry (n+0) [false,false,true]
  have h3 := MFinish.canon n
  rw [rep_add Z n 0,rep_add A n 0] at h2
  simp only [Q,A,Z,rep,List.append_assoc,List.nil_append,List.append_nil,List.cons_append] at h2
  have h := join0 (join0 h1 h2) h3
  simpa only [cost,family,rep,rep_succ_snoc,List.append_assoc,List.nil_append,List.append_nil,List.cons_append] using h


theorem never (m : Machine) (hm : compatible table m) : NeverHalts m :=
  never_of_growth table family 8 cost entry (by intro n; unfold cost; omega) growth m hm

#print axioms growth
#print axioms never
end M589

end BB6.Agent11Raw39RCCounter383
