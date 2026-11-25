import Raw39CounterCarry
open BB6Coverage BB6Coverage.Agent31Pump BB6.Agent11CounterCarry
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedVariables false
namespace BB6.Agent11Raw39B0RBCounter61
namespace M61

namespace MInit

-- 1RB0RB_1RC0LE_0RD1LD_1LD0RA_1LE0LF_1LC---

def table : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 0,true => some (some ⟨false,true,1⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 1,true => some (some ⟨false,false,4⟩)
  | 2,false => some (some ⟨false,true,3⟩)
  | 2,true => some (some ⟨true,false,3⟩)
  | 3,false => some (some ⟨true,false,3⟩)
  | 3,true => some (some ⟨false,true,0⟩)
  | 4,false => some (some ⟨true,false,4⟩)
  | 4,true => some (some ⟨false,false,5⟩)
  | 5,false => some (some ⟨true,false,2⟩)
  | _,_ => none

theorem phase0 (n : Nat) : run0 table 6 ⟨2,([false,true,false,false]) ++ (rep [false,false] (n)) ++ ([true,false,false]),[]⟩ = some ⟨4,([false,false,false,false]) ++ (rep [false,false] (n)) ++ ([true,false,false]),([false])⟩ := by rfl

theorem local1 (L R : List Bool) : run0 table 2 ⟨4,([false,false,false,false]) ++ ([false,false]) ++ (L),(R)⟩ = some ⟨4,([false,false,false,false]) ++ (L),([true,true]) ++ (R)⟩ := by rfl

theorem phase1 (n : Nat) : run0 table (2*n) ⟨4,([false,false,false,false]) ++ (rep [false,false] (n)) ++ ([true,false,false]),([false])⟩ = some ⟨4,([false,false,false,false,true,false,false]),(rep [true,true] (n)) ++ ([false])⟩ := by
  simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using sweepL table 4 [false,false,false,false] [] [false,false] [true,true] 2 local1 n (([true,false,false])) (([false]))

theorem finalL (n : Nat) : ([false,false,false,false,true,false,false]) = ([false,false,false,false,true,false,false]) := by
  rfl

theorem finalR (n : Nat) : (rep [true,true] (n)) ++ ([false]) = (rep [true,true] (n)) ++ ([false]) := by
  rfl

theorem epoch (n : Nat) : run0 table (6+2*n) ⟨2,([false,true,false,false]) ++ (rep [false,false] (n)) ++ ([true,false,false]),[]⟩ = some ⟨4,([false,false,false,false,true,false,false]),(rep [true,true] (n)) ++ ([false])⟩ := by
  have H := (join0 (phase0 n) (phase1 n))
  rw [show 6+2*n=6+2*n by omega] at H
  exact H

theorem canon (n : Nat) : run0 table (6+2*n) ⟨2,([false,true,false,false]) ++ (rep [false,false] (n)) ++ ([true,false,false]),[]⟩ = some ⟨4,([false,false,false,false,true,false,false]),(rep [true,true] (n)) ++ ([false])⟩ := by
  exact epoch n

end MInit


namespace MFinish

-- 1RB0RB_1RC0LE_0RD1LD_1LD0RA_1LE0LF_1LC---

def table : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 0,true => some (some ⟨false,true,1⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 1,true => some (some ⟨false,false,4⟩)
  | 2,false => some (some ⟨false,true,3⟩)
  | 2,true => some (some ⟨true,false,3⟩)
  | 3,false => some (some ⟨true,false,3⟩)
  | 3,true => some (some ⟨false,true,0⟩)
  | 4,false => some (some ⟨true,false,4⟩)
  | 4,true => some (some ⟨false,false,5⟩)
  | 5,false => some (some ⟨true,false,2⟩)
  | _,_ => none

theorem phase0 (n : Nat) : run0 table 33 ⟨4,([false,false,false,false,true,false,false]),(rep [false,true] (n)) ++ ([false])⟩ = some ⟨1,([false,true,false,false]),([true,false,true]) ++ (rep [false,true] (n)) ++ ([false])⟩ := by rfl

theorem local1 (L R : List Bool) : run0 table 4 ⟨1,([false]) ++ (L),([true,false,true]) ++ ([false,true]) ++ (R)⟩ = some ⟨1,([false]) ++ ([false,false]) ++ (L),([true,false,true]) ++ (R)⟩ := by rfl

theorem phase1 (n : Nat) : run0 table (4*n) ⟨1,([false,true,false,false]),([true,false,true]) ++ (rep [false,true] (n)) ++ ([false])⟩ = some ⟨1,([false]) ++ (rep [false,false] (n)) ++ ([true,false,false]),([true,false,true,false])⟩ := by
  simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using sweepR table 1 [false] [true,false,true] [false,true] [false,false] 4 local1 n (([true,false,false])) (([false]))

theorem phase2 (n : Nat) : run0 table 9 ⟨1,([false]) ++ (rep [false,false] (n)) ++ ([true,false,false]),([true,false,true,false])⟩ = some ⟨2,([false,true,false,false,false,false]) ++ (rep [false,false] (n)) ++ ([true,false,false]),[]⟩ := by rfl

theorem finalL (n : Nat) : ([false,true,false,false,false,false]) ++ (rep [false,false] (n)) ++ ([true,false,false]) = ([false,true,false,false]) ++ (rep [false,false] (n)) ++ ([false,false,true,false,false]) := by
  calc
    _ = ([false,true,false,false,false]) ++ (rep [false,false] (n)) ++ ([false,true,false,false]) := by simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using moveCut (([false,true,false,false,false])) (([true,false,false])) [false] false n
    _ = ([false,true,false,false]) ++ (rep [false,false] (n)) ++ ([false,false,true,false,false]) := by simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using moveCut (([false,true,false,false])) (([false,true,false,false])) [false] false n

theorem finalR (n : Nat) : ([] : List Bool) = [] := by
  rfl

theorem epoch (n : Nat) : run0 table (42+4*n) ⟨4,([false,false,false,false,true,false,false]),(rep [false,true] (n)) ++ ([false])⟩ = some ⟨2,([false,true,false,false]) ++ (rep [false,false] (n)) ++ ([false,false,true,false,false]),[]⟩ := by
  have H := (join0 (join0 (phase0 n) (phase1 n)) (phase2 n))
  rw [finalL n] at H
  rw [show 33+4*n+9=42+4*n by omega] at H
  exact H

theorem eq1l (n : Nat) : ([false,true,false,false]) ++ (rep [false,false] (n)) ++ ([false,false,true,false,false]) = ([false,true,false,false,false,false]) ++ (rep [false,false] (n)) ++ ([true,false,false]) := by
  calc
    _ = ([false,true,false,false,false]) ++ (rep [false,false] (n)) ++ ([false,true,false,false]) := by symm; simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using moveCut (([false,true,false,false])) (([false,true,false,false])) [false] false n
    _ = ([false,true,false,false,false,false]) ++ (rep [false,false] (n)) ++ ([true,false,false]) := by symm; simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using moveCut (([false,true,false,false,false])) (([true,false,false])) [false] false n

theorem canon (n : Nat) : run0 table (42+4*n) ⟨4,([false,false,false,false,true,false,false]),(rep [false,true] (n)) ++ ([false])⟩ = some ⟨2,([false,true,false,false,false,false]) ++ (rep [false,false] (n)) ++ ([true,false,false]),[]⟩ := by
  simpa only [eq1l n] using epoch n

end MFinish


namespace MCarry

-- 1RB0RB_1RC0LE_0RD1LD_1LD0RA_1LE0LF_1LC---

def table : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 0,true => some (some ⟨false,true,1⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 1,true => some (some ⟨false,false,4⟩)
  | 2,false => some (some ⟨false,true,3⟩)
  | 2,true => some (some ⟨true,false,3⟩)
  | 3,false => some (some ⟨true,false,3⟩)
  | 3,true => some (some ⟨false,true,0⟩)
  | 4,false => some (some ⟨true,false,4⟩)
  | 4,true => some (some ⟨false,false,5⟩)
  | 5,false => some (some ⟨true,false,2⟩)
  | _,_ => none

theorem phase0 (n : Nat) (R : List Bool) : run0 table 33 ⟨4,([false,false,false,false,true,false,false]),(rep [false,true] (n)) ++ ([false,true,true,true]) ++ (R)⟩ = some ⟨1,([false,true,false,false]),([true,false,true]) ++ (rep [false,true] (n)) ++ ([false,true,true,true]) ++ (R)⟩ := by rfl

theorem local1 (L R : List Bool) : run0 table 4 ⟨1,([false]) ++ (L),([true,false,true]) ++ ([false,true]) ++ (R)⟩ = some ⟨1,([false]) ++ ([false,false]) ++ (L),([true,false,true]) ++ (R)⟩ := by rfl

theorem phase1 (n : Nat) (R : List Bool) : run0 table (4*n) ⟨1,([false,true,false,false]),([true,false,true]) ++ (rep [false,true] (n)) ++ ([false,true,true,true]) ++ (R)⟩ = some ⟨1,([false]) ++ (rep [false,false] (n)) ++ ([true,false,false]),([true,false,true,false,true,true,true]) ++ (R)⟩ := by
  simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using sweepR table 1 [false] [true,false,true] [false,true] [false,false] 4 local1 n (([true,false,false])) (([false,true,true,true]) ++ (R))

theorem phase2 (n : Nat) (R : List Bool) : run0 table 13 ⟨1,([false]) ++ (rep [false,false] (n)) ++ ([true,false,false]),([true,false,true,false,true,true,true]) ++ (R)⟩ = some ⟨4,([false,false,false,false,false,false]) ++ (rep [false,false] (n)) ++ ([true,false,false]),([false,true]) ++ (R)⟩ := by rfl

theorem local3 (L R : List Bool) : run0 table 2 ⟨4,([false,false,false,false,false,false]) ++ ([false,false]) ++ (L),(R)⟩ = some ⟨4,([false,false,false,false,false,false]) ++ (L),([true,true]) ++ (R)⟩ := by rfl

theorem phase3 (n : Nat) (R : List Bool) : run0 table (2*n) ⟨4,([false,false,false,false,false,false]) ++ (rep [false,false] (n)) ++ ([true,false,false]),([false,true]) ++ (R)⟩ = some ⟨4,([false,false,false,false,false,false,true,false,false]),(rep [true,true] (n)) ++ ([false,true]) ++ (R)⟩ := by
  simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using sweepL table 4 [false,false,false,false,false,false] [] [false,false] [true,true] 2 local3 n (([true,false,false])) (([false,true]) ++ (R))

theorem phase4 (n : Nat) (R : List Bool) : run0 table 2 ⟨4,([false,false,false,false,false,false,true,false,false]),(rep [true,true] (n)) ++ ([false,true]) ++ (R)⟩ = some ⟨4,([false,false,false,false,true,false,false]),([true,true]) ++ (rep [true,true] (n)) ++ ([false,true]) ++ (R)⟩ := by rfl

theorem finalL (n : Nat) (R : List Bool) : ([false,false,false,false,true,false,false]) = ([false,false,false,false,true,false,false]) := by
  rfl

theorem finalR (n : Nat) (R : List Bool) : ([true,true]) ++ (rep [true,true] (n)) ++ ([false,true]) ++ (R) = (rep [true,true] (n)) ++ ([true,true,false,true]) ++ (R) := by
  calc
    _ = ([true]) ++ (rep [true,true] (n)) ++ ([true,false,true]) ++ (R) := by simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using moveCut (([true])) (([false,true]) ++ (R)) [true] true n
    _ = (rep [true,true] (n)) ++ ([true,true,false,true]) ++ (R) := by simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using moveCut ([]) (([true,false,true]) ++ (R)) [true] true n

theorem epoch (n : Nat) (R : List Bool) : run0 table (48+6*n) ⟨4,([false,false,false,false,true,false,false]),(rep [false,true] (n)) ++ ([false,true,true,true]) ++ (R)⟩ = some ⟨4,([false,false,false,false,true,false,false]),(rep [true,true] (n)) ++ ([true,true,false,true]) ++ (R)⟩ := by
  have H := (join0 (join0 (join0 (join0 (phase0 n R) (phase1 n R)) (phase2 n R)) (phase3 n R)) (phase4 n R))
  rw [finalR n R] at H
  rw [show 33+4*n+13+2*n+2=48+6*n by omega] at H
  exact H

theorem canon (n : Nat) (R : List Bool) : run0 table (48+6*n) ⟨4,([false,false,false,false,true,false,false]),(rep [false,true] (n)) ++ ([false,true,true,true]) ++ (R)⟩ = some ⟨4,([false,false,false,false,true,false,false]),(rep [true,true] (n)) ++ ([true,true,false,true]) ++ (R)⟩ := by
  exact epoch n R

end MCarry


abbrev table := MInit.table
abbrev A : List Bool := [false,true]
abbrev Z : List Bool := [true,true]
def Q (R : List Bool) : Z0 := ⟨4,[false,false,false,false,true,false,false],(R)⟩
def family (n : Nat) : Z0 := ⟨2,([false,true,false,false]) ++ (rep [false,false] (n)) ++ ([true,false,false]),[]⟩
def carryCost (n : Nat) : Nat := 42+6*n

theorem carry (n : Nat) (R : List Bool) : run0 table (carryCost n) (Q (rep A n ++ Z ++ R)) = some (Q (rep Z n ++ A ++ R)) := by
  cases n with
  | zero => rfl
  | succ n =>
    have h := MCarry.canon n R
    rw [show MCarry.table = table from rfl] at h
    unfold carryCost
    rw [show 42+6*n.succ = 48+6*n by omega]
    rw [rep_succ_snoc A n,rep_succ_snoc Z n]
    simpa only [table,Q,A,Z,List.append_assoc,List.nil_append,List.append_nil,List.cons_append] using h

theorem entry : run0 table 26 ⟨0,[],[]⟩ = some (family 0) := by rfl


def cost (n : Nat) : Nat := (6+2*n) + fillCost carryCost (n+0) + (42+4*n)
theorem growth (n : Nat) : run0 table (cost n) (family n) = some (family (n+1)) := by
  have h1 := MInit.canon n
  have h2 := fill table Q A Z carryCost carry (n+0) [false]
  have h3 := MFinish.canon n
  rw [rep_add Z n 0,rep_add A n 0] at h2
  simp only [Q,A,Z,rep,List.append_assoc,List.nil_append,List.append_nil,List.cons_append] at h2
  have h := join0 (join0 h1 h2) h3
  simpa only [cost,family,rep,rep_succ_snoc,List.append_assoc,List.nil_append,List.append_nil,List.cons_append] using h

theorem never (m : Machine) (hm : compatible table m) : NeverHalts m :=
  never_of_growth table family 26 cost entry (by intro n; unfold cost; omega) growth m hm

#print axioms growth
#print axioms never
end M61

end BB6.Agent11Raw39B0RBCounter61
