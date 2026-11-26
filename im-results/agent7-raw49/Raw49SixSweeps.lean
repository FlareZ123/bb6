import SweepPumping
set_option maxRecDepth 10000
set_option maxHeartbeats 0
namespace BB6.Agent7Raw49SixSweeps
open BB6Coverage BB6Coverage.Agent31Pump

def alt01 : Nat → List Bool
  | 0 => []
  | n+1 => false :: true :: alt01 n

def alt10 : Nat → List Bool
  | 0 => []
  | n+1 => true :: false :: alt10 n

def C (l r : List Bool) : Z0 := ⟨2,l,r⟩
def E (l r : List Bool) : Z0 := ⟨4,l,r⟩
def A (l r : List Bool) : Z0 := ⟨0,l,r⟩
def B (l r : List Bool) : Z0 := ⟨1,l,r⟩

namespace Alternating
inductive Kind where | c3 | c8a | c8b
  deriving DecidableEq, Repr

def table (v : Kind) : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 0,true => some (some ⟨v != .c3,true,4⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 1,true => some (some (match v with | .c3 => ⟨true,false,5⟩ | .c8a => ⟨true,false,4⟩ | .c8b => ⟨false,false,2⟩))
  | 2,false => some (some ⟨false,true,3⟩)
  | 2,true => some (some ⟨false,false,0⟩)
  | 3,false => some (some ⟨true,false,3⟩)
  | 3,true => some (some ⟨true,true,2⟩)
  | 4,false => some (some ⟨true,true,if v = .c3 then 4 else 5⟩)
  | 4,true => some (some (match v with | .c3 => ⟨false,false,1⟩ | .c8a => ⟨false,false,2⟩ | .c8b => ⟨true,false,1⟩))
  | 5,false => if v = .c3 then some (some ⟨false,false,2⟩) else none
  | 5,true => if v = .c3 then none else some (some ⟨false,false,if v = .c8a then 1 else 4⟩)
  | _,_ => none

def family (n : Nat) := C [true] (false::alt10 (n+1))
def ls (k : Nat) := false::alt10 k ++ [true,true]

theorem enter (v : Kind) (k : Nat) : run0 (table v) 3 (C [true] (false::alt10 k)) = some (C (ls 0) (alt10 k)) := by cases v <;> rfl

theorem rightStep (v : Kind) (k j : Nat) : run0 (table v) 2 (C (ls j) (alt10 (k+1))) = some (C (ls (j+1)) (alt10 k)) := by cases v <;> rfl

theorem rightScan (v : Kind) (k j : Nat) : run0 (table v) (2*k) (C (ls j) (alt10 k)) = some (C (ls (j+k)) []) := by
  induction k generalizing j with
  | zero => rfl
  | succ k ih =>
    have h := join0 (rightStep v k j) (ih (j+1))
    rw [show 2+2*k=2*(k+1) by omega,show j+1+k=j+(k+1) by omega] at h
    exact h

theorem leftFirst (v : Kind) (k : Nat) : run0 (table v) 10 (C (ls (k+1)) []) = some (C (ls k) (false::alt10 1)) := by cases v <;> rfl

theorem leftStep (v : Kind) (k j : Nat) : run0 (table v) 10 (C (ls (k+1)) (false::alt10 j)) = some (C (ls k) (false::alt10 (j+1))) := by cases v <;> rfl

theorem leftScan (v : Kind) (k j : Nat) : run0 (table v) (10*k) (C (ls k) (false::alt10 j)) = some (C (ls 0) (false::alt10 (j+k))) := by
  induction k generalizing j with
  | zero => rfl
  | succ k ih =>
    have h := join0 (leftStep v k j) (ih (j+1))
    rw [show 10+10*k=10*(k+1) by omega,show j+1+k=j+(k+1) by omega] at h
    exact h

theorem finish (v : Kind) (j : Nat) : run0 (table v) 10 (C (ls 0) (false::alt10 j)) = some (C [true] (false::alt10 (j+1))) := by cases v <;> rfl

theorem growth (v : Kind) (n : Nat) : run0 (table v) (12*n+25) (family n) = some (family (n+1)) := by
  have h := join0 (enter v (n+1)) (rightScan v (n+1) 0)
  simp only [Nat.zero_add] at h
  have h := join0 h (leftFirst v n)
  have h := join0 h (leftScan v n 1)
  have h := join0 h (finish v (1+n))
  rw [show 3+2*(n+1)+10+10*n+10=12*n+25 by omega,show 1+n+1=n+1+1 by omega] at h
  exact h

theorem entry (v : Kind) : run0 (table v) 12 ⟨0,[],[]⟩ = some (family 0) := by cases v <;> rfl

theorem never (v : Kind) (m : Machine) (hm : compatible (table v) m) : NeverHalts m :=
  never_of_growth (table v) family 12 (fun n => 12*n+25) (entry v) (by omega) (growth v) m hm
#print axioms never
end Alternating

namespace EDouble

def table : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 0,true => some (some ⟨false,true,4⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 1,true => some (some ⟨false,false,4⟩)
  | 2,false => some (some ⟨false,true,3⟩)
  | 2,true => some (some ⟨false,false,0⟩)
  | 3,false => some (some ⟨true,false,3⟩)
  | 3,true => some (some ⟨true,true,2⟩)
  | 4,false => some (some ⟨true,true,1⟩)
  | 4,true => some (some ⟨true,false,5⟩)
  | 5,false => some (some ⟨false,false,4⟩)
  | _,_ => none

def family (n : Nat) := E [] (false::alt10 (2*n+2))
def lp (j : Nat) := false::false::true::alt01 j

theorem enter (k : Nat) : run0 table 4 (E [] (false::alt10 (k+1))) = some (E (lp 0) (false::alt10 k)) := by rfl

theorem rstep (j k : Nat) : run0 table 4 (E (lp j) (false::alt10 (k+1))) = some (E (lp (j+1)) (false::alt10 k)) := by rfl

theorem rscan (k j : Nat) : run0 table (4*k) (E (lp j) (false::alt10 k)) = some (E (lp (j+k)) [false]) := by
  induction k generalizing j with
  | zero => rfl
  | succ k ih =>
    have h := join0 (rstep j k) (ih (j+1))
    rw [show 4+4*k=4*(k+1) by omega,show j+1+k=j+(k+1) by omega] at h
    exact h

theorem turn (j : Nat) : run0 table 10 (E (lp j) [false]) = some (E (true::alt01 (j+2)) [false]) := by rfl

theorem lstep (k j : Nat) : run0 table 2 (E (true::alt01 (k+1)) (false::alt10 j)) = some (E (true::alt01 k) (false::alt10 (j+1))) := by rfl

theorem lscan (k j : Nat) : run0 table (2*k) (E (true::alt01 k) (false::alt10 j)) = some (E [true] (false::alt10 (j+k))) := by
  induction k generalizing j with
  | zero => rfl
  | succ k ih =>
    have h := join0 (lstep k j) (ih (j+1))
    rw [show 2+2*k=2*(k+1) by omega,show j+1+k=j+(k+1) by omega] at h
    exact h

theorem finish (j : Nat) : run0 table 2 (E [true] (false::alt10 j)) = some (E [] (false::alt10 (j+1))) := by rfl

theorem growth (n : Nat) : run0 table (12*n+26) (family n) = some (family (n+1)) := by
  have h := join0 (enter (2*n+1)) (rscan (2*n+1) 0)
  simp only [Nat.zero_add] at h
  have h := join0 h (turn (2*n+1))
  have h := join0 h (lscan (2*n+1+2) 0)
  simp only [Nat.zero_add] at h
  have h := join0 h (finish (2*n+1+2))
  rw [show 4+4*(2*n+1)+10+2*(2*n+1+2)+2=12*n+26 by omega,show 2*n+1+2+1=2*(n+1)+2 by omega] at h
  unfold family
  rw [show 2*n+2=2*n+1+1 by omega]
  exact h

theorem entry : run0 table 14 ⟨0,[],[]⟩ = some (family 0) := by rfl

theorem never (m : Machine) (hm : compatible table m) : NeverHalts m :=
  never_of_growth table family 14 (fun n => 12*n+26) entry (by omega) growth m hm
#print axioms never
end EDouble

namespace Ones

def table (v : Bool) : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 0,true => some (some ⟨true,false,0⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 1,true => some (some ⟨true,true,4⟩)
  | 2,false => some (some ⟨false,true,3⟩)
  | 2,true => some (some ⟨false,false,0⟩)
  | 3,false => some (some ⟨true,false,3⟩)
  | 3,true => some (some ⟨true,true,2⟩)
  | 4,true => some (some ⟨v,true,5⟩)
  | 5,false => some (some ⟨true,true,0⟩)
  | 5,true => some (some (if v then ⟨true,true,1⟩ else ⟨false,false,5⟩))
  | _,_ => none

def o : Nat → List Bool
  | 0 => []
  | n+1 => true :: o n

theorem oadd (j k : Nat) : o (j+k) = o j ++ o k := by
  induction j with
  | zero => simp [o]
  | succ j ih => rw [Nat.succ_add,o,ih]; rfl

-- Use a left scan with a right accumulator; the head cell belongs to l.
theorem lstep (v : Bool) (k j : Nat) (R : List Bool) :
    run0 (table v) 1 (A (o (k+1)) (o j ++ R)) = some (A (o k) (o (j+1) ++ R)) := by rfl

theorem lscan (v : Bool) (k j : Nat) (R : List Bool) :
    run0 (table v) k (A (o k) (o j ++ R)) = some (A [] (o (j+k) ++ R)) := by
  induction k generalizing j with
  | zero => rfl
  | succ k ih =>
    have h := join0 (lstep v k j R) (ih (j+1))
    rw [show 1+k=k+1 by omega,show j+1+k=j+(k+1) by omega] at h
    exact h

theorem startC (v : Bool) (k : Nat) : run0 (table v) 1 (C (o (k+1)) []) = some (A (o k) [false]) := by rfl

theorem startB (v : Bool) (k : Nat) (R : List Bool) : run0 (table v) 1 (A [] (o (k+1) ++ R)) = some (B (o 2) (o k ++ R)) := by rfl

theorem initial (v : Bool) (k : Nat) : run0 (table v) (k+3) (C (o (k+2)) []) = some (B (o 2) (o k ++ [false])) := by
  have h := join0 (startC v (k+1)) (lscan v (k+1) 0 [false])
  simp only [Nat.zero_add] at h
  have h := join0 h (startB v k [false])
  rw [show 1+(k+1)+1=k+3 by omega] at h
  exact h

theorem afterTurn (v : Bool) (k : Nat) : run0 (table v) (k+2) (A (o (k+1)) [false,true]) = some (B (o 2) (o k ++ [false,true])) := by
  have h := lscan v (k+1) 0 [false,true]
  simp only [Nat.zero_add] at h
  have h := join0 h (startB v k [false,true])
  exact h

def cost (v : Bool) : Nat := if v then 3 else 5

theorem rstep (v : Bool) (j k : Nat) (R : List Bool) : run0 (table v) (cost v) (B (o (j+2)) (o (k+3) ++ R)) = some (B (o (j+5)) (o k ++ R)) := by cases v <;> rfl

theorem rscan (v : Bool) (k j : Nat) (R : List Bool) :
    run0 (table v) (cost v*k) (B (o (j+2)) (o (3*k) ++ R)) = some (B (o (j+2+3*k)) R) := by
  induction k generalizing j with
  | zero => simp [run0,o]
  | succ k ih =>
    have h := join0 (rstep v j (3*k) R) (ih (j+3))
    rw [show cost v+cost v*k=cost v*(k+1) by simp [Nat.mul_succ,Nat.add_comm],show 3*k+3=3*(k+1) by omega,show j+3+2+3*k=j+2+3*(k+1) by omega] at h
    exact h

theorem turn0 (j : Nat) : run0 (table false) 11 (B (o (j+2)) [true,true,false]) = some (A (o (j+5)) [false,true]) := by rfl

theorem turn1 (j : Nat) : run0 (table true) 10 (B (o (j+2)) [true,false]) = some (A (o (j+6)) [false,true]) := by rfl

theorem finish0 (j : Nat) : run0 (table false) 26 (B (o (j+2)) [true,false,true]) = some (C (o (j+10)) []) := by rfl

theorem finish1 (j : Nat) : run0 (table true) 4 (B (o (j+2)) [true,true,false,true]) = some (C (o (j+6)) []) := by rfl

theorem epoch0 (m : Nat) : run0 (table false) (16*m+53) (C (o (3*m+4)) []) = some (C (o (3*m+13)) []) := by
  have h := initial false (3*m+2)
  rw [oadd (3*m) 2] at h
  simp only [o,List.append_assoc,List.cons_append,List.nil_append] at h
  -- retain the symbolic o(3*m); the simp above only unfolds the concrete word
  have s := rscan false m 0 [true,true,false]
  simp only [Nat.zero_add,cost] at s
  have h := join0 h s
  rw [show 2+3*m=3*m+2 by omega] at h
  have h := join0 h (turn0 (3*m))
  have h := join0 h (afterTurn false (3*m+4))
  rw [show 3*m+4=3*(m+1)+1 by omega,oadd (3*(m+1)) 1] at h
  simp only [o,List.append_assoc,List.cons_append,List.nil_append] at h
  have s := rscan false (m+1) 0 [true,false,true]
  simp only [Nat.zero_add,cost] at s
  have h := join0 h s
  rw [show 2+3*(m+1)=3*(m+1)+2 by omega] at h
  have h := join0 h (finish0 (3*(m+1)))
  simp only [Bool.false_eq_true,if_false] at h
  rw [show 3*m+2+3+5*m+11+(3*(m+1)+1+2)+5*(m+1)+26=16*m+53 by omega,show 3*(m+1)+10=3*m+13 by omega] at h
  exact h

theorem epoch1 (m : Nat) : run0 (table true) (12*m+28) (C (o (3*m+3)) []) = some (C (o (3*m+9)) []) := by
  have h := initial true (3*m+1)
  rw [oadd (3*m) 1] at h
  simp only [o,List.append_assoc,List.cons_append,List.nil_append] at h
  have s := rscan true m 0 [true,false]
  simp only [Nat.zero_add,cost] at s
  have h := join0 h s
  rw [show 2+3*m=3*m+2 by omega] at h
  have h := join0 h (turn1 (3*m))
  have h := join0 h (afterTurn true (3*m+5))
  rw [show 3*m+5=3*(m+1)+2 by omega,oadd (3*(m+1)) 2] at h
  simp only [o,List.append_assoc,List.cons_append,List.nil_append] at h
  have s := rscan true (m+1) 0 [true,true,false,true]
  simp only [Nat.zero_add,cost] at s
  have h := join0 h s
  rw [show 2+3*(m+1)=3*(m+1)+2 by omega] at h
  have h := join0 h (finish1 (3*(m+1)))
  simp only [if_true] at h
  rw [show 3*m+1+3+3*m+10+(3*(m+1)+2+2)+3*(m+1)+4=12*m+28 by omega,show 3*(m+1)+6=3*m+9 by omega] at h
  exact h

def family (v : Bool) (n : Nat) := C (o (if v then 6*n+12 else 9*n+10)) []
def entryTime (v : Bool) := if v then 52 else 36
def epochCost (v : Bool) (n : Nat) := if v then 24*n+64 else 48*n+85

theorem entry (v : Bool) : run0 (table v) (entryTime v) ⟨0,[],[]⟩ = some (family v 0) := by cases v <;> rfl

theorem growth (v : Bool) (n : Nat) : run0 (table v) (epochCost v n) (family v n) = some (family v (n+1)) := by
  cases v
  · have h := epoch0 (3*n+2)
    rw [show 16*(3*n+2)+53=48*n+85 by omega,show 3*(3*n+2)+4=9*n+10 by omega,show 3*(3*n+2)+13=9*(n+1)+10 by omega] at h
    exact h
  · have h := epoch1 (2*n+3)
    rw [show 12*(2*n+3)+28=24*n+64 by omega,show 3*(2*n+3)+3=6*n+12 by omega,show 3*(2*n+3)+9=6*(n+1)+12 by omega] at h
    exact h

theorem never (v : Bool) (m : Machine) (hm : compatible (table v) m) : NeverHalts m :=
  never_of_growth (table v) (family v) (entryTime v) (epochCost v) (entry v) (by cases v <;> intro k <;> simp [epochCost] <;> omega) (growth v) m hm
#print axioms never
end Ones
end BB6.Agent7Raw49SixSweeps
