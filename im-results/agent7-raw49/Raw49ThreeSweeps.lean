import SweepPumping
set_option maxRecDepth 10000
set_option maxHeartbeats 0
namespace BB6.Agent7Raw49ThreeSweeps
open BB6Coverage BB6Coverage.Agent31Pump

namespace LeftE

def table : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 0,true => some (some ⟨false,true,0⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 1,true => some (some ⟨false,false,4⟩)
  | 2,false => some (some ⟨false,true,3⟩)
  | 2,true => some (some ⟨false,false,0⟩)
  | 3,false => some (some ⟨true,false,3⟩)
  | 3,true => some (some ⟨true,true,2⟩)
  | 4,false => some (some ⟨true,false,2⟩)
  | 4,true => some (some ⟨false,false,5⟩)
  | 5,false => some (some ⟨true,false,4⟩)
  | _,_ => none

def B (l r : List Bool) : Z0 := ⟨1,l,r⟩
def C (l r : List Bool) : Z0 := ⟨2,l,r⟩
def E (l r : List Bool) : Z0 := ⟨4,l,r⟩
def L : Nat → List Bool
  | 0 => [false,false]
  | n+1 => false :: true :: L n
def R : Nat → List Bool
  | 0 => [false]
  | n+1 => true :: false :: R n

def family (n : Nat) := B (true::true::L (n+2)) []

theorem enter (k : Nat) : run0 table 1 (B (true::true::L k) []) = some (E (true::L k) (R 0)) := by rfl
theorem lstep (k j : Nat) : run0 table 2 (E (true::L (k+1)) (R j)) = some (E (true::L k) (R (j+1))) := by rfl
theorem lscan (k j : Nat) : run0 table (2*k) (E (true::L k) (R j)) = some (E (true::L 0) (R (j+k))) := by
  induction k generalizing j with
  | zero => rfl
  | succ k ih =>
    have h := join0 (lstep k j) (ih (j+1))
    rw [show 2+2*k=2*(k+1) by omega,show j+1+k=j+(k+1) by omega] at h
    exact h
theorem lturn (j : Nat) : run0 table 3 (E (true::L 0) (R j)) = some (C [] (true::true::false::R j)) := by rfl
theorem rightStart (j : Nat) : run0 table 5 (C [] (true::true::false::R j)) = some (B (L 1) (R j)) := by rfl
theorem rstep (k j : Nat) : run0 table 4 (B (L (j+1)) (R (k+1))) = some (B (L (j+2)) (R k)) := by rfl
theorem rscan (k j : Nat) : run0 table (4*k) (B (L (j+1)) (R k)) = some (B (L (j+1+k)) (R 0)) := by
  induction k generalizing j with
  | zero => rfl
  | succ k ih =>
    have h := join0 (rstep k j) (ih (j+1))
    rw [show 4+4*k=4*(k+1) by omega,show j+1+1+k=j+1+(k+1) by omega] at h
    exact h
theorem finish (j : Nat) : run0 table 8 (B (L (j+1)) (R 0)) = some (B (true::true::L (j+1)) []) := by rfl
theorem epoch (k : Nat) : run0 table (6*k+17) (B (true::true::L k) []) = some (B (true::true::L (k+1)) []) := by
  have h := join0 (enter k) (lscan k 0)
  simp only [Nat.zero_add] at h
  have h := join0 h (lturn k)
  have h := join0 h (rightStart k)
  have h := join0 h (rscan k 0)
  rw [show 0+1+k=k+1 by omega] at h
  have h := join0 h (finish k)
  rw [show 1+2*k+3+5+4*k+8=6*k+17 by omega] at h
  exact h

theorem growth (n : Nat) : run0 table (6*n+29) (family n) = some (family (n+1)) := by
  have h := epoch (n+2)
  rw [show 6*(n+2)+17=6*n+29 by omega,show n+2+1=n+1+2 by omega] at h
  exact h
theorem entry : run0 table 32 ⟨0,[],[]⟩ = some (family 0) := by rfl
theorem never (m : Machine) (hm : compatible table m) : NeverHalts m :=
  never_of_growth table family 32 (fun n => 6*n+29) entry (by omega) growth m hm
#print axioms never
end LeftE

namespace RightE

def table (v : Bool) : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 0,true => some (some ⟨false,true,0⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 1,true => some (some ⟨v,true,4⟩)
  | 2,false => some (some ⟨false,true,3⟩)
  | 2,true => some (some ⟨false,false,0⟩)
  | 3,false => some (some ⟨true,false,3⟩)
  | 3,true => some (some ⟨true,true,2⟩)
  | 4,false => some (some ⟨true,false,5⟩)
  | 5,false => some (some ⟨v,false,if v then 3 else 5⟩)
  | 5,true => some (some ⟨false,false,if v then 5 else 3⟩)
  | _,_ => none

def B (l r : List Bool) : Z0 := ⟨1,l,r⟩
def C (l r : List Bool) : Z0 := ⟨2,l,r⟩
def Z : Nat → List Bool
  | 0 => []
  | n+1 => false :: Z n
def L (n : Nat) (tail : List Bool) : List Bool := rep [false,true] n ++ tail
def P (n : Nat) := false::false::true::L n []
def family (n : Nat) := B (false::true::Z (n+1)) (L (n+1) [])

theorem enter (v : Bool) (n : Nat) : run0 (table v) 1 (family n) = some (C (false::true::true::Z (n+1)) (true::L n [])) := by rfl
theorem rstep (v : Bool) (j k : Nat) (T : List Bool) : run0 (table v) 2 (C (L (j+1) T) (true::L (k+1) [])) = some (C (L (j+2) T) (true::L k [])) := by rfl
theorem rscan (v : Bool) (n j : Nat) (T : List Bool) : run0 (table v) (2*n) (C (L (j+1) T) (true::L n [])) = some (C (L (j+1+n) T) [true]) := by
  induction n generalizing j with
  | zero => rfl
  | succ n ih =>
    have h := join0 (rstep v j n T) (ih (j+1))
    rw [show 2+2*n=2*(n+1) by omega,show j+1+1+n=j+1+(n+1) by omega] at h
    exact h
theorem rlast (v : Bool) (j : Nat) (T : List Bool) : run0 (table v) 2 (C (L (j+1) T) [true]) = some (C (L (j+2) T) []) := by rfl
theorem turn (v : Bool) (j : Nat) (T : List Bool) : run0 (table v) 7 (C (L (j+1) T) []) = some (B (true::true::false::L j T) []) := by rfl

theorem lfirst (v : Bool) (j : Nat) (T : List Bool) : run0 (table v) 10 (B (true::true::false::L (j+1) T) []) = some (B (true::true::false::L j T) (P 0)) := by cases v <;> rfl
theorem lstep (v : Bool) (j k : Nat) (T : List Bool) : run0 (table v) 10 (B (true::true::false::L (j+1) T) (P k)) = some (B (true::true::false::L j T) (P (k+1))) := by cases v <;> rfl
theorem lscan (v : Bool) (n k : Nat) (T : List Bool) : run0 (table v) (10*n) (B (true::true::false::L n T) (P k)) = some (B (true::true::false::T) (P (k+n))) := by
  induction n generalizing k with
  | zero => rfl
  | succ n ih =>
    have h := join0 (lstep v n k T) (ih (k+1))
    rw [show 10+10*n=10*(n+1) by omega,show k+1+n=k+(n+1) by omega] at h
    exact h
theorem finish (v : Bool) (n k : Nat) : run0 (table v) 9 (B (true::true::false::true::Z (n+1)) (P k)) = some (B (false::true::Z (n+2)) (L (k+2) [])) := by cases v <;> rfl

theorem growth (v : Bool) (n : Nat) : run0 (table v) (12*n+29) (family n) = some (family (n+1)) := by
  have h := join0 (enter v n) (rscan v n 0 (true::Z (n+1)))
  rw [show 0+1+n=n+1 by omega] at h
  have h := join0 h (rlast v n (true::Z (n+1)))
  have h := join0 h (turn v (n+1) (true::Z (n+1)))
  have h := join0 h (lfirst v n (true::Z (n+1)))
  have h := join0 h (lscan v n 0 (true::Z (n+1)))
  simp only [Nat.zero_add] at h
  have h := join0 h (finish v n n)
  rw [show 1+2*n+2+7+10+10*n+9=12*n+29 by omega] at h
  exact h

theorem entry (v : Bool) : run0 (table v) 18 ⟨0,[],[]⟩ = some (family 0) := by cases v <;> rfl
theorem never (v : Bool) (m : Machine) (hm : compatible (table v) m) : NeverHalts m :=
  never_of_growth (table v) family 18 (fun n => 12*n+29) (entry v) (by omega) (growth v) m hm
#print axioms never
end RightE
end BB6.Agent7Raw49ThreeSweeps
