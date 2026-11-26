import SweepPumping
set_option maxRecDepth 10000
set_option maxHeartbeats 0
namespace BB6.Agent7Raw49C7Sweeps
open BB6Coverage BB6Coverage.Agent31Pump

def ones : Nat → List Bool
  | 0 => []
  | n+1 => true :: ones n

def block100 : Nat → List Bool
  | 0 => []
  | n+1 => true :: false :: false :: block100 n

def block01 : Nat → List Bool
  | 0 => []
  | n+1 => false :: true :: block01 n

def block10 : Nat → List Bool
  | 0 => []
  | n+1 => true :: false :: block10 n

def B (l r : List Bool) : Z0 := ⟨1,l,r⟩
def C (l r : List Bool) : Z0 := ⟨2,l,r⟩
def E (l r : List Bool) : Z0 := ⟨4,l,r⟩

namespace Triple
inductive Kind where | a | b | c
  deriving DecidableEq, Repr

def table (v : Kind) : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 0,true => some (some ⟨true,true,0⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 1,true => some (some ⟨false,false,4⟩)
  | 2,false => some (some ⟨false,true,3⟩)
  | 2,true => some (some ⟨false,false,0⟩)
  | 3,false => some (some ⟨true,false,3⟩)
  | 3,true => some (some ⟨true,true,2⟩)
  | 4,false => some (some (if v = .a then ⟨false,false,0⟩ else ⟨true,false,1⟩))
  | 4,true => some (some ⟨v = .c,false,5⟩)
  | 5,true => some (some (if v = .c then ⟨false,true,1⟩ else ⟨true,false,1⟩))
  | _,_ => none

def family (n : Nat) := E [] (false::block100 (n+1))
def rb (j k : Nat) := B (false::ones (3*j+1)) (false::block100 k)
def le (j k : Nat) := E (ones (3*j)) (false::block100 k)
def rcost (v : Kind) : Nat := if v = .c then 19 else 17
def lcost (v : Kind) : Nat := if v = .c then 5 else 3

theorem enterA (k : Nat) : run0 (table .a) 2 (family k) = some (rb 0 (k+1)) := by rfl
theorem enterB (k : Nat) : run0 (table .b) 9 (family k) = some (rb 1 k) := by rfl
theorem enterC (k : Nat) : run0 (table .c) 9 (family k) = some (rb 1 k) := by rfl

theorem rstep (v : Kind) (j k : Nat) : run0 (table v) (rcost v) (rb j (k+1)) = some (rb (j+1) k) := by
  unfold rb
  rw [show 3*(j+1)+1=(3*j+1)+3 by omega]
  cases v <;> rfl

theorem rscan (v : Kind) (j k : Nat) : run0 (table v) (rcost v*k) (rb j k) = some (rb (j+k) 0) := by
  induction k generalizing j with
  | zero => simp [run0]
  | succ k ih =>
    have h := join0 (rstep v j k) (ih (j+1))
    rw [show rcost v+rcost v*k=rcost v*(k+1) by rw [Nat.mul_succ]; omega,show j+1+k=j+(k+1) by omega] at h
    exact h

theorem turn (v : Kind) (j : Nat) : run0 (table v) 9 (rb j 0) = some (le (j+1) 0) := by
  unfold rb le
  rw [show 3*(j+1)=3*j+3 by omega]
  cases v <;> rfl

theorem lstep (v : Kind) (j k : Nat) : run0 (table v) (lcost v) (le (j+1) k) = some (le j (k+1)) := by
  unfold le
  rw [show 3*(j+1)=3*j+3 by omega]
  cases v <;> rfl

theorem lscan (v : Kind) (j k : Nat) : run0 (table v) (lcost v*j) (le j k) = some (le 0 (k+j)) := by
  induction j generalizing k with
  | zero => simp [run0]
  | succ j ih =>
    have h := join0 (lstep v j k) (ih (k+1))
    rw [show lcost v+lcost v*j=lcost v*(j+1) by rw [Nat.mul_succ]; omega,show k+1+j=k+(j+1) by omega] at h
    exact h

def entryTime : Kind → Nat | .a => 13 | .b => 13 | .c => 15
def cost : Kind → Nat → Nat | .a,n => 20*n+34 | .b,n => 20*n+24 | .c,n => 24*n+28

theorem entry (v : Kind) : run0 (table v) (entryTime v) ⟨0,[],[]⟩ = some (family 0) := by cases v <;> rfl

theorem growth (v : Kind) (n : Nat) : run0 (table v) (cost v n) (family n) = some (family (n+1)) := by
  cases v with
  | a =>
    have h := join0 (enterA n) (rscan .a 0 (n+1))
    simp only [Nat.zero_add] at h
    have h := join0 h (turn .a (n+1))
    have h := join0 h (lscan .a (n+1+1) 0)
    simp only [Nat.zero_add,rcost,lcost,reduceCtorEq,ite_false] at h
    rw [show 2+17*(n+1)+9+3*(n+1+1)=20*n+34 by omega] at h
    exact h
  | b =>
    have h := join0 (enterB n) (rscan .b 1 n)
    rw [show 1+n=n+1 by omega] at h
    have h := join0 h (turn .b (n+1))
    have h := join0 h (lscan .b (n+1+1) 0)
    simp only [Nat.zero_add,rcost,lcost,reduceCtorEq,ite_false] at h
    rw [show 9+17*n+9+3*(n+1+1)=20*n+24 by omega] at h
    exact h
  | c =>
    have h := join0 (enterC n) (rscan .c 1 n)
    rw [show 1+n=n+1 by omega] at h
    have h := join0 h (turn .c (n+1))
    have h := join0 h (lscan .c (n+1+1) 0)
    simp only [Nat.zero_add,rcost,lcost,ite_true] at h
    rw [show 9+19*n+9+5*(n+1+1)=24*n+28 by omega] at h
    exact h

theorem never (v : Kind) (m : Machine) (hm : compatible (table v) m) : NeverHalts m :=
  never_of_growth (table v) family (entryTime v) (cost v) (entry v) (by cases v <;> simp [cost] <;> omega) (growth v) m hm
#print axioms never
end Triple

namespace Double

def table (v : Bool) : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 0,true => some (some ⟨true,true,0⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 1,true => some (some ⟨true,false,4⟩)
  | 2,false => some (some ⟨false,true,3⟩)
  | 2,true => some (some ⟨false,false,0⟩)
  | 3,false => some (some ⟨true,false,3⟩)
  | 3,true => some (some ⟨true,true,2⟩)
  | 4,false => some (some ⟨v,false,5⟩)
  | 4,true => some (some ⟨false,false,1⟩)
  | 5,true => some (some ⟨v,false,1⟩)
  | _,_ => none

def family (n : Nat) := C [false,true] (true::false::true::true::block01 (2*n+1))
def rb (j k : Nat) := B (false::ones (2*j+2) ++ [false,true,false,true]) (block10 k ++ [true])
def le (j k : Nat) := E (ones (2*j) ++ [false,true,false,true]) (true::block01 k)

theorem blocks (k : Nat) : true::block01 k = block10 k ++ [true] := by
  induction k with
  | zero => rfl
  | succ k ih =>
    change true::false::true::block01 k = true::false::(block10 k ++ [true])
    rw [← ih]

theorem enter (v : Bool) (k : Nat) : run0 (table v) 7 (C [false,true] (true::false::true::true::block01 (k+1))) = some (rb 0 k) := by
  unfold rb
  rw [← blocks]
  cases v <;> rfl

theorem rstep (v : Bool) (j k : Nat) : run0 (table v) 4 (rb j (k+1)) = some (rb (j+1) k) := by
  unfold rb
  rw [show 2*(j+1)+2=(2*j+2)+2 by omega]
  cases v <;> rfl

theorem rscan (v : Bool) (j k : Nat) : run0 (table v) (4*k) (rb j k) = some (rb (j+k) 0) := by
  induction k generalizing j with
  | zero => rfl
  | succ k ih =>
    have h := join0 (rstep v j k) (ih (j+1))
    rw [show 4+4*k=4*(k+1) by omega,show j+1+k=j+(k+1) by omega] at h
    exact h

theorem turn (v : Bool) (j : Nat) : run0 (table v) 13 (rb j 0) = some (le (j+3) 0) := by
  unfold rb le
  rw [show 2*(j+3)=(2*j+2)+4 by omega]
  cases v <;> rfl

theorem lstep (v : Bool) (j k : Nat) : run0 (table v) 2 (le (j+1) k) = some (le j (k+1)) := by
  unfold le
  rw [show 2*(j+1)=2*j+2 by omega]
  cases v <;> rfl

theorem lscan (v : Bool) (j k : Nat) : run0 (table v) (2*j) (le j k) = some (le 0 (k+j)) := by
  induction j generalizing k with
  | zero => rfl
  | succ j ih =>
    have h := join0 (lstep v j k) (ih (k+1))
    rw [show 2+2*j=2*(j+1) by omega,show k+1+j=k+(j+1) by omega] at h
    exact h

def fcost (v : Bool) : Nat := if v then 11 else 15

theorem finish (v : Bool) (k : Nat) : run0 (table v) (fcost v) (le 0 k) = some (C [false,true] (true::false::true::true::block01 k)) := by cases v <;> rfl

def entryTime (v : Bool) : Nat := if v then 39 else 43
def cost (v : Bool) (n : Nat) : Nat := 12*n+26+fcost v

theorem entry (v : Bool) : run0 (table v) (entryTime v) ⟨0,[],[]⟩ = some (family 0) := by cases v <;> rfl

theorem growth (v : Bool) (n : Nat) : run0 (table v) (cost v n) (family n) = some (family (n+1)) := by
  have h := join0 (enter v (2*n)) (rscan v 0 (2*n))
  simp only [Nat.zero_add] at h
  have h := join0 h (turn v (2*n))
  have h := join0 h (lscan v (2*n+3) 0)
  simp only [Nat.zero_add] at h
  have h := join0 h (finish v (2*n+3))
  rw [show 7+4*(2*n)+13+2*(2*n+3)+fcost v=cost v n by unfold cost; omega,show 2*n+3=2*(n+1)+1 by omega] at h
  exact h

theorem never (v : Bool) (m : Machine) (hm : compatible (table v) m) : NeverHalts m :=
  never_of_growth (table v) family (entryTime v) (cost v) (entry v) (by unfold cost; omega) (growth v) m hm
#print axioms never
end Double
end BB6.Agent7Raw49C7Sweeps
