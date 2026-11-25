import SweepPumping
set_option maxRecDepth 100000
set_option maxHeartbeats 1000000
namespace BB6.Agent8Raw112Quinary
open BB6Coverage BB6Coverage.Agent31Pump

-- Leaf 12597: 1RB0RB_1RC---_0RD1RF_1LD1RE_0RA1LC_1LE0LF
-- Five-cell encoding of a binary counter with a moving return marker.
def table : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 0,true => some (some ⟨false,true,1⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 2,false => some (some ⟨false,true,3⟩)
  | 2,true => some (some ⟨true,true,5⟩)
  | 3,false => some (some ⟨true,false,3⟩)
  | 3,true => some (some ⟨true,true,4⟩)
  | 4,false => some (some ⟨false,true,0⟩)
  | 4,true => some (some ⟨true,false,2⟩)
  | 5,false => some (some ⟨true,false,4⟩)
  | 5,true => some (some ⟨false,false,5⟩)
  | _,_ => none

abbrev P : List Bool := [true,false,true,true,false]
abbrev Q : List Bool := [true,false,true,false,false]
abbrev D0 : List Bool := [false,false,true,false,false]
abbrev D1 : List Bool := [false,false,false,true,false]
abbrev S : List Bool := [false,false,false,true]

def root (b : Bool) (R : List Bool) : Z0 :=
  ⟨4,[false],true::false::false::b::false::R⟩
def carry (n : Nat) (R : List Bool) : Z0 :=
  ⟨4,false::(rep P n ++ Q),R⟩
def returning (n : Nat) (R : List Bool) : Z0 :=
  ⟨4,rep P n ++ Q,true::R⟩

theorem rootZero (R : List Bool) :
    run0 table 12 (root false R) = some (root true R) := by rfl
theorem rootOne (R : List Bool) :
    run0 table 5 (root true R) = some (carry 0 R) := by rfl
theorem carryOne (n : Nat) (R : List Bool) :
    run0 table 5 (carry n (D1 ++ R)) = some (carry (n+1) R) := by rfl
theorem carryLast (n : Nat) :
    run0 table 5 (carry n S) = some (carry (n+1) []) := by rfl
theorem carryZeroSetup (n : Nat) (R : List Bool) :
    run0 table 11 (carry n (D0 ++ R)) = some (returning n (D1 ++ R)) := by rfl
theorem finishSetup (n : Nat) :
    run0 table 13 (carry n []) = some (returning n S) := by rfl

theorem sweep (n : Nat) (R : List Bool) :
    run0 table (13*n+16) (returning n R) = some (root false (rep D0 n ++ R)) := by
  induction n generalizing R with
  | zero => rfl
  | succ n ih =>
    have h : run0 table 13 (returning (n+1) R) = some (returning n (D0 ++ R)) := by rfl
    have g := join0 h (ih (D0 ++ R))
    rw [show 13+(13*n+16)=13*(n+1)+16 by omega] at g
    rw [← List.append_assoc,rep_snoc] at g
    exact g

theorem carryZero (n : Nat) (R : List Bool) :
    run0 table (13*n+27) (carry n (D0 ++ R)) =
      some (root false (rep D0 n ++ (D1 ++ R))) := by
  have g := join0 (carryZeroSetup n R) (sweep n (D1 ++ R))
  rw [show 11+(13*n+16)=13*n+27 by omega] at g
  exact g

theorem finish (n : Nat) :
    run0 table (13*n+29) (carry n []) = some (root false (rep D0 n ++ S)) := by
  have g := join0 (finishSetup n) (sweep n S)
  rw [show 13+(13*n+16)=13*n+29 by omega] at g
  exact g

def ticks : Nat → Nat
  | 0 => 17
  | n+1 => ticks n + (13*n+27) + ticks n + 5

theorem fullCarry (n : Nat) (R : List Bool) :
    run0 table (ticks n) (root false (rep D0 n ++ R)) = some (carry n R) := by
  induction n generalizing R with
  | zero => exact join0 (rootZero R) (rootOne R)
  | succ n ih =>
    have e : rep D0 (n+1) ++ R = rep D0 n ++ (D0 ++ R) := by
      rw [← List.append_assoc,rep_snoc];rfl
    rw [e]
    exact join0 (join0 (join0 (ih (D0 ++ R)) (carryZero n R)) (ih (D1 ++ R))) (carryOne n R)

theorem ticks_formula (n : Nat) : ticks n + 13*n + 45 = 62*2^n := by
  induction n with
  | zero => decide
  | succ n ih => simp only [ticks,Nat.pow_succ]; omega

def family (n : Nat) : Z0 := carry n []
theorem entry : run0 table 59 ⟨0,[],[]⟩ = some (family 0) := by rfl

theorem growth (n : Nat) : run0 table (62*2^n-11) (family n) = some (family (n+1)) := by
  have h := join0 (join0 (finish n) (fullCarry n S)) (carryLast n)
  have e : 13*n+29+ticks n+5=62*2^n-11 := by have h := ticks_formula n; omega
  rw [e] at h
  exact h

theorem never (m : Machine) (hm : compatible table m) : NeverHalts m :=
  never_of_growth table family 59 (fun n => 62*2^n-11) entry
    (by intro n; have hp : 0 < 2^n := Nat.pow_pos (by decide); omega)
    growth m hm

#print axioms fullCarry
#print axioms ticks_formula
#print axioms growth
#print axioms never
end BB6.Agent8Raw112Quinary
