import SweepPumping
set_option maxRecDepth 100000
set_option maxHeartbeats 1000000
namespace BB6.Agent8Raw112Binary
open BB6Coverage BB6Coverage.Agent31Pump

-- Leaf 10554: 1RB0LF_1RC---_0RD1RA_1LD1RE_0RC1LC_0RA0LA
-- The sole unspecified row B1 is never queried.
def table : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 0,true => some (some ⟨false,false,5⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 2,false => some (some ⟨false,true,3⟩)
  | 2,true => some (some ⟨true,true,0⟩)
  | 3,false => some (some ⟨true,false,3⟩)
  | 3,true => some (some ⟨true,true,4⟩)
  | 4,false => some (some ⟨false,true,2⟩)
  | 4,true => some (some ⟨true,false,2⟩)
  | 5,false => some (some ⟨false,true,0⟩)
  | 5,true => some (some ⟨false,false,0⟩)
  | _,_ => none

abbrev Z : List Bool := [false,false,false,false]
abbrev O : List Bool := [true,true,true,true]
abbrev I : List Bool := [true,false,false,false]

def A (j : Nat) (R : List Bool) : Z0 :=
  ⟨0,false::(rep O j ++ [false]),false::false::R⟩

theorem onesComm (j : Nat) : true::(rep O j ++ [false]) = rep O j ++ [true,false] := by
  induction j with
  | zero => rfl
  | succ j ih => exact congrArg (fun x => true::true::true::true::x) ih

theorem zerosComm (j : Nat) (R : List Bool) :
    rep Z j ++ (false::false::R) = false::false::(rep Z j ++ R) := by
  induction j with
  | zero => rfl
  | succ j ih => exact congrArg (fun x => false::false::false::false::x) ih

theorem carryOne (j : Nat) (R : List Bool) :
    run0 table 22 (A j (I ++ R)) = some (A (j+1) R) := by rfl

theorem carryLast (j : Nat) :
    run0 table 22 (A j [true]) = some (A (j+1) []) := by rfl

theorem erase (j : Nat) (R : List Bool) :
    run0 table (4*j+2) ⟨0,rep O j ++ [true,false],R⟩ =
      some ⟨0,[false,false],rep Z j ++ R⟩ := by
  induction j generalizing R with
  | zero => rfl
  | succ j ih =>
    have h : run0 table 4 ⟨0,rep O (j+1) ++ [true,false],R⟩ =
        some ⟨0,rep O j ++ [true,false],Z ++ R⟩ := by rfl
    have g := join0 h (ih (Z ++ R))
    rw [show 4+(4*j+2)=4*(j+1)+2 by omega] at g
    rw [← List.append_assoc,rep_snoc] at g
    exact g

theorem zeroSetup (j : Nat) (R : List Bool) :
    run0 table 10 (A j (false::R)) =
      some ⟨0,rep O j ++ [true,false],false::false::true::R⟩ := by
  rw [← onesComm j]
  rfl

theorem zeroStep (j : Nat) (R : List Bool) :
    run0 table (4*j+12) (A j (Z ++ R)) =
      some (A 0 (rep Z j ++ I ++ R)) := by
  have g := join0 (zeroSetup j (false::false::false::R))
    (erase j (false::false::true::false::false::false::R))
  rw [show 10+(4*j+2)=4*j+12 by omega] at g
  rw [zerosComm] at g
  simpa only [A,rep,List.nil_append,Z,I,List.append_assoc,List.cons_append] using g

theorem zeroLast (j : Nat) :
    run0 table (4*j+12) (A j []) = some (A 0 (rep Z j ++ [true])) := by
  have h : run0 table 10 (A j []) =
      some ⟨0,true::(rep O j ++ [false]),[false,false,true]⟩ := by rfl
  rw [onesComm] at h
  have g := join0 h (erase j [false,false,true])
  rw [show 10+(4*j+2)=4*j+12 by omega,zerosComm] at g
  exact g

def ticks : Nat → Nat
  | 0 => 0
  | n+1 => ticks n + (4*n+12) + ticks n + 22

/-- Exhaust a finite low-order block of binary digits without inspecting its tail. -/
theorem fullCarry (n : Nat) (R : List Bool) :
    run0 table (ticks n) (A 0 (rep Z n ++ R)) = some (A n R) := by
  induction n generalizing R with
  | zero => rfl
  | succ n ih =>
    have e : rep Z (n+1) ++ R = rep Z n ++ (Z ++ R) := by
      rw [← List.append_assoc,rep_snoc];rfl
    rw [e]
    have h2 := zeroStep n R
    rw [List.append_assoc] at h2
    exact join0 (join0 (join0 (ih (Z ++ R)) h2) (ih (I ++ R))) (carryOne n R)

theorem ticks_formula (n : Nat) : ticks n + 4*n + 38 = 38*2^n := by
  induction n with
  | zero => decide
  | succ n ih => simp only [ticks,Nat.pow_succ]; omega

def family (n : Nat) : Z0 := A 0 (rep Z n ++ [true])

theorem entry : run0 table 12 ⟨0,[],[]⟩ = some (family 0) := by rfl

theorem growth (n : Nat) : run0 table (38*2^n) (family n) = some (family (n+1)) := by
  have h := join0 (join0 (fullCarry n [true]) (carryLast n)) (zeroLast (n+1))
  have e : ticks n+22+(4*(n+1)+12)=38*2^n := by have h := ticks_formula n; omega
  rw [e] at h
  exact h

theorem never (m : Machine) (hm : compatible table m) : NeverHalts m :=
  never_of_growth table family 12 (fun n => 38*2^n) entry
    (by intro n; have hp : 0 < 2^n := Nat.pow_pos (by decide); omega)
    growth m hm

#print axioms fullCarry
#print axioms ticks_formula
#print axioms growth
#print axioms never
end BB6.Agent8Raw112Binary
