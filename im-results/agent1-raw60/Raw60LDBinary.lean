import SweepPumping
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace BB6.Agent1Raw60LDBinary
open BB6Coverage BB6Coverage.Agent31Pump
inductive V | d | e deriving DecidableEq

def table (v : V) : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 0,true => some (some ⟨false,false,3⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 2,false => some (some ⟨false,true,3⟩)
  | 2,true => some (some ⟨false,true,5⟩)
  | 3,false => some (some ⟨true,false,3⟩)
  | 3,true => some (some ⟨true,true,4⟩)
  | 4,false => some (some ⟨false,false,2⟩)
  | 4,true => some (some ⟨true,true,0⟩)
  | 5,false => some (some ⟨false,true,2⟩)
  | 5,true => some (some (match v with
      | .d => ⟨false,false,3⟩
      | .e => ⟨false,false,4⟩))
  | _,_ => none
abbrev Z : List Bool := [false,false]
abbrev K : List Bool := [true,true]
abbrev X : List Bool := [true,false]
abbrev C (L R : List Bool) : Z0 := ⟨2,L,R⟩
abbrev D (L R : List Bool) : Z0 := ⟨3,L,R⟩
abbrev F (L R : List Bool) : Z0 := ⟨5,L,R⟩
def w (n : Nat) (L : List Bool) := rep Z (n+1) ++ K ++ L

def resetCost (v : V) : Nat := match v with | .d => 2 | .e => 4

def T (v : V) : Nat → Nat
  | 0 => 8
  | n+1 => 2 * T v n + 6 + resetCost v

theorem base (v : V) (L R : List Bool) :
    run0 (table v) 8 (D (w 0 L) R) = some (F (w 0 L) R) := by cases v <;> rfl

theorem enter (v : V) (L R : List Bool) :
    run0 (table v) 2 (D (Z++L) R) = some (D L (K++R)) := by cases v <;> rfl

theorem first (v : V) (n : Nat) (L R : List Bool) :
    run0 (table v) 2 (F (w n L) (K++R)) = some (F (X++w n L) R) := by cases v <;> rfl

theorem reset (v : V) (n : Nat) (L R : List Bool) :
    run0 (table v) (resetCost v) (F (X++w n L) R) = some (D (w n L) (X++R)) := by cases v <;> rfl

theorem last (v : V) (n : Nat) (L R : List Bool) :
    run0 (table v) 2 (F (w n L) (X++R)) = some (F (w (n+1) L) R) := by cases v <;> rfl

theorem traverse (v : V) (n : Nat) (L R : List Bool) :
    run0 (table v) (T v n) (D (w n L) R) = some (F (w n L) R) := by
  induction n generalizing R with
  | zero => exact base v L R
  | succ n ih =>
    have h1 := enter v (w n L) R
    have h2 := ih (K++R)
    have h3 := first v n L R
    have h4 := reset v n L R
    have h5 := ih (X++R)
    have h6 := last v n L R
    have H := join0 (join0 (join0 (join0 (join0 h1 h2) h3) h4) h5) h6
    rw [show 2 + T v n + 2 + resetCost v + T v n + 2 = T v (n+1) by simp only [T]; omega] at H
    simpa only [w,rep,List.append_assoc] using H

def family (n : Nat) : Z0 := C (false :: (rep Z n ++ K)) []
def cost (v : V) (n : Nat) := T v n + 2

theorem entry (v : V) : run0 (table v) 2 ⟨0,[],[]⟩ = some (family 0) := by cases v <;> rfl

theorem growth (v : V) (n : Nat) :
    run0 (table v) (cost v n) (family n) = some (family (n+1)) := by
  have h1 : run0 (table v) 1 (family n) = some (D (w n []) []) := by cases v <;> simp only [family,w,rep,List.append_assoc,List.append_nil] <;> rfl
  have h2 := traverse v n [] []
  have h3 : run0 (table v) 1 (F (w n []) []) = some (family (n+1)) := by cases v <;> simp only [family,w,rep,List.append_assoc,List.append_nil] <;> rfl
  have H := join0 (join0 h1 h2) h3
  rw [show 1 + T v n + 1 = cost v n by unfold cost; omega] at H
  exact H

theorem positive (v : V) (n : Nat) : 0 < cost v n := by unfold cost; omega

theorem never (v : V) (m : Machine) (hm : compatible (table v) m) : NeverHalts m :=
  never_of_growth (table v) family 2 (cost v) (entry v) (positive v) (growth v) m hm

namespace M1398
abbrev table := _root_.BB6.Agent1Raw60LDBinary.table .d
theorem never (m : Machine) (hm : compatible table m) : NeverHalts m :=
  _root_.BB6.Agent1Raw60LDBinary.never .d m hm
end M1398
namespace M1399
abbrev table := _root_.BB6.Agent1Raw60LDBinary.table .e
theorem never (m : Machine) (hm : compatible table m) : NeverHalts m :=
  _root_.BB6.Agent1Raw60LDBinary.never .e m hm
end M1399
#print axioms traverse
#print axioms growth
#print axioms never
end BB6.Agent1Raw60LDBinary
