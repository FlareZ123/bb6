import SweepPumping
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace BB6.Agent1Raw60LDTernary
open BB6Coverage BB6Coverage.Agent31Pump
inductive V | a | b deriving DecidableEq

def table (v : V) : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 0,true => some (some ⟨false,false,3⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 1,true => match v with | .a => some (some ⟨false,false,0⟩) | .b => none
  | 2,false => some (some ⟨false,true,3⟩)
  | 2,true => match v with | .a => none | .b => some (some ⟨false,false,0⟩)
  | 3,false => some (some ⟨true,false,3⟩)
  | 3,true => some (some ⟨true,true,4⟩)
  | 4,false => some (some ⟨true,false,5⟩)
  | 4,true => some (some ⟨true,true,0⟩)
  | 5,false => some (some (match v with | .a => ⟨false,true,0⟩ | .b => ⟨false,true,1⟩))
  | 5,true => some (some ⟨false,false,5⟩)
  | _,_ => none
abbrev J : List Bool := [true,true,true]
abbrev Z : List Bool := [false,false,false]
abbrev P : List Bool := [false,true,false]
abbrev B (L R : List Bool) : Z0 := ⟨1,L,R⟩
abbrev E (L R : List Bool) : Z0 := ⟨4,L,R⟩
abbrev F (L R : List Bool) : Z0 := ⟨5,L,R⟩
def seed (v : V) : List Bool := match v with | .a => [true] | .b => []
def u (v : V) (n : Nat) (L : List Bool) := rep J n ++ seed v ++ (false :: L)
def w (v : V) (n : Nat) (L : List Bool) := true :: u v n L
def b (v : V) (n : Nat) (L : List Bool) := false :: u v n L

def T (v : V) : Nat → Nat
  | 0 => match v with | .a => 4 | .b => 2
  | n+1 => 2 * T v n + 26

theorem base (v : V) (L R : List Bool) :
    run0 (table v) (T v 0) (F (w v 0 L) R) = some (B (b v 0 L) R) := by cases v <;> rfl

theorem enter (v : V) (n : Nat) (L R : List Bool) :
    run0 (table v) 3 (F (w v (n+1) L) R) = some (F (w v n L) (Z++R)) := by cases v <;> rfl

theorem reset (v : V) (U R : List Bool) :
    run0 (table v) 10 (B (false::U) (Z++R)) = some (F (true::U) (P++R)) := by cases v <;> rfl

theorem e_enter (v : V) (U R : List Bool) :
    run0 (table v) 3 (B (false::U) (P++R)) = some (E (P++(true::U)) R) := by cases v <;> rfl

theorem e_finish (v : V) (U R : List Bool) :
    run0 (table v) 10 (E (P++(true::U)) R) = some (B (false::(J++U)) R) := by cases v <;> rfl

theorem traverse (v : V) (n : Nat) (L R : List Bool) :
    run0 (table v) (T v n) (F (w v n L) R) = some (B (b v n L) R) := by
  induction n generalizing R with
  | zero => exact base v L R
  | succ n ih =>
    have h1 := enter v n L R
    have h2 := ih (Z++R)
    have h3 := reset v (u v n L) R
    have h4 := ih (P++R)
    have h5 := e_enter v (u v n L) R
    have h6 := e_finish v (u v n L) R
    have H := join0 (join0 (join0 (join0 (join0 h1 h2) h3) h4) h5) h6
    rw [show 3 + T v n + 10 + T v n + 3 + 10 = T v (n+1) by simp only [T]; omega] at H
    simpa only [b,u,rep,List.append_assoc] using H

theorem reset_blank (v : V) (U : List Bool) :
    run0 (table v) 10 (B (false::U) []) = some (F (true::U) [false,true]) := by cases v <;> rfl

theorem e_enter_blank (v : V) (U : List Bool) :
    run0 (table v) 3 (B (false::U) [false,true]) = some (E (P++(true::U)) []) := by cases v <;> rfl

def boundary (v : V) (n : Nat) (L : List Bool) := E (P++w v n L) []

theorem growBoundary (v : V) (n : Nat) (L : List Bool) :
    run0 (table v) (23 + T v (n+1)) (boundary v n L) = some (boundary v (n+1) L) := by
  have h1 : run0 (table v) 10 (boundary v n L) = some (B (b v (n+1) L) []) := by
    simpa only [boundary,w,b,u,rep,List.append_assoc] using e_finish v (u v n L) []
  have h2 := reset_blank v (u v (n+1) L)
  have h3 := traverse v (n+1) L [false,true]
  have h4 := e_enter_blank v (u v (n+1) L)
  have H := join0 (join0 (join0 h1 h2) h3) h4
  rw [show 10 + 10 + T v (n+1) + 3 = 23 + T v (n+1) by omega] at H
  exact H

def off (v : V) : Nat := match v with | .a => 0 | .b => 1
def tail (v : V) : List Bool := match v with | .a => [] | .b => [true,false]
def start (v : V) : Nat := match v with | .a => 18 | .b => 74
def family (v : V) (n : Nat) := boundary v (n + off v) (tail v)
def cost (v : V) (n : Nat) := 23 + T v (n+off v+1)
theorem entry (v : V) : run0 (table v) (start v) ⟨0,[],[]⟩ = some (family v 0) := by cases v <;> rfl
theorem growth (v : V) (n : Nat) :
    run0 (table v) (cost v n) (family v n) = some (family v (n+1)) := by
  simpa only [family,cost,show n+off v+1 = n+1+off v by omega] using growBoundary v (n+off v) (tail v)
theorem positive (v : V) (n : Nat) : 0 < cost v n := by unfold cost; omega
theorem never (v : V) (m : Machine) (hm : compatible (table v) m) : NeverHalts m :=
  never_of_growth (table v) (family v) (start v) (cost v) (entry v) (positive v) (growth v) m hm

namespace M1676
abbrev table := _root_.BB6.Agent1Raw60LDTernary.table .a
theorem never (m : Machine) (hm : compatible table m) : NeverHalts m :=
  _root_.BB6.Agent1Raw60LDTernary.never .a m hm
end M1676
namespace M1677
abbrev table := _root_.BB6.Agent1Raw60LDTernary.table .b
theorem never (m : Machine) (hm : compatible table m) : NeverHalts m :=
  _root_.BB6.Agent1Raw60LDTernary.never .b m hm
end M1677
#print axioms traverse
#print axioms growth
#print axioms never
end BB6.Agent1Raw60LDTernary
