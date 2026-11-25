import SweepPumping
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace BB6.Agent1Raw60LFTriple
open BB6Coverage BB6Coverage.Agent31Pump
inductive V | a | b | c deriving DecidableEq

def table (v : V) : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 0,true => some (some ⟨true,false,5⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 1,true => match v with | .c => none | _ => some (some ⟨false,false,3⟩)
  | 2,false => some (some ⟨false,true,3⟩)
  | 2,true => match v with | .c => some (some ⟨false,false,3⟩) | _ => none
  | 3,false => some (some ⟨true,false,3⟩)
  | 3,true => some (some ⟨true,true,4⟩)
  | 4,false => some (some (match v with | .a => ⟨false,false,0⟩ | .b => ⟨false,false,1⟩ | .c => ⟨false,false,2⟩))
  | 4,true => some (some ⟨true,true,0⟩)
  | 5,false => some (some ⟨false,true,1⟩)
  | 5,true => some (some ⟨false,false,5⟩)
  | _,_ => none
abbrev D (L R : List Bool) : Z0 := ⟨3,L,R⟩
abbrev F (L R : List Bool) : Z0 := ⟨5,L,R⟩
abbrev U (k : Nat) := List.replicate k true
abbrev Z (k : Nat) := List.replicate k false

def P (n : Nat) := 3*n+2
def extra (v : V) : Nat := match v with | .a => 11 | _ => 9

theorem clear (v : V) (k : Nat) (L R : List Bool) :
    run0 (table v) k (F (U k++L) R) = some (F L (Z k++R)) := by
  induction k generalizing R with
  | zero => rfl
  | succ k ih =>
    have h1 : run0 (table v) 1 (F (U (k+1)++L) R) = some (F (U k++L) (false::R)) := by cases v <;> rfl
    have H := join0 h1 (ih (false::R))
    rw [Nat.add_comm 1 k] at H
    simpa only [List.replicate_succ' (n:=k) (a:=false),List.append_assoc,List.singleton_append] using H

theorem turn (v : V) (L R : List Bool) :
    run0 (table v) 5 (D (false::false::true::L) R) = some (F (true::true::L) (true::R)) := by cases v <;> rfl

theorem finish (v : V) (b : Bool) (L R : List Bool) :
    run0 (table v) (extra v) (D (true::false::true::L) (false::false::b::R)) =
      some (D (b::false::(U 4++L)) R) := by cases v <;> cases b <;> rfl

def T (v : V) : Nat → Nat
  | 0 => 3
  | n+1 => 2*T v n+5+P n+extra v

theorem fill (v : V) (n : Nat) (b : Bool) (L R : List Bool) :
    run0 (table v) (T v n) (F (false::L) (Z (P n)++b::R)) =
      some (D (b::false::(U (P n-1)++false::L)) R) := by
  induction n generalizing b L R with
  | zero => cases v <;> cases b <;> rfl
  | succ n ih =>
    have h1 := ih false L (false::false::b::R)
    have h2 := turn v (U (P n-2)++false::L) (false::false::b::R)
    have h3 := clear v (P n) (false::L) (true::false::false::b::R)
    have h4 := ih true L (false::false::b::R)
    have h5 := finish v b (U (P n-2)++false::L) R
    have hu : true::(U (P n-2)++false::L) = U (P n-1)++false::L := by
      rw [show P n-1=(P n-2)+1 by unfold P; omega]; rfl
    have hv : true::true::(U (P n-2)++false::L) = U (P n)++false::L := by
      rw [show P n=(P n-2)+1+1 by unfold P; omega]; rfl
    rw [hv,hu] at h2
    rw [hu] at h5
    have H := join0 (join0 (join0 (join0 h1 h2) h3) h4) h5
    rw [show T v n+5+P n+T v n+extra v=T v (n+1) by simp only [T]; omega] at H
    have hl : Z (P n)++false::false::false::b::R = Z (P (n+1))++b::R := by
      change List.replicate (P n) false ++ false::false::false::b::R = List.replicate (P (n+1)) false ++ b::R
      rw [show P (n+1)=P n+3 by unfold P; omega,← List.replicate_append_replicate,List.append_assoc]; rfl
    have hr : U 4++(U (P n-2)++false::L) = U (P (n+1)-1)++false::L := by
      rw [← List.append_assoc,List.replicate_append_replicate,show 4+(P n-2)=P (n+1)-1 by unfold P; omega]
    rw [hl,hr] at H
    exact H

theorem turnBlank (v : V) (L : List Bool) :
    run0 (table v) 5 (D (false::false::true::L) []) = some (F (true::true::L) [true]) := by cases v <;> rfl

theorem finishBlank (v : V) (L : List Bool) :
    run0 (table v) (extra v) (D (true::false::true::L) []) = some (D (false::false::(U 4++L)) []) := by cases v <;> rfl

def family (n : Nat) : Z0 := D (false::false::(U (3*n+4)++[false,true,false])) []
def cost (v : V) (n : Nat) := 5+P (n+1)+T v (n+1)+extra v

theorem growth (v : V) (n : Nat) : run0 (table v) (cost v n) (family n) = some (family (n+1)) := by
  have h1 := turnBlank v (U (3*n+3)++[false,true,false])
  have h2 := clear v (P (n+1)) [false,true,false] [true]
  have h3 := fill v (n+1) true [true,false] []
  have h4 := finishBlank v (U (3*n+3)++[false,true,false])
  have hu : true::true::(U (3*n+3)++[false,true,false]) = U (P (n+1))++[false,true,false] := by
    rw [show P (n+1)=3*n+3+1+1 by unfold P; omega]; rfl
  rw [hu] at h1
  have hv : P (n+1)-1=3*n+4 := by unfold P; omega
  rw [hv] at h3
  have hl : true::(U (3*n+3)++[false,true,false]) = U (3*n+4)++[false,true,false] := by rfl
  rw [hl] at h4
  have H := join0 (join0 (join0 h1 h2) h3) h4
  unfold family cost
  have hr : U 4++(U (3*n+3)++[false,true,false]) = U (3*(n+1)+4)++[false,true,false] := by
    rw [← List.append_assoc,List.replicate_append_replicate,show 4+(3*n+3)=3*(n+1)+4 by omega]
  rw [hr] at H
  exact H

theorem entry (v : V) : run0 (table v) 29 ⟨0,[],[]⟩ = some (family 0) := by cases v <;> rfl
theorem positive (v : V) (n : Nat) : 0 < cost v n := by unfold cost; omega
theorem never (v : V) (m : Machine) (hm : compatible (table v) m) : NeverHalts m :=
  never_of_growth (table v) family 29 (cost v) (entry v) (positive v) (growth v) m hm

namespace M782
abbrev table := _root_.BB6.Agent1Raw60LFTriple.table .a
theorem never (m : Machine) (hm : compatible table m) : NeverHalts m := _root_.BB6.Agent1Raw60LFTriple.never .a m hm
end M782
namespace M783
abbrev table := _root_.BB6.Agent1Raw60LFTriple.table .b
theorem never (m : Machine) (hm : compatible table m) : NeverHalts m := _root_.BB6.Agent1Raw60LFTriple.never .b m hm
end M783
namespace M784
abbrev table := _root_.BB6.Agent1Raw60LFTriple.table .c
theorem never (m : Machine) (hm : compatible table m) : NeverHalts m := _root_.BB6.Agent1Raw60LFTriple.never .c m hm
end M784
#print axioms never
#print axioms fill
#print axioms growth
#print axioms entry
end BB6.Agent1Raw60LFTriple
