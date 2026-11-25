import SweepPumping
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace BB6.Agent1Raw60BCBinary
open BB6Coverage BB6Coverage.Agent31Pump
inductive V | lb | lc deriving DecidableEq

def table (v : V) : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 0,true => some (some (match v with | .lb => ⟨true,false,1⟩ | .lc => ⟨true,false,2⟩))
  | 1,false => some (some ⟨true,true,2⟩)
  | 1,true => match v with | .lb => some (some ⟨true,true,3⟩) | .lc => none
  | 2,false => some (some ⟨false,true,3⟩)
  | 2,true => match v with | .lb => none | .lc => some (some ⟨true,true,3⟩)
  | 3,false => some (some ⟨true,false,3⟩)
  | 3,true => some (some ⟨true,true,4⟩)
  | 4,false => some (some ⟨true,false,5⟩)
  | 4,true => some (some ⟨true,true,0⟩)
  | 5,false => some (some ⟨false,true,0⟩)
  | 5,true => some (some ⟨false,false,5⟩)
  | _,_ => none
abbrev E (L R : List Bool) : Z0 := ⟨4,L,R⟩
abbrev F (L R : List Bool) : Z0 := ⟨5,L,R⟩
abbrev U (k : Nat) := List.replicate k true
abbrev Z (k : Nat) := List.replicate k false

theorem repU (b : Bool) (n : Nat) : rep [b] n = List.replicate n b := by
  induction n <;> simp [rep,List.replicate_succ, *]

theorem clearOne (v : V) (L R : List Bool) :
    run0 (table v) 1 (F (true::L) R) = some (F L (false::R)) := by cases v <;> rfl

theorem clear (v : V) (k : Nat) (L R : List Bool) :
    run0 (table v) (k+1) (E (false::(U k++L)) R) = some (F L (Z k++true::R)) := by
  have h1 : run0 (table v) 1 (E (false::(U k++L)) R) = some (F (U k++L) (true::R)) := by cases v <;> rfl
  have h2 := sweepL (table v) 5 [] [] [true] [false] 1 (clearOne v) k L (true::R)
  simp only [List.nil_append,Nat.one_mul,repU] at h2
  have H := join0 h1 h2
  rw [Nat.add_comm 1 k] at H
  exact H

theorem fillBase (v : V) (b : Bool) (L R : List Bool) :
    run0 (table v) 11 (F (false::L) (Z 4++b::R)) = some (E (b::(U 4++false::L)) R) := by cases v <;> cases b <;> rfl

theorem turn (v : V) (b : Bool) (L R : List Bool) :
    run0 (table v) 11 (E (true::L) (Z 4++b::R)) = some (E (b::(U 5++L)) R) := by cases v <;> cases b <;> rfl

def P (n : Nat) := 5*n+4
def fillCost : Nat → Nat
  | 0 => 11
  | n+1 => 2*fillCost n + P n + 12

def traverseCost (n : Nat) := P n+1+fillCost n

def Fill (v : V) (n : Nat) : Prop := ∀ (b : Bool) (L R : List Bool),
  run0 (table v) (fillCost n) (F (false::L) (Z (P n)++b::R)) = some (E (b::(U (P n)++false::L)) R)

theorem traverseOfFill (v : V) (n : Nat) (h : Fill v n) (L R : List Bool) :
    run0 (table v) (traverseCost n) (E (false::(U (P n)++false::L)) R) = some (E (true::(U (P n)++false::L)) R) := by
  exact join0 (clear v (P n) (false::L) R) (h true L R)

theorem fill (v : V) (n : Nat) : Fill v n := by
  induction n with
  | zero => exact fillBase v
  | succ n ih =>
    intro b L R
    have h1 := ih false L (Z 4++b::R)
    have h2 := traverseOfFill v n ih L (Z 4++b::R)
    have h3 := turn v b (U (P n)++false::L) R
    have H := join0 (join0 h1 h2) h3
    rw [show fillCost n+traverseCost n+11=fillCost (n+1) by simp only [traverseCost,fillCost]; omega] at H
    have hp : P (n+1)=P n+5 := by simp [P]; omega
    have hL : Z (P n) ++ false :: (Z 4++b::R) = Z (P (n+1))++b::R := by
      rw [hp]
      have h : Z (P n) ++ Z 5 = Z (P n+5) := List.replicate_append_replicate
      rw [← h,List.append_assoc]; rfl
    have hR : U 5++(U (P n)++false::L) = U (P (n+1))++false::L := by
      rw [← List.append_assoc,List.replicate_append_replicate,hp,Nat.add_comm 5]
    rw [hL,hR] at H
    exact H

theorem traverse (v : V) (n : Nat) (L R : List Bool) :
    run0 (table v) (traverseCost n) (E (false::(U (P n)++false::L)) R) = some (E (true::(U (P n)++false::L)) R) := traverseOfFill v n (fill v n) L R

theorem turnBlank (v : V) (L : List Bool) :
    run0 (table v) 11 (E (true::L) []) = some (E (false::(U 5++L)) []) := by cases v <;> rfl

def family (n : Nat) := E (true::(U (P n)++[false])) []
def cost (n : Nat) := 11+traverseCost (n+1)

theorem growth (v : V) (n : Nat) : run0 (table v) (cost n) (family n) = some (family (n+1)) := by
  have h1 := turnBlank v (U (P n)++[false])
  have h2 := traverse v (n+1) [] []
  have h : U 5++(U (P n)++[false]) = U (P (n+1))++[false] := by
    rw [← List.append_assoc,List.replicate_append_replicate,show 5+P n=P (n+1) by simp [P]; omega]
  rw [h] at h1
  exact join0 h1 h2

theorem entry (v : V) : run0 (table v) 26 ⟨0,[],[]⟩ = some (family 0) := by cases v <;> rfl
theorem positive (n : Nat) : 0 < cost n := by unfold cost; omega
theorem never (v : V) (m : Machine) (hm : compatible (table v) m) : NeverHalts m := never_of_growth (table v) family 26 cost (entry v) positive (growth v) m hm
namespace M1039
abbrev table := _root_.BB6.Agent1Raw60BCBinary.table .lb
theorem never (m : Machine) (hm : compatible table m) : NeverHalts m := _root_.BB6.Agent1Raw60BCBinary.never .lb m hm
end M1039
namespace M580
abbrev table := _root_.BB6.Agent1Raw60BCBinary.table .lc
theorem never (m : Machine) (hm : compatible table m) : NeverHalts m := _root_.BB6.Agent1Raw60BCBinary.never .lc m hm
end M580
#print axioms fill
#print axioms traverse
#print axioms never
end BB6.Agent1Raw60BCBinary
