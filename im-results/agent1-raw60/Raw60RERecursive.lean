import SweepPumping

set_option maxRecDepth 100000

set_option maxHeartbeats 0

namespace BB6.Agent1Raw60RERecursive

open BB6Coverage BB6Coverage.Agent31Pump

inductive V | m327 | m328 | m454 | m455 | m663 | m664 | m665 | m666 | m667 | m668 | m669 | m670 | m671 | m672 | m673 | m674 | m675 | m676 | m677 | m678 | m679 | m680 | m681 | m682 | m683 | m684 deriving DecidableEq

def table (v : V) : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 0,true => some (some ⟨true,true,4⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 1,true => match v with | .m327 | .m328 | .m666 | .m676 => some (some ⟨false,false,5⟩) | .m454 | .m455 | .m663 => none | .m664 => some (some ⟨false,false,1⟩) | .m665 | .m675 => some (some ⟨false,false,4⟩) | .m667 => some (some ⟨false,true,1⟩) | .m668 | .m678 => some (some ⟨false,true,5⟩) | .m669 | .m679 => some (some ⟨true,false,0⟩) | .m670 | .m680 => some (some ⟨true,false,3⟩) | .m671 | .m681 => some (some ⟨true,true,0⟩) | .m672 | .m682 => some (some ⟨true,true,1⟩) | .m673 | .m683 => some (some ⟨true,true,2⟩) | .m674 | .m684 => some (some ⟨true,true,5⟩) | .m677 => some (some ⟨false,true,4⟩)
  | 2,false => some (some ⟨false,true,3⟩)
  | 2,true => match v with | .m327 | .m328 | .m663 | .m664 | .m665 | .m666 | .m667 | .m668 | .m669 | .m670 | .m671 | .m672 | .m673 | .m674 | .m675 | .m676 | .m677 | .m678 | .m679 | .m680 | .m681 | .m682 | .m683 | .m684 => none | .m454 | .m455 => some (some ⟨false,false,5⟩)
  | 3,false => some (some ⟨true,false,3⟩)
  | 3,true => some (some ⟨true,true,4⟩)
  | 4,false => match v with | .m327 | .m328 => some (some ⟨true,false,1⟩) | .m454 | .m455 => some (some ⟨true,false,2⟩) | .m663 | .m664 | .m665 | .m666 | .m667 | .m668 | .m669 | .m670 | .m671 | .m672 | .m673 | .m674 | .m675 | .m676 | .m677 | .m678 | .m679 | .m680 | .m681 | .m682 | .m683 | .m684 => some (some ⟨true,false,5⟩)
  | 4,true => some (some ⟨true,true,0⟩)
  | 5,false => match v with | .m327 | .m454 | .m663 => some (some ⟨false,true,0⟩) | .m328 | .m664 | .m665 | .m666 | .m667 | .m668 | .m669 | .m670 | .m671 | .m672 | .m673 | .m674 => some (some ⟨false,true,1⟩) | .m455 | .m675 | .m676 | .m677 | .m678 | .m679 | .m680 | .m681 | .m682 | .m683 | .m684 => some (some ⟨false,true,4⟩)
  | 5,true => some (some ⟨false,false,5⟩)
  | _,_ => none

def p (v : V) : Nat := match v with
  | .m327 | .m454 | .m663 => 4
  | .m328 | .m664 | .m665 | .m666 | .m667 | .m668 | .m669 | .m670 | .m671 | .m672 | .m673 | .m674 => 3
  | .m455 => 1
  | .m675 | .m676 | .m677 | .m678 | .m679 | .m680 | .m681 | .m682 | .m683 | .m684 => 5

def baseCost (v : V) : Nat := match v with
  | .m327 | .m454 | .m663 => 9
  | .m328 | .m664 | .m665 | .m666 | .m667 | .m668 | .m669 | .m670 | .m671 | .m672 | .m673 | .m674 => 8
  | .m455 => 4
  | .m675 | .m676 | .m677 | .m678 | .m679 | .m680 | .m681 | .m682 | .m683 | .m684 => 12

def kind (v : V) : Nat := match v with
  | .m327 | .m328 | .m454 | .m455 | .m663 | .m664 | .m666 | .m667 | .m668 | .m673 | .m674 | .m676 | .m677 | .m678 | .m683 | .m684 => 0
  | .m665 | .m672 | .m675 | .m682 => 2
  | .m669 | .m670 | .m671 | .m679 | .m680 | .m681 => 1

def tailCost (v : V) : Nat := match v with
  | .m327 | .m328 | .m454 | .m455 | .m663 | .m664 | .m666 | .m667 | .m668 | .m673 | .m674 | .m676 | .m677 | .m678 | .m683 | .m684 => 0
  | .m665 | .m675 => 12
  | .m669 | .m670 | .m679 | .m680 => 13
  | .m671 | .m681 => 11
  | .m672 | .m682 => 10

def entryCost (v : V) : Nat := match v with
  | .m327 | .m454 | .m663 => 31
  | .m328 | .m666 => 98
  | .m455 => 50
  | .m664 => 97
  | .m665 | .m669 | .m670 | .m671 | .m672 => 35
  | .m667 => 71
  | .m668 | .m674 => 72
  | .m673 => 70
  | .m675 => 85
  | .m676 => 51
  | .m677 => 48
  | .m678 | .m684 => 49
  | .m679 | .m680 => 47
  | .m681 => 45
  | .m682 => 83
  | .m683 => 43

def startN (v : V) : Nat := match v with
  | .m327 | .m328 | .m454 | .m455 | .m663 | .m664 | .m666 | .m673 => 1
  | .m665 | .m667 | .m668 | .m669 | .m670 | .m671 | .m672 | .m674 | .m675 | .m676 | .m677 | .m678 | .m679 | .m680 | .m681 | .m682 | .m683 | .m684 => 0

def suffix (v : V) : List Bool := match v with
  | .m327 | .m328 | .m454 | .m455 | .m663 | .m664 | .m665 | .m666 | .m669 | .m670 | .m671 | .m672 | .m673 => []
  | .m667 => [true,true,true,true,true,false]
  | .m668 => [false,true,true,true,true,true,false]
  | .m674 => [true,true,true,true,true,true,false]
  | .m675 | .m676 | .m679 | .m680 | .m681 | .m682 | .m683 => [true,true,true,false]
  | .m677 => [true,true,false,true,true,true,false]
  | .m678 => [false,true,true,false,true,true,true,false]
  | .m684 => [true,true,true,false,true,true,true,false]

abbrev E (L R : List Bool) : Z0 := ⟨4,L,R⟩
abbrev F (L R : List Bool) : Z0 := ⟨5,L,R⟩
abbrev U (n : Nat) := List.replicate n true
abbrev Z (n : Nat) := List.replicate n false

def K (v : V) (n : Nat) := 5*n+p v

theorem Kpos (v : V) (n : Nat) : 0 < K v n := by cases v <;> simp [K,p] <;> omega

theorem clearF (v : V) (k : Nat) (L R : List Bool) :
    run0 (table v) k (F (U k++L) R) = some (F L (Z k++R)) := by
  induction k generalizing R with
  | zero => rfl
  | succ k ih =>
    have h1 : run0 (table v) 1 (F (U (k+1)++L) R) = some (F (U k++L) (false::R)) := by cases v <;> rfl
    have H := join0 h1 (ih (false::R))
    rw [Nat.add_comm 1 k] at H
    simpa only [List.replicate_succ' (n:=k) (a:=false),List.append_assoc,List.singleton_append] using H

theorem clearE (v : V) (k : Nat) (hk : 0 < k) (L R : List Bool) :
    run0 (table v) (k+1) (E (false::(U k++false::L)) R) = some (F (false::L) (Z k++true::R)) := by
  cases k with
  | zero => omega
  | succ k =>
    have h1 : run0 (table v) 2 (E (false::(U (k+1)++false::L)) R) = some (F (U k++false::L) (false::true::R)) := by cases v <;> rfl
    have H := join0 h1 (clearF v k (false::L) (false::true::R))
    rw [show 2+k=k+1+1 by omega] at H
    simpa only [List.replicate_succ' (n:=k) (a:=false),List.append_assoc,List.singleton_append] using H

theorem base (v : V) (b : Bool) (L R : List Bool) :
    run0 (table v) (baseCost v) (F (false::L) (Z (p v)++b::R)) = some (E (b::(U (p v)++false::L)) R) := by cases v <;> cases b <;> rfl

theorem extend (v : V) (k : Nat) (b : Bool) (L R : List Bool) :
    run0 (table v) 9 (E (true::(U k++false::L)) (false::false::false::false::b::R)) = some (E (b::(U (k+5)++false::L)) R) := by cases v <;> cases b <;> rfl

theorem extendBlank (v : V) (k : Nat) (L : List Bool) :
    run0 (table v) 9 (E (true::(U k++false::L)) []) = some (E (false::(U (k+5)++false::L)) []) := by cases v <;> rfl

def T (v : V) : Nat → Nat
  | 0 => baseCost v
  | n+1 => 2*T v n+K v n+10

theorem fill (v : V) (n : Nat) (b : Bool) (L R : List Bool) :
    run0 (table v) (T v n) (F (false::L) (Z (K v n)++b::R)) = some (E (b::(U (K v n)++false::L)) R) := by
  induction n generalizing b L R with
  | zero => simpa [K,T] using base v b L R
  | succ n ih =>
    have h1 := ih false L (false::false::false::false::b::R)
    have h2 := clearE v (K v n) (Kpos v n) L (false::false::false::false::b::R)
    have h3 := ih true L (false::false::false::false::b::R)
    have h4 := extend v (K v n) b L R
    have H := join0 (join0 (join0 h1 h2) h3) h4
    rw [show T v n+(K v n+1)+T v n+9=T v (n+1) by simp only [T]; omega] at H
    have ha : Z (K v n)++false::false::false::false::false::b::R=Z (K v (n+1))++b::R := by
      change List.replicate (K v n) false ++ false::false::false::false::false::b::R = List.replicate (K v (n+1)) false ++ b::R
      rw [show K v (n+1)=K v n+5 by unfold K; omega,← List.replicate_append_replicate,List.append_assoc]; rfl
    rw [ha,show K v n+5=K v (n+1) by unfold K; omega] at H
    exact H

def readyCost (v : V) (n : Nat) := T v n+(K v n+1)+T v n

theorem ready (v : V) (n : Nat) (L R : List Bool) :
    run0 (table v) (readyCost v n) (F (false::L) (Z (K v n)++false::R)) = some (E (true::(U (K v n)++false::L)) R) :=
  join0 (join0 (fill v n false L R) (clearE v (K v n) (Kpos v n) L R)) (fill v n true L R)

def fam (v : V) (n d : Nat) : Z0 := E (false::(U (K v n+d)++false::suffix v)) []
def cost0 (v : V) (n : Nat) := K v n+1+T v n+9

theorem epoch0 (v : V) (n : Nat) : run0 (table v) (cost0 v n) (fam v n 0) = some (fam v (n+1) 0) := by
  have H := join0 (join0 (clearE v (K v n) (Kpos v n) (suffix v) []) (fill v n true (suffix v) [])) (extendBlank v (K v n) (suffix v))
  unfold cost0 fam
  rw [← show K v n+5=K v (n+1) by unfold K; omega]
  exact H

theorem tail1 (v : V) (k : Nat) (L : List Bool) :
    run0 (table v) 2 (E (true::(U k++false::L)) [true]) = some (E (false::(U (k+2)++false::L)) []) := by cases v <;> rfl

def cost1 (v : V) (n : Nat) := K v n+1+1+readyCost v n+2

theorem epoch1 (v : V) (n : Nat) : run0 (table v) (cost1 v n) (fam v n 1) = some (fam v n 2) := by
  have hp : 0<K v n+1 := by omega
  have h := clearE v (K v n+1) hp (suffix v) []
  have he : Z (K v n+1)++[true] = Z (K v n)++[false,true] := by
    change List.replicate (K v n+1) false ++ [true] = List.replicate (K v n) false ++ [false,true]
    rw [← List.replicate_append_replicate,List.append_assoc]; rfl
  rw [he] at h
  have H := join0 (join0 h (ready v n (suffix v) [true])) (tail1 v (K v n) (suffix v))
  exact H

theorem tail2a (v : V) (h : kind v=1) (n : Nat) (L : List Bool) :
    run0 (table v) (tailCost v) (E (true::(U (K v n)++false::L)) [false,true]) = some (E (false::(U (K v n+7)++false::L)) []) := by
  cases v <;> simp [kind] at h <;> rfl

theorem tail2b (v : V) (h : kind v=2) (n : Nat) (L : List Bool) :
    run0 (table v) (tailCost v) (E (true::(U (K v n)++false::L)) [false,true]) = some (E (false::(U (K v n+6)++false::L)) []) := by
  cases v <;> simp [kind] at h <;> rfl

def cost2 (v : V) (n : Nat) := K v n+2+1+readyCost v n+tailCost v

theorem epoch2a (v : V) (h : kind v=1) (n : Nat) : run0 (table v) (cost2 v n) (fam v n 2) = some (fam v (n+1) 2) := by
  have hp : 0<K v n+2 := by omega
  have h1 := clearE v (K v n+2) hp (suffix v) []
  have he : Z (K v n+2)++[true] = Z (K v n)++[false,false,true] := by
    change List.replicate (K v n+2) false ++ [true] = List.replicate (K v n) false ++ [false,false,true]
    rw [← List.replicate_append_replicate,List.append_assoc]; rfl
  rw [he] at h1
  have H := join0 (join0 h1 (ready v n (suffix v) [false,true])) (tail2a v h n (suffix v))
  unfold cost2 fam
  rw [← show K v n+7=K v (n+1)+2 by unfold K; omega]
  exact H

theorem epoch2b (v : V) (h : kind v=2) (n : Nat) : run0 (table v) (cost2 v n) (fam v n 2) = some (fam v (n+1) 1) := by
  have hp : 0<K v n+2 := by omega
  have h1 := clearE v (K v n+2) hp (suffix v) []
  have he : Z (K v n+2)++[true] = Z (K v n)++[false,false,true] := by
    change List.replicate (K v n+2) false ++ [true] = List.replicate (K v n) false ++ [false,false,true]
    rw [← List.replicate_append_replicate,List.append_assoc]; rfl
  rw [he] at h1
  have H := join0 (join0 h1 (ready v n (suffix v) [false,true])) (tail2b v h n (suffix v))
  unfold cost2 fam
  rw [← show K v n+6=K v (n+1)+1 by unfold K; omega]
  exact H

def family (v : V) (n : Nat) := fam v (n+startN v) (if kind v=0 then 0 else 2)
def cost (v : V) (n : Nat) :=
  if kind v=0 then cost0 v (n+startN v) else if kind v=1 then cost2 v (n+startN v) else cost2 v (n+startN v)+cost1 v (n+startN v+1)
theorem kindCases (v : V) : kind v=0 ∨ kind v=1 ∨ kind v=2 := by cases v <;> decide

theorem growth (v : V) (n : Nat) : run0 (table v) (cost v n) (family v n) = some (family v (n+1)) := by
  rcases kindCases v with h|h|h
  · simp only [family,cost,h,ite_true]
    rw [show n+1+startN v=n+startN v+1 by omega]
    exact epoch0 v _
  · simp only [family,cost,h,show (1:Nat)≠0 by decide,ite_false,ite_true]
    rw [show n+1+startN v=n+startN v+1 by omega]
    exact epoch2a v h _
  · simp only [family,cost,h,show (2:Nat)≠0 by decide,show (2:Nat)≠1 by decide,ite_false]
    rw [show n+1+startN v=n+startN v+1 by omega]
    exact join0 (epoch2b v h _) (epoch1 v _)

theorem entry (v : V) : run0 (table v) (entryCost v) ⟨0,[],[]⟩ = some (family v 0) := by cases v <;> rfl

theorem positive (v : V) (n : Nat) : 0 < cost v n := by
  unfold cost
  split
  · unfold cost0; omega
  · split
    · unfold cost2; omega
    · unfold cost2 cost1; omega

theorem never (v : V) (m : Machine) (hm : compatible (table v) m) : NeverHalts m := never_of_growth (table v) (family v) (entryCost v) (cost v) (entry v) (positive v) (growth v) m hm


namespace M327
abbrev table := _root_.BB6.Agent1Raw60RERecursive.table .m327
theorem never (m : Machine) (hm : compatible table m) : NeverHalts m := _root_.BB6.Agent1Raw60RERecursive.never .m327 m hm
end M327

namespace M328
abbrev table := _root_.BB6.Agent1Raw60RERecursive.table .m328
theorem never (m : Machine) (hm : compatible table m) : NeverHalts m := _root_.BB6.Agent1Raw60RERecursive.never .m328 m hm
end M328

namespace M454
abbrev table := _root_.BB6.Agent1Raw60RERecursive.table .m454
theorem never (m : Machine) (hm : compatible table m) : NeverHalts m := _root_.BB6.Agent1Raw60RERecursive.never .m454 m hm
end M454

namespace M455
abbrev table := _root_.BB6.Agent1Raw60RERecursive.table .m455
theorem never (m : Machine) (hm : compatible table m) : NeverHalts m := _root_.BB6.Agent1Raw60RERecursive.never .m455 m hm
end M455

namespace M663
abbrev table := _root_.BB6.Agent1Raw60RERecursive.table .m663
theorem never (m : Machine) (hm : compatible table m) : NeverHalts m := _root_.BB6.Agent1Raw60RERecursive.never .m663 m hm
end M663

namespace M664
abbrev table := _root_.BB6.Agent1Raw60RERecursive.table .m664
theorem never (m : Machine) (hm : compatible table m) : NeverHalts m := _root_.BB6.Agent1Raw60RERecursive.never .m664 m hm
end M664

namespace M665
abbrev table := _root_.BB6.Agent1Raw60RERecursive.table .m665
theorem never (m : Machine) (hm : compatible table m) : NeverHalts m := _root_.BB6.Agent1Raw60RERecursive.never .m665 m hm
end M665

namespace M666
abbrev table := _root_.BB6.Agent1Raw60RERecursive.table .m666
theorem never (m : Machine) (hm : compatible table m) : NeverHalts m := _root_.BB6.Agent1Raw60RERecursive.never .m666 m hm
end M666

namespace M667
abbrev table := _root_.BB6.Agent1Raw60RERecursive.table .m667
theorem never (m : Machine) (hm : compatible table m) : NeverHalts m := _root_.BB6.Agent1Raw60RERecursive.never .m667 m hm
end M667

namespace M668
abbrev table := _root_.BB6.Agent1Raw60RERecursive.table .m668
theorem never (m : Machine) (hm : compatible table m) : NeverHalts m := _root_.BB6.Agent1Raw60RERecursive.never .m668 m hm
end M668

namespace M669
abbrev table := _root_.BB6.Agent1Raw60RERecursive.table .m669
theorem never (m : Machine) (hm : compatible table m) : NeverHalts m := _root_.BB6.Agent1Raw60RERecursive.never .m669 m hm
end M669

namespace M670
abbrev table := _root_.BB6.Agent1Raw60RERecursive.table .m670
theorem never (m : Machine) (hm : compatible table m) : NeverHalts m := _root_.BB6.Agent1Raw60RERecursive.never .m670 m hm
end M670

namespace M671
abbrev table := _root_.BB6.Agent1Raw60RERecursive.table .m671
theorem never (m : Machine) (hm : compatible table m) : NeverHalts m := _root_.BB6.Agent1Raw60RERecursive.never .m671 m hm
end M671

namespace M672
abbrev table := _root_.BB6.Agent1Raw60RERecursive.table .m672
theorem never (m : Machine) (hm : compatible table m) : NeverHalts m := _root_.BB6.Agent1Raw60RERecursive.never .m672 m hm
end M672

namespace M673
abbrev table := _root_.BB6.Agent1Raw60RERecursive.table .m673
theorem never (m : Machine) (hm : compatible table m) : NeverHalts m := _root_.BB6.Agent1Raw60RERecursive.never .m673 m hm
end M673

namespace M674
abbrev table := _root_.BB6.Agent1Raw60RERecursive.table .m674
theorem never (m : Machine) (hm : compatible table m) : NeverHalts m := _root_.BB6.Agent1Raw60RERecursive.never .m674 m hm
end M674

namespace M675
abbrev table := _root_.BB6.Agent1Raw60RERecursive.table .m675
theorem never (m : Machine) (hm : compatible table m) : NeverHalts m := _root_.BB6.Agent1Raw60RERecursive.never .m675 m hm
end M675

namespace M676
abbrev table := _root_.BB6.Agent1Raw60RERecursive.table .m676
theorem never (m : Machine) (hm : compatible table m) : NeverHalts m := _root_.BB6.Agent1Raw60RERecursive.never .m676 m hm
end M676

namespace M677
abbrev table := _root_.BB6.Agent1Raw60RERecursive.table .m677
theorem never (m : Machine) (hm : compatible table m) : NeverHalts m := _root_.BB6.Agent1Raw60RERecursive.never .m677 m hm
end M677

namespace M678
abbrev table := _root_.BB6.Agent1Raw60RERecursive.table .m678
theorem never (m : Machine) (hm : compatible table m) : NeverHalts m := _root_.BB6.Agent1Raw60RERecursive.never .m678 m hm
end M678

namespace M679
abbrev table := _root_.BB6.Agent1Raw60RERecursive.table .m679
theorem never (m : Machine) (hm : compatible table m) : NeverHalts m := _root_.BB6.Agent1Raw60RERecursive.never .m679 m hm
end M679

namespace M680
abbrev table := _root_.BB6.Agent1Raw60RERecursive.table .m680
theorem never (m : Machine) (hm : compatible table m) : NeverHalts m := _root_.BB6.Agent1Raw60RERecursive.never .m680 m hm
end M680

namespace M681
abbrev table := _root_.BB6.Agent1Raw60RERecursive.table .m681
theorem never (m : Machine) (hm : compatible table m) : NeverHalts m := _root_.BB6.Agent1Raw60RERecursive.never .m681 m hm
end M681

namespace M682
abbrev table := _root_.BB6.Agent1Raw60RERecursive.table .m682
theorem never (m : Machine) (hm : compatible table m) : NeverHalts m := _root_.BB6.Agent1Raw60RERecursive.never .m682 m hm
end M682

namespace M683
abbrev table := _root_.BB6.Agent1Raw60RERecursive.table .m683
theorem never (m : Machine) (hm : compatible table m) : NeverHalts m := _root_.BB6.Agent1Raw60RERecursive.never .m683 m hm
end M683

namespace M684
abbrev table := _root_.BB6.Agent1Raw60RERecursive.table .m684
theorem never (m : Machine) (hm : compatible table m) : NeverHalts m := _root_.BB6.Agent1Raw60RERecursive.never .m684 m hm
end M684

#print axioms never

#print axioms growth

#print axioms fill

#print axioms entry

end BB6.Agent1Raw60RERecursive
