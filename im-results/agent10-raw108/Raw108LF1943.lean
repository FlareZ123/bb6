import SweepPumping
namespace BB6.Agent10Raw108LF1943
open BB6Coverage BB6Coverage.Agent31Pump
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def table : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 1,true => some (some ⟨false,false,5⟩)
  | 2,false => some (some ⟨false,true,3⟩)
  | 2,true => some (some ⟨false,false,1⟩)
  | 3,false => some (some ⟨true,false,3⟩)
  | 3,true => some (some ⟨true,true,4⟩)
  | 4,false => some (some ⟨false,true,0⟩)
  | 4,true => some (some ⟨true,false,1⟩)
  | 5,false => some (some ⟨false,true,4⟩)
  | 5,true => some (some ⟨true,false,5⟩)
  | _,_ => none
abbrev P := [true,false,true,true,false]
abbrev X := [false,false,true,true,false]
abbrev D (L R : List Bool) : Z0 := ⟨3,L,R⟩
abbrev F (L R : List Bool) : Z0 := ⟨5,L,R⟩
theorem initial (L R : List Bool) :
    run0 table 13 (F (P++P++L) R) = some (F (P++L) ([false,false,true,false,false]++R)) := by rfl
theorem change1 (L R : List Bool) :
    run0 table 10 (D (P++L) ([false,false,true,false,false]++R)) = some (F (P++L) ([false,false,false,false,false]++R)) := by rfl
theorem return1 (L R : List Bool) :
    run0 table 5 (D (P++L) ([false,false,false,false,false]++R)) = some (D (X++P++L) R) := by rfl
theorem descend2 (L R : List Bool) :
    run0 table 11 (D (X++P++L) R) = some (F (P++L) ([false,false,false,true,true]++R)) := by rfl
theorem change2 (L R : List Bool) :
    run0 table 12 (D (P++L) ([false,false,false,true,true]++R)) = some (F (P++L) ([false,false,false,false,true]++R)) := by rfl
theorem return2 (L R : List Bool) :
    run0 table 5 (D (P++L) ([false,false,false,false,true]++R)) = some (D (P++P++L) R) := by rfl
theorem base (R : List Bool) :
    run0 table 56 (F (P++[false]) R) = some (D (P++[false]) R) := by rfl
theorem outer (L : List Bool) :
    run0 table 5 (D (P++L) []) = some (D (X++P++L) []) := by rfl

def cost : Nat → Nat
  | 0 => 56
  | n+1 => 13 + cost n + 10 + cost n + 5 + 11 + cost n + 12 + cost n + 5
theorem recursive (n : Nat) (R : List Bool) :
    run0 table (cost n) (F (P++rep P n++[false]) R) =
      some (D (P++rep P n++[false]) R) := by
  induction n generalizing R with
  | zero => exact base R
  | succ n ih =>
    have H := initial (rep P n++[false]) R
    have H := join0 H (ih ([false,false,true,false,false]++R))
    have H := join0 H (change1 (rep P n++[false]) R)
    have H := join0 H (ih ([false,false,false,false,false]++R))
    have H := join0 H (return1 (rep P n++[false]) R)
    have H := join0 H (descend2 (rep P n++[false]) R)
    have H := join0 H (ih ([false,false,false,true,true]++R))
    have H := join0 H (change2 (rep P n++[false]) R)
    have H := join0 H (ih ([false,false,false,false,true]++R))
    have H := join0 H (return2 (rep P n++[false]) R)
    simpa only [cost,rep,List.append_assoc] using H

def family (n : Nat) := D (P++rep P n++[false]) []
def epoch (n : Nat) := 5 + 11 + cost n + 12 + cost n + 5
theorem entry : run0 table 31 ⟨0,[],[]⟩ = some (family 0) := by rfl
theorem growth (n : Nat) : run0 table (epoch n) (family n) = some (family (n+1)) := by
    have H := outer (rep P n++[false])
    have H := join0 H (descend2 (rep P n++[false]) [])
    have H := join0 H (recursive n [false,false,false,true,true])
    have H := join0 H (change2 (rep P n++[false]) [])
    have H := join0 H (recursive n [false,false,false,false,true])
    have H := join0 H (return2 (rep P n++[false]) [])
    simpa only [epoch,family,rep,List.append_assoc,List.append_nil] using H
theorem positive (n : Nat) : 0 < epoch n := by unfold epoch; omega
theorem never (m : Machine) (hm : compatible table m) : NeverHalts m :=
  never_of_growth table family 31 epoch entry positive growth m hm
#print axioms growth
#print axioms never
end BB6.Agent10Raw108LF1943
