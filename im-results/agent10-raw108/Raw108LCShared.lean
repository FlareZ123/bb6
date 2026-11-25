import SweepPumping

namespace BB6.Agent10Raw108LCShared
open BB6Coverage BB6Coverage.Agent31Pump
set_option maxRecDepth 100000
set_option maxHeartbeats 0

/-- false: 93, true: 106. The two machines share the same section dynamics. -/
def table (v : Bool) : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 0,true => some (some ⟨false,false,if v then 4 else 5⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 1,true => some (some ⟨false,false,2⟩)
  | 2,false => some (some ⟨false,true,3⟩)
  | 2,true => some (some ⟨true,true,if v then 5 else 4⟩)
  | 3,false => some (some ⟨true,false,3⟩)
  | 3,true => some (some ⟨true,true,4⟩)
  | 4,false => some (some ⟨v,!v,0⟩)
  | 4,true => some (some ⟨true,false,1⟩)
  | 5,false => some (some ⟨!v,v,0⟩)
  | _,_ => none

abbrev A (L R : List Bool) : Z0 := ⟨0,L,R⟩
abbrev Q : List Bool := [true,false]
abbrev Z : List Bool := [false,false]

theorem rep_snoc_frame (n : Nat) (R : List Bool) :
    rep Q n ++ (Q++R) = rep Q (n+1) ++ R := by
  induction n with
  | zero => rfl
  | succ n ih =>
    change (Q++rep Q n)++(Q++R) = (Q++rep Q (n+1))++R
    simp only [List.append_assoc,ih]

theorem pop_one (v : Bool) (L R : List Bool) :
    run0 (table v) 2 (A (Q++L) R) = some (A L (Q++R)) := by cases v <;> rfl

theorem pop (v : Bool) (k : Nat) (L R : List Bool) :
    run0 (table v) (2*k) (A (rep Q k++L) R) = some (A L (rep Q k++R)) := by
  induction k generalizing R with
  | zero => rfl
  | succ k ih =>
    have h := join0 (pop_one v (rep Q k++L) R) (ih (Q++R))
    rw [rep_snoc_frame] at h
    simpa only [rep,List.append_assoc,show 2*(k+1)=2+2*k by omega] using h

theorem pop_last (v : Bool) (R : List Bool) :
    run0 (table v) 2 (A [true] R) = some (A [] (Q++R)) := by cases v <;> rfl

theorem scan_start (v : Bool) (R : List Bool) :
    run0 (table v) 4 (A [] (Q++R)) = some (A [false,false,true] R) := by cases v <;> rfl

theorem scan_one (v : Bool) (L R : List Bool) :
    run0 (table v) 4 (A (Z++L) (Q++R)) = some (A (Z++Q++L) R) := by cases v <;> rfl

theorem scan (v : Bool) (k : Nat) (L R : List Bool) :
    run0 (table v) (4*k) (A (Z++L) (rep Q k++R)) = some (A (Z++rep Q k++L) R) := by
  induction k generalizing L with
  | zero => rfl
  | succ k ih =>
    have h := join0 (scan_one v L (rep Q k++R)) (ih (Q++L))
    simp only [List.append_assoc] at h
    rw [rep_snoc_frame] at h
    simpa only [rep,List.append_assoc,show 4*(k+1)=4+4*k by omega] using h

theorem scan_last (v : Bool) (L : List Bool) :
    run0 (table v) 4 (A (Z++L) [true]) = some (A (Z++Q++L) []) := by cases v <;> rfl

theorem finish_pair (v : Bool) (L : List Bool) :
    run0 (table v) 10 (A (Z++Q++L) []) = some (A (Q++Q++Q++L) [true]) := by cases v <;> rfl

def family (k : Nat) : Z0 := A (rep Q k++[true]) [true]

theorem epoch (v : Bool) (k : Nat) :
    run0 (table v) (2*k+2+4+4*k+4+10) (family k) = some (family (k+3)) := by
  have h1 := pop v k [true] [true]
  have h2 := pop_last v (rep Q k++[true])
  have h3 := scan_start v (rep Q k++[true])
  have h4 := scan v k [true] [true]
  have h5 := scan_last v (rep Q k++[true])
  have h6 := finish_pair v (rep Q k++[true])
  exact join0 (join0 (join0 (join0 (join0 h1 h2) h3) h4) h5) h6

theorem entry (v : Bool) : run0 (table v) 10 ⟨0,[],[]⟩ = some (family 1) := by cases v <;> rfl

def seq (n : Nat) : Z0 := family (3*n+1)
def cost (n : Nat) : Nat := 2*(3*n+1)+2+4+4*(3*n+1)+4+10

theorem seq_entry (v : Bool) : run0 (table v) 10 ⟨0,[],[]⟩ = some (seq 0) := entry v
theorem cost_pos (n : Nat) : 0 < cost n := by unfold cost; omega
theorem growth (v : Bool) (n : Nat) : run0 (table v) (cost n) (seq n) = some (seq (n+1)) := by
  simpa only [seq,cost,show 3*(n+1)+1=3*n+1+3 by omega] using epoch v (3*n+1)

theorem never (v : Bool) (m : Machine) (hm : compatible (table v) m) : NeverHalts m :=
  never_of_growth (table v) seq 10 cost (seq_entry v) cost_pos (growth v) m hm

#print axioms epoch
#print axioms growth
#print axioms never
end BB6.Agent10Raw108LCShared

namespace BB6.Agent10Raw108LC93
open BB6Coverage
abbrev table := BB6.Agent10Raw108LCShared.table false
theorem never (m : Machine) (hm : compatible table m) : NeverHalts m :=
  BB6.Agent10Raw108LCShared.never false m hm
end BB6.Agent10Raw108LC93

namespace BB6.Agent10Raw108LC106
open BB6Coverage
abbrev table := BB6.Agent10Raw108LCShared.table true
theorem never (m : Machine) (hm : compatible table m) : NeverHalts m :=
  BB6.Agent10Raw108LCShared.never true m hm
end BB6.Agent10Raw108LC106
