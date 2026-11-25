import SweepPumping
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace BB6.Agent1Raw60LCGlider
open BB6Coverage BB6Coverage.Agent31Pump
inductive V | le | rb deriving DecidableEq

def table (v : V) : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 0,true => some (some ⟨true,false,2⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 1,true => some (some (match v with | .le => ⟨false,false,4⟩ | .rb => ⟨true,true,1⟩))
  | 2,false => some (some ⟨false,true,3⟩)
  | 2,true => some (some ⟨false,false,5⟩)
  | 3,false => some (some ⟨true,false,3⟩)
  | 3,true => some (some ⟨true,true,4⟩)
  | 4,true => some (some ⟨true,true,0⟩)
  | 5,false => some (some ⟨true,false,1⟩)
  | 5,true => some (some ⟨true,false,0⟩)
  | _,_ => none
abbrev A (L R : List Bool) : Z0 := ⟨0,L,R⟩
abbrev P : List Bool := [true,false,true,false,true,true,false]
abbrev Q : List Bool := [true,true,true,true,true,true,false]
abbrev S : List Bool := [true,false,false,true,true,false,true,true,false,false,true,true,false]
abbrev M : List Bool := [true,true,true]
abbrev LR : List Bool := [false,true,true,false]
abbrev LL : List Bool := true::Q

def initCost : V → Nat | .le => 19 | .rb => 13
def rightCost : V → Nat | .le => 25 | .rb => 19
def leftCost : V → Nat | .le => 35 | .rb => 27
def finalCost : V → Nat | .le => 61 | .rb => 49

theorem init (v : V) (R : List Bool) : run0 (table v) (initCost v) (A [] (S++R)) = some (A (LR++Q++M) R) := by cases v <;> rfl

theorem oneR (v : V) (L R : List Bool) :
    run0 (table v) (rightCost v) (A (LR++L) (P++R)) = some (A (LR++Q++L) R) := by cases v <;> rfl

theorem oneL (v : V) (L R : List Bool) :
    run0 (table v) (leftCost v) (A (LL++Q++L) R) = some (A (LL++L) (P++R)) := by cases v <;> rfl

theorem forward (v : V) (n : Nat) (R : List Bool) :
    run0 (table v) (initCost v+rightCost v*n) (A [] (S++rep P n++R)) = some (A (LR++rep Q (n+1)++M) R) := by
  have h1 := init v (rep P n++R)
  have h2 := sweepR (table v) 0 LR [] P Q (rightCost v) (oneR v) n (Q++M) R
  simp only [List.nil_append] at h2
  have H := join0 h1 h2
  simpa only [List.append_assoc,rep,← List.append_assoc (rep Q n) Q M,rep_snoc Q n] using H

theorem finish (v : V) (R : List Bool) : run0 (table v) (finalCost v) (A (LL++M) (P++R)) = some (A [] (S++P++R)) := by cases v <;> rfl

theorem backward (v : V) (n : Nat) (R : List Bool) :
    run0 (table v) (leftCost v*n+finalCost v) (A (LL++rep Q n++M) (P++R)) = some (A [] (S++rep P (n+1)++R)) := by
  have h1 := sweepL (table v) 0 LL [] Q P (leftCost v) (oneL v) n M (P++R)
  simp only [List.nil_append] at h1
  have h : rep P n ++ (P++R) = P++(rep P n++R) := by rw [← List.append_assoc,rep_snoc P n,List.append_assoc]
  rw [h] at h1
  have H := join0 h1 (finish v (rep P n++R))
  simpa only [rep,List.append_assoc] using H

def X (b : Bool) : List Bool := if b then [false,true] else [false]
def Y (b : Bool) : List Bool := if b then [true,true,false,true,false] else [true,true,false,true,false,true]
def longCost (v : V) (b : Bool) : Nat := match v,b with | .le,false => 38 | .le,true => 32 | .rb,false => 32 | .rb,true => 26
def shortCost : V → Nat | .le => 25 | .rb => 17

theorem turnLong (v : V) (b : Bool) (L : List Bool) :
    run0 (table v) (longCost v b) (A (LR++Q++Q++L) (X b)) = some (A (LL++L) (P++Y b)) := by cases v <;> cases b <;> rfl

theorem turnShort (v : V) (b : Bool) (L : List Bool) :
    run0 (table v) (shortCost v) (A (LR++Q++L) (Y b)) = some (A (LL++L) (P++X (!b))) := by cases v <;> cases b <;> rfl

def config (n : Nat) (R : List Bool) := A [] (S++rep P n++R)
def costLong (v : V) (b : Bool) (n : Nat) := initCost v+rightCost v*(n+1)+longCost v b+(leftCost v*n+finalCost v)
def costShort (v : V) (n : Nat) := initCost v+rightCost v*n+shortCost v+(leftCost v*n+finalCost v)

theorem long (v : V) (b : Bool) (n : Nat) :
    run0 (table v) (costLong v b n) (config (n+1) (X b)) = some (config (n+1) (Y b)) := by
  have h1 := forward v (n+1) (X b)
  have h2 := turnLong v b (rep Q n++M)
  have h3 := backward v n (Y b)
  have H := join0 (join0 h1 h2) h3
  exact H

theorem short (v : V) (b : Bool) (n : Nat) :
    run0 (table v) (costShort v n) (config n (Y b)) = some (config (n+1) (X (!b))) := by
  have h1 := forward v n (Y b)
  have h2 := turnShort v b (rep Q n++M)
  have h3 := backward v n (X (!b))
  exact join0 (join0 h1 h2) h3

def family (n : Nat) := config (2*n+3) (X false)
def cost (v : V) (n : Nat) := costLong v false (2*n+2)+costShort v (2*n+3)+costLong v true (2*n+3)+costShort v (2*n+4)

theorem growth (v : V) (n : Nat) : run0 (table v) (cost v n) (family n) = some (family (n+1)) := by
  have h1 := long v false (2*n+2)
  have h2 := short v false (2*n+3)
  have h3 := long v true (2*n+3)
  have h4 := short v true (2*n+4)
  have H := join0 (join0 (join0 h1 h2) h3) h4
  unfold family cost
  rw [show 2*(n+1)+3=2*n+5 by omega]
  exact H

def entryTime : V → Nat | .le => 973 | .rb => 757
theorem entry (v : V) : run0 (table v) (entryTime v) ⟨0,[],[]⟩ = some (family 0) := by cases v <;> rfl
theorem positive (v : V) (n : Nat) : 0 < cost v n := by cases v <;> simp [cost,costLong,costShort,initCost,rightCost,longCost,leftCost,finalCost,shortCost] <;> omega
theorem never (v : V) (m : Machine) (hm : compatible (table v) m) : NeverHalts m := never_of_growth (table v) family (entryTime v) (cost v) (entry v) (positive v) (growth v) m hm
namespace M83
abbrev table := _root_.BB6.Agent1Raw60LCGlider.table .le
theorem never (m : Machine) (hm : compatible table m) : NeverHalts m := _root_.BB6.Agent1Raw60LCGlider.never .le m hm
end M83
namespace M85
abbrev table := _root_.BB6.Agent1Raw60LCGlider.table .rb
theorem never (m : Machine) (hm : compatible table m) : NeverHalts m := _root_.BB6.Agent1Raw60LCGlider.never .rb m hm
end M85
#print axioms long
#print axioms short
#print axioms never
end BB6.Agent1Raw60LCGlider
