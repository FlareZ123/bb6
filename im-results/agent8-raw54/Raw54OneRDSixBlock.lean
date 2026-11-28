import Raw54OneRDBankAudit
import SweepPumping

set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option autoImplicit false

namespace BB6.Agent8Raw54.SixBlock
open BB6Coverage BB6Coverage.Agent31Pump BB6.Agent13BlankDelay

/-- A1 is the single variable instruction; C1 is never queried on certified runs. -/
def table (a : Move) : PartialMachine := fun s => match s.1.val,s.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 0,true  => some (some a)
  | 1,false => some (some ⟨true,true,2⟩)
  | 1,true  => some (some ⟨true,true,5⟩)
  | 2,false => some (some ⟨false,true,3⟩)
  | 3,false => some (some ⟨true,false,3⟩)
  | 3,true  => some (some ⟨false,false,4⟩)
  | 4,false => some (some ⟨true,true,0⟩)
  | 4,true  => some (some ⟨true,true,3⟩)
  | 5,false => some (some ⟨false,true,4⟩)
  | 5,true  => some (some ⟨false,false,5⟩)
  | _,_     => none

def P : List Bool := [true,true,true,true,true,true,false]
def Q : List Bool := [false,false,false,false,false,true,true]
def lp : List Bool := [false,false,true,true,true,false]
def rp : List Bool := [true,false,true,true,true,false]
def S (k : Nat) : Z0 := ⟨3,lp ++ rep P k,[]⟩

theorem left_one (a : Move) (L R : List Bool) :
    run0 (table a) 27 ⟨3,lp ++ P ++ L,R⟩ =
      some ⟨3,lp ++ L,Q ++ R⟩ := by rfl

theorem turn (a : Move) (R : List Bool) :
    run0 (table a) 21 ⟨3,lp,R⟩ = some ⟨3,rp,true::R⟩ := by rfl

theorem right_one (a : Move) (L R : List Bool) :
    run0 (table a) 9 ⟨3,rp ++ L,[true] ++ Q ++ R⟩ =
      some ⟨3,rp ++ P ++ L,[true] ++ R⟩ := by rfl

theorem finish (a : Move) (L : List Bool) :
    run0 (table a) 9 ⟨3,rp ++ L,[true]⟩ = some ⟨3,lp ++ P ++ L,[]⟩ := by rfl

theorem epoch (a : Move) (k : Nat) :
    run0 (table a) (30+36*k) (S k) = some (S (k+1)) := by
  have h1 := sweepL (table a) 3 lp [] P Q 27 (left_one a) k [] []
  have h1' : run0 (table a) (27*k) (S k) = some ⟨3,lp,rep Q k⟩ := by
    simpa only [S,List.append_nil,List.nil_append] using h1
  have h2 := turn a (rep Q k)
  have h3 := sweepR (table a) 3 rp [true] Q P 9 (right_one a) k [] []
  have h3' : run0 (table a) (9*k) ⟨3,rp,true::rep Q k⟩ = some ⟨3,rp ++ rep P k,[true]⟩ := by
    simpa only [List.append_nil,List.singleton_append] using h3
  have h4 := finish a (rep P k)
  have H := join0 (join0 (join0 h1' h2) h3') h4
  rw [show 30+36*k = 27*k+21+9*k+9 by omega]
  simpa only [S,rep,List.append_assoc] using H

theorem never_at (a : Move) (n k : Nat)
    (entry : run0 (table a) n ⟨0,[],[]⟩ = some (S k))
    (m : Machine) (hm : compatible (table a) m) : NeverHalts m := by
  apply never_of_growth (table a) (fun j => S (k+j)) n (fun j => 30+36*(k+j))
  · simpa using entry
  · intro j; omega
  · intro j; simpa only [Nat.add_assoc] using epoch a (k+j)
  · exact hm

theorem cover_at (a : Move) (n k : Nat)
    (entry : run0 (table a) n ⟨0,[],[]⟩ = some (S k)) (B : Nat) :
    Cover (WeightedBound B) (table a) := by
  apply Cover.leaf
  intro m hm
  exact weighted_never B m (never_at a n k entry m hm)

def a0LA : Move := ⟨false,false,0⟩
theorem entry_a0LA : run0 (table a0LA) 404 ⟨0,[],[]⟩ = some (S 2) := by decide +kernel
theorem cover_a0LA (B : Nat) : Cover (WeightedBound B) (table a0LA) :=
  cover_at a0LA 404 2 entry_a0LA B

def a0LB : Move := ⟨false,false,1⟩
theorem entry_a0LB : run0 (table a0LB) 212 ⟨0,[],[]⟩ = some (S 2) := by decide +kernel
theorem cover_a0LB (B : Nat) : Cover (WeightedBound B) (table a0LB) :=
  cover_at a0LB 212 2 entry_a0LB B

def a0LE : Move := ⟨false,false,4⟩
theorem entry_a0LE : run0 (table a0LE) 151 ⟨0,[],[]⟩ = some (S 1) := by decide +kernel
theorem cover_a0LE (B : Nat) : Cover (WeightedBound B) (table a0LE) :=
  cover_at a0LE 151 1 entry_a0LE B

def a0RB : Move := ⟨false,true,1⟩
theorem entry_a0RB : run0 (table a0RB) 544 ⟨0,[],[]⟩ = some (S 3) := by decide +kernel
theorem cover_a0RB (B : Nat) : Cover (WeightedBound B) (table a0RB) :=
  cover_at a0RB 544 3 entry_a0RB B

def a0RD : Move := ⟨false,true,3⟩
theorem entry_a0RD : run0 (table a0RD) 247 ⟨0,[],[]⟩ = some (S 2) := by decide +kernel
theorem cover_a0RD (B : Nat) : Cover (WeightedBound B) (table a0RD) :=
  cover_at a0RD 247 2 entry_a0RD B

def a0RE : Move := ⟨false,true,4⟩
theorem entry_a0RE : run0 (table a0RE) 210 ⟨0,[],[]⟩ = some (S 2) := by decide +kernel
theorem cover_a0RE (B : Nat) : Cover (WeightedBound B) (table a0RE) :=
  cover_at a0RE 210 2 entry_a0RE B

def a1LD : Move := ⟨true,false,3⟩
theorem entry_a1LD : run0 (table a1LD) 149 ⟨0,[],[]⟩ = some (S 1) := by decide +kernel
theorem cover_a1LD (B : Nat) : Cover (WeightedBound B) (table a1LD) :=
  cover_at a1LD 149 1 entry_a1LD B

def a1LE : Move := ⟨true,false,4⟩
theorem entry_a1LE : run0 (table a1LE) 153 ⟨0,[],[]⟩ = some (S 1) := by decide +kernel
theorem cover_a1LE (B : Nat) : Cover (WeightedBound B) (table a1LE) :=
  cover_at a1LE 153 1 entry_a1LE B

def a1RA : Move := ⟨true,true,0⟩
theorem entry_a1RA : run0 (table a1RA) 464 ⟨0,[],[]⟩ = some (S 3) := by decide +kernel
theorem cover_a1RA (B : Nat) : Cover (WeightedBound B) (table a1RA) :=
  cover_at a1RA 464 3 entry_a1RA B

def a1RD : Move := ⟨true,true,3⟩
theorem entry_a1RD : run0 (table a1RD) 155 ⟨0,[],[]⟩ = some (S 1) := by decide +kernel
theorem cover_a1RD (B : Nat) : Cover (WeightedBound B) (table a1RD) :=
  cover_at a1RD 155 1 entry_a1RD B

def a1RF : Move := ⟨true,true,5⟩
theorem entry_a1RF : run0 (table a1RF) 108 ⟨0,[],[]⟩ = some (S 1) := by decide +kernel
theorem cover_a1RF (B : Nat) : Cover (WeightedBound B) (table a1RF) :=
  cover_at a1RF 108 1 entry_a1RF B

#print axioms epoch
#print axioms never_at
#print axioms cover_a0LA
#print axioms cover_a0LB
#print axioms cover_a0LE
#print axioms cover_a0RB
#print axioms cover_a0RD
#print axioms cover_a0RE
#print axioms cover_a1LD
#print axioms cover_a1LE
#print axioms cover_a1RA
#print axioms cover_a1RD
#print axioms cover_a1RF
end BB6.Agent8Raw54.SixBlock
