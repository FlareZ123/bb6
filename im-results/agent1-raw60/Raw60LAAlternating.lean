import SweepPumping
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace BB6.Agent1Raw60LAAlternating
open BB6Coverage BB6Coverage.Agent31Pump
inductive V | le | rb deriving DecidableEq

def table (v : V) : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 0,true => some (some ⟨true,false,0⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 1,true => some (some ⟨true,false,5⟩)
  | 2,false => some (some ⟨false,true,3⟩)
  | 2,true => some (some (match v with | .le => ⟨false,false,4⟩ | .rb => ⟨true,true,1⟩))
  | 3,false => some (some ⟨true,false,3⟩)
  | 3,true => some (some ⟨true,true,4⟩)
  | 4,true => some (some ⟨true,true,0⟩)
  | 5,false => some (some ⟨true,true,2⟩)
  | 5,true => some (some ⟨false,false,1⟩)
  | _,_ => none
abbrev A (L R : List Bool) : Z0 := ⟨0,L,R⟩
abbrev C (L R : List Bool) : Z0 := ⟨2,L,R⟩
abbrev F (L R : List Bool) : Z0 := ⟨5,L,R⟩
abbrev X : List Bool := [true,false]
abbrev Y : List Bool := [false,true]
abbrev J : List Bool := [true,true]
abbrev U (n : Nat) := List.replicate n true

def s (v : V) : Nat := match v with | .le => 4 | .rb => 2

theorem start (v : V) (n : Nat) (R : List Bool) :
    run0 (table v) 1 (F [] (rep X n ++ true::R)) =
      some (C J (rep Y n ++ R)) := by
  have h := congrArg (fun L => L++R) (rotate true [false] n)
  have h' : true :: (rep Y n ++ R) = rep X n ++ true::R := by
    simpa only [List.append_assoc,List.singleton_append,List.cons_append,List.nil_append] using h
  rw [← h']; cases v <;> rfl

theorem oneR (v : V) (L R : List Bool) :
    run0 (table v) (s v) (C (J++L) (Y++R)) = some (C (J++J++L) R) := by
  cases v <;> rfl

theorem sweepRight (v : V) (n : Nat) (R : List Bool) :
    run0 (table v) (s v*n) (C J (rep Y n ++ R)) = some (C (rep J (n+1)) R) := by
  have h := sweepR (table v) 2 J [] Y J (s v) (oneR v) n [] R
  simpa only [rep,List.append_nil,List.nil_append] using h

theorem middle (v : V) (L R : List Bool) :
    run0 (table v) (s v) (C (J++L) (true::R)) = some (F (J++L) (true::R)) := by
  cases v <;> rfl

theorem oneL (v : V) (L R : List Bool) :
    run0 (table v) 2 (F (J++L) R) = some (F L (X++R)) := by cases v <;> rfl

theorem sweepLeft (v : V) (n : Nat) (R : List Bool) :
    run0 (table v) (2*n) (F (rep J n) R) = some (F [] (rep X n ++ R)) := by
  have h := sweepL (table v) 5 [] [] J X 2 (oneL v) n [] R
  simpa only [List.append_nil,List.nil_append] using h

def convertCost (v : V) (n : Nat) := 1+s v*n+s v+2*(n+1)

theorem convert (v : V) (n : Nat) (R : List Bool) :
    run0 (table v) (convertCost v n) (F [] (rep X n ++ true::true::R)) =
      some (F [] (rep X (n+1) ++ true::R)) := by
  have h1 := start v n (true::R)
  have h2 := sweepRight v n (true::R)
  have h3 := middle v (rep J n) R
  have h4 := sweepLeft v (n+1) (true::R)
  exact join0 (join0 (join0 h1 h2) h3) h4

def consumeCost (v : V) (n : Nat) : Nat → Nat
  | 0 => 0
  | k+1 => convertCost v n + consumeCost v (n+1) k

theorem consume (v : V) (n k : Nat) :
    run0 (table v) (consumeCost v n k) (F [] (rep X n ++ U (k+1))) =
      some (F [] (rep X (n+k) ++ [true])) := by
  induction k generalizing n with
  | zero => rfl
  | succ k ih =>
    have h1 := convert v n (U k)
    have h2 := ih (n+1)
    have H := join0 h1 h2
    rw [show n+1+k=n+(k+1) by omega] at H
    exact H

theorem terminalTurn (v : V) (L : List Bool) :
    run0 (table v) (s v+5) (C (J++L) []) = some (A ([true,true,true,true,true]++L) []) := by
  cases v <;> rfl

theorem oneA (v : V) (L R : List Bool) :
    run0 (table v) 1 (A (true::L) R) = some (A L (true::R)) := by cases v <;> rfl

theorem repU (n : Nat) : rep [true] n = U n := by induction n <;> simp [rep,List.replicate_succ, *]
theorem repJ (n : Nat) : rep J n = U (2*n) := by
  induction n with
  | zero => rfl
  | succ n ih => rw [show 2*(n+1)=2*n+1+1 by omega]; simp only [rep,ih]; rfl

theorem terminal (v : V) (n : Nat) :
    run0 (table v) (1+s v*n+(s v+5)+(2*n+5)) (F [] (rep X n ++ [true])) =
      some (A [] (U (2*n+5))) := by
  have h1 := start v n []
  have h2 := sweepRight v n []
  have h3 := terminalTurn v (rep J n)
  have h4 := sweepL (table v) 0 [] [] [true] [true] 1 (oneA v) (2*n+5) [] []
  simp only [Nat.one_mul,List.append_nil,List.nil_append,repU] at h4
  have hh : [true,true,true,true,true] ++ rep J n = U (2*n+5) := by
    rw [repJ]; rfl
  rw [hh] at h3
  exact join0 (join0 (join0 h1 h2) h3) h4

theorem initialise (v : V) (k : Nat) :
    run0 (table v) 14 (A [] (U (k+4))) = some (F [] (X++U (k+4))) := by
  cases v <;> rfl

def size : Nat → Nat
  | 0 => 0
  | n+1 => 2*size n + 9

def family (n : Nat) : Z0 := A [] (U (size n+4))
def cost (v : V) (n : Nat) :=
  14 + consumeCost v 1 (size n+3) + (1+s v*(size n+4)+(s v+5)+(2*(size n+4)+5))

theorem growth (v : V) (n : Nat) :
    run0 (table v) (cost v n) (family n) = some (family (n+1)) := by
  have h1 := initialise v (size n)
  have h2 := consume v 1 (size n+3)
  rw [show 1+(size n+3)=size n+4 by omega] at h2
  have h3 := terminal v (size n+4)
  have H := join0 (join0 h1 h2) h3
  unfold family cost
  rw [show size (n+1)+4=2*(size n+4)+5 by simp only [size]; omega]
  exact H

theorem entry (v : V) : run0 (table v) 11 ⟨0,[],[]⟩ = some (family 0) := by cases v <;> rfl
theorem positive (v : V) (n : Nat) : 0 < cost v n := by unfold cost; omega
theorem never (v : V) (m : Machine) (hm : compatible (table v) m) : NeverHalts m :=
  never_of_growth (table v) family 11 (cost v) (entry v) (positive v) (growth v) m hm
namespace M1383
abbrev table := _root_.BB6.Agent1Raw60LAAlternating.table .le
theorem never (m : Machine) (hm : compatible table m) : NeverHalts m :=
  _root_.BB6.Agent1Raw60LAAlternating.never .le m hm
end M1383
namespace M1384
abbrev table := _root_.BB6.Agent1Raw60LAAlternating.table .rb
theorem never (m : Machine) (hm : compatible table m) : NeverHalts m :=
  _root_.BB6.Agent1Raw60LAAlternating.never .rb m hm
end M1384
#print axioms convert
#print axioms terminal
#print axioms growth
#print axioms never
end BB6.Agent1Raw60LAAlternating
