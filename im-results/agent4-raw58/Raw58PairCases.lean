import Raw58PairCounter
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace BB6Coverage.Agent4PairCases
open BB6Coverage Agent31Pump Agent4PairCounter
namespace M1510
-- 1RB0RC_1RC---_0RD0RF_1LD1RE_---0RA_0RC0LD
def table : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 0,true => some (some ⟨false,true,2⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 2,false => some (some ⟨false,true,3⟩)
  | 2,true => some (some ⟨false,true,5⟩)
  | 3,false => some (some ⟨true,false,3⟩)
  | 3,true => some (some ⟨true,true,4⟩)
  | 4,true => some (some ⟨false,true,0⟩)
  | 5,false => some (some ⟨false,true,2⟩)
  | 5,true => some (some ⟨false,false,3⟩)
  | _,_ => none
theorem entry : run0 table 7 ⟨0,[],[]⟩ = some (A []) := by rfl
theorem anchor (r : List Bool) : run0 table 1 (A r) = some (C 0 r) := by rfl
theorem carry (k : Nat) (r : List Bool) :
    run0 table 2 (C k (true::false::r)) = some (C (k+1) r) := by rfl
theorem sweepStop (L R : List Bool) :
    run0 table 2 ⟨3,[false,false,false]++[false,false]++L,[]++R⟩ =
      some ⟨3,[false,false,false]++L,[]++[true,true]++R⟩ := by rfl
theorem sweepEmpty (L R : List Bool) :
    run0 table 2 ⟨3,[false,false,false,false]++[false,false]++L,[]++R⟩ =
      some ⟨3,[false,false,false,false]++L,[]++[true,true]++R⟩ := by rfl
theorem stop (k : Nat) (r : List Bool) :
    run0 table (7+2*k) (C k (true::true::r)) =
      some (A (rep [true,true] k ++ true::false::r)) := by
  have h1 : run0 table 2 (C k (true::true::r)) = some (D [false,false,false] k (false::r)) := by rfl
  have h2 := clear table [false,false,false] sweepStop k (false::r)
  have h3 : run0 table 5 (D [false,false,false] 0 (rep [true,true] k ++ false::r)) =
      some (A (true :: (rep [true,true] k ++ false::r))) := by rfl
  have h := join0 (join0 h1 h2) h3
  rw [ones_comm] at h
  rw [show 2+2*k+5=7+2*k by omega] at h
  exact h
theorem empty (k : Nat) :
    run0 table (7+2*k) (C k []) = some (A (rep [true,true] (k+1))) := by
  have h1 : run0 table 1 (C k []) = some (D [false,false,false,false] k []) := by rfl
  have h2 := clear table [false,false,false,false] sweepEmpty k []
  have h3 : run0 table 6 (D [false,false,false,false] 0 (rep [true,true] k ++ [])) =
      some (A (rep [true,true] (k+1))) := by
    simp only [List.append_nil]
    rfl
  have h := join0 (join0 h1 h2) h3
  rw [show 1+2*k+6=7+2*k by omega] at h
  exact h
theorem never (m : Machine) (hm : compatible table m) : NeverHalts m :=
  Agent4PairCounter.never table 7 1 2 7 7 entry anchor carry stop empty (by decide) (by decide) m hm
#print axioms never
end M1510
namespace M1513
-- 1RB0RC_1RC1LE_0RD0RF_1LD1RE_---0RA_1LA0LD
def table : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 0,true => some (some ⟨false,true,2⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 1,true => some (some ⟨true,false,4⟩)
  | 2,false => some (some ⟨false,true,3⟩)
  | 2,true => some (some ⟨false,true,5⟩)
  | 3,false => some (some ⟨true,false,3⟩)
  | 3,true => some (some ⟨true,true,4⟩)
  | 4,true => some (some ⟨false,true,0⟩)
  | 5,false => some (some ⟨true,false,0⟩)
  | 5,true => some (some ⟨false,false,3⟩)
  | _,_ => none
theorem entry : run0 table 7 ⟨0,[],[]⟩ = some (A []) := by rfl
theorem anchor (r : List Bool) : run0 table 1 (A r) = some (C 0 r) := by rfl
theorem carry (k : Nat) (r : List Bool) :
    run0 table 6 (C k (true::false::r)) = some (C (k+1) r) := by rfl
theorem sweepStop (L R : List Bool) :
    run0 table 2 ⟨3,[false,false,false]++[false,false]++L,[]++R⟩ =
      some ⟨3,[false,false,false]++L,[]++[true,true]++R⟩ := by rfl
theorem sweepEmpty (L R : List Bool) :
    run0 table 2 ⟨3,[false,false,false,false]++[false,false]++L,[]++R⟩ =
      some ⟨3,[false,false,false,false]++L,[]++[true,true]++R⟩ := by rfl
theorem stop (k : Nat) (r : List Bool) :
    run0 table (7+2*k) (C k (true::true::r)) =
      some (A (rep [true,true] k ++ true::false::r)) := by
  have h1 : run0 table 2 (C k (true::true::r)) = some (D [false,false,false] k (false::r)) := by rfl
  have h2 := clear table [false,false,false] sweepStop k (false::r)
  have h3 : run0 table 5 (D [false,false,false] 0 (rep [true,true] k ++ false::r)) =
      some (A (true :: (rep [true,true] k ++ false::r))) := by rfl
  have h := join0 (join0 h1 h2) h3
  rw [ones_comm] at h
  rw [show 2+2*k+5=7+2*k by omega] at h
  exact h
theorem empty (k : Nat) :
    run0 table (7+2*k) (C k []) = some (A (rep [true,true] (k+1))) := by
  have h1 : run0 table 1 (C k []) = some (D [false,false,false,false] k []) := by rfl
  have h2 := clear table [false,false,false,false] sweepEmpty k []
  have h3 : run0 table 6 (D [false,false,false,false] 0 (rep [true,true] k ++ [])) =
      some (A (rep [true,true] (k+1))) := by
    simp only [List.append_nil]
    rfl
  have h := join0 (join0 h1 h2) h3
  rw [show 1+2*k+6=7+2*k by omega] at h
  exact h
theorem never (m : Machine) (hm : compatible table m) : NeverHalts m :=
  Agent4PairCounter.never table 7 1 6 7 7 entry anchor carry stop empty (by decide) (by decide) m hm
#print axioms never
end M1513
namespace M1514
-- 1RB0RC_1RC---_0RD0RF_1LD1RE_0RA0RA_1LE0LD
def table : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 0,true => some (some ⟨false,true,2⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 2,false => some (some ⟨false,true,3⟩)
  | 2,true => some (some ⟨false,true,5⟩)
  | 3,false => some (some ⟨true,false,3⟩)
  | 3,true => some (some ⟨true,true,4⟩)
  | 4,false => some (some ⟨false,true,0⟩)
  | 4,true => some (some ⟨false,true,0⟩)
  | 5,false => some (some ⟨true,false,4⟩)
  | 5,true => some (some ⟨false,false,3⟩)
  | _,_ => none
theorem entry : run0 table 7 ⟨0,[],[]⟩ = some (A []) := by rfl
theorem anchor (r : List Bool) : run0 table 1 (A r) = some (C 0 r) := by rfl
theorem carry (k : Nat) (r : List Bool) :
    run0 table 4 (C k (true::false::r)) = some (C (k+1) r) := by rfl
theorem sweepStop (L R : List Bool) :
    run0 table 2 ⟨3,[false,false,false]++[false,false]++L,[]++R⟩ =
      some ⟨3,[false,false,false]++L,[]++[true,true]++R⟩ := by rfl
theorem sweepEmpty (L R : List Bool) :
    run0 table 2 ⟨3,[false,false,false,false]++[false,false]++L,[]++R⟩ =
      some ⟨3,[false,false,false,false]++L,[]++[true,true]++R⟩ := by rfl
theorem stop (k : Nat) (r : List Bool) :
    run0 table (7+2*k) (C k (true::true::r)) =
      some (A (rep [true,true] k ++ true::false::r)) := by
  have h1 : run0 table 2 (C k (true::true::r)) = some (D [false,false,false] k (false::r)) := by rfl
  have h2 := clear table [false,false,false] sweepStop k (false::r)
  have h3 : run0 table 5 (D [false,false,false] 0 (rep [true,true] k ++ false::r)) =
      some (A (true :: (rep [true,true] k ++ false::r))) := by rfl
  have h := join0 (join0 h1 h2) h3
  rw [ones_comm] at h
  rw [show 2+2*k+5=7+2*k by omega] at h
  exact h
theorem empty (k : Nat) :
    run0 table (7+2*k) (C k []) = some (A (rep [true,true] (k+1))) := by
  have h1 : run0 table 1 (C k []) = some (D [false,false,false,false] k []) := by rfl
  have h2 := clear table [false,false,false,false] sweepEmpty k []
  have h3 : run0 table 6 (D [false,false,false,false] 0 (rep [true,true] k ++ [])) =
      some (A (rep [true,true] (k+1))) := by
    simp only [List.append_nil]
    rfl
  have h := join0 (join0 h1 h2) h3
  rw [show 1+2*k+6=7+2*k by omega] at h
  exact h
theorem never (m : Machine) (hm : compatible table m) : NeverHalts m :=
  Agent4PairCounter.never table 7 1 4 7 7 entry anchor carry stop empty (by decide) (by decide) m hm
#print axioms never
end M1514
namespace M1515
-- 1RB0RC_1RC---_0RD0RF_1LD1RE_0LC0RA_0RC0LE
def table : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 0,true => some (some ⟨false,true,2⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 2,false => some (some ⟨false,true,3⟩)
  | 2,true => some (some ⟨false,true,5⟩)
  | 3,false => some (some ⟨true,false,3⟩)
  | 3,true => some (some ⟨true,true,4⟩)
  | 4,false => some (some ⟨false,false,2⟩)
  | 4,true => some (some ⟨false,true,0⟩)
  | 5,false => some (some ⟨false,true,2⟩)
  | 5,true => some (some ⟨false,false,4⟩)
  | _,_ => none
theorem entry : run0 table 7 ⟨0,[],[]⟩ = some (A []) := by rfl
theorem anchor (r : List Bool) : run0 table 1 (A r) = some (C 0 r) := by rfl
theorem carry (k : Nat) (r : List Bool) :
    run0 table 2 (C k (true::false::r)) = some (C (k+1) r) := by rfl
theorem sweepStop (L R : List Bool) :
    run0 table 2 ⟨3,[false,false,false]++[false,false]++L,[]++R⟩ =
      some ⟨3,[false,false,false]++L,[]++[true,true]++R⟩ := by rfl
theorem sweepEmpty (L R : List Bool) :
    run0 table 2 ⟨3,[false,false,false,false]++[false,false]++L,[]++R⟩ =
      some ⟨3,[false,false,false,false]++L,[]++[true,true]++R⟩ := by rfl
theorem stop (k : Nat) (r : List Bool) :
    run0 table (9+2*k) (C k (true::true::r)) =
      some (A (rep [true,true] k ++ true::false::r)) := by
  have h1 : run0 table 4 (C k (true::true::r)) = some (D [false,false,false] k (false::r)) := by rfl
  have h2 := clear table [false,false,false] sweepStop k (false::r)
  have h3 : run0 table 5 (D [false,false,false] 0 (rep [true,true] k ++ false::r)) =
      some (A (true :: (rep [true,true] k ++ false::r))) := by rfl
  have h := join0 (join0 h1 h2) h3
  rw [ones_comm] at h
  rw [show 4+2*k+5=9+2*k by omega] at h
  exact h
theorem empty (k : Nat) :
    run0 table (7+2*k) (C k []) = some (A (rep [true,true] (k+1))) := by
  have h1 : run0 table 1 (C k []) = some (D [false,false,false,false] k []) := by rfl
  have h2 := clear table [false,false,false,false] sweepEmpty k []
  have h3 : run0 table 6 (D [false,false,false,false] 0 (rep [true,true] k ++ [])) =
      some (A (rep [true,true] (k+1))) := by
    simp only [List.append_nil]
    rfl
  have h := join0 (join0 h1 h2) h3
  rw [show 1+2*k+6=7+2*k by omega] at h
  exact h
theorem never (m : Machine) (hm : compatible table m) : NeverHalts m :=
  Agent4PairCounter.never table 7 1 2 9 7 entry anchor carry stop empty (by decide) (by decide) m hm
#print axioms never
end M1515
namespace M1517
-- 1RB0RC_1RC---_0RD0RF_1LD1RE_1LD0RA_0RC0LE
def table : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 0,true => some (some ⟨false,true,2⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 2,false => some (some ⟨false,true,3⟩)
  | 2,true => some (some ⟨false,true,5⟩)
  | 3,false => some (some ⟨true,false,3⟩)
  | 3,true => some (some ⟨true,true,4⟩)
  | 4,false => some (some ⟨true,false,3⟩)
  | 4,true => some (some ⟨false,true,0⟩)
  | 5,false => some (some ⟨false,true,2⟩)
  | 5,true => some (some ⟨false,false,4⟩)
  | _,_ => none
theorem entry : run0 table 7 ⟨0,[],[]⟩ = some (A []) := by rfl
theorem anchor (r : List Bool) : run0 table 1 (A r) = some (C 0 r) := by rfl
theorem carry (k : Nat) (r : List Bool) :
    run0 table 2 (C k (true::false::r)) = some (C (k+1) r) := by rfl
theorem sweepStop (L R : List Bool) :
    run0 table 2 ⟨3,[false,false]++[false,false]++L,[]++R⟩ =
      some ⟨3,[false,false]++L,[]++[true,true]++R⟩ := by rfl
theorem sweepEmpty (L R : List Bool) :
    run0 table 2 ⟨3,[false,false,false,false]++[false,false]++L,[]++R⟩ =
      some ⟨3,[false,false,false,false]++L,[]++[true,true]++R⟩ := by rfl
theorem stop (k : Nat) (r : List Bool) :
    run0 table (7+2*k) (C k (true::true::r)) =
      some (A (rep [true,true] k ++ true::false::r)) := by
  have h1 : run0 table 3 (C k (true::true::r)) = some (D [false,false] k (true::false::r)) := by rfl
  have h2 := clear table [false,false] sweepStop k (true::false::r)
  have h3 : run0 table 4 (D [false,false] 0 (rep [true,true] k ++ true::false::r)) =
      some (A (rep [true,true] k ++ true::false::r)) := by rfl
  have h := join0 (join0 h1 h2) h3
  rw [show 3+2*k+4=7+2*k by omega] at h
  exact h
theorem empty (k : Nat) :
    run0 table (7+2*k) (C k []) = some (A (rep [true,true] (k+1))) := by
  have h1 : run0 table 1 (C k []) = some (D [false,false,false,false] k []) := by rfl
  have h2 := clear table [false,false,false,false] sweepEmpty k []
  have h3 : run0 table 6 (D [false,false,false,false] 0 (rep [true,true] k ++ [])) =
      some (A (rep [true,true] (k+1))) := by
    simp only [List.append_nil]
    rfl
  have h := join0 (join0 h1 h2) h3
  rw [show 1+2*k+6=7+2*k by omega] at h
  exact h
theorem never (m : Machine) (hm : compatible table m) : NeverHalts m :=
  Agent4PairCounter.never table 7 1 2 7 7 entry anchor carry stop empty (by decide) (by decide) m hm
#print axioms never
end M1517
namespace M2878
-- 1RB1LA_1RC0LC_0RD0RF_1LD1RE_---0RA_0RC0LD
def table : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 0,true => some (some ⟨true,false,0⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 1,true => some (some ⟨false,false,2⟩)
  | 2,false => some (some ⟨false,true,3⟩)
  | 2,true => some (some ⟨false,true,5⟩)
  | 3,false => some (some ⟨true,false,3⟩)
  | 3,true => some (some ⟨true,true,4⟩)
  | 4,true => some (some ⟨false,true,0⟩)
  | 5,false => some (some ⟨false,true,2⟩)
  | 5,true => some (some ⟨false,false,3⟩)
  | _,_ => none
theorem entry : run0 table 7 ⟨0,[],[]⟩ = some (A []) := by rfl
theorem anchor (r : List Bool) : run0 table 5 (A r) = some (C 0 r) := by rfl
theorem carry (k : Nat) (r : List Bool) :
    run0 table 2 (C k (true::false::r)) = some (C (k+1) r) := by rfl
theorem sweepStop (L R : List Bool) :
    run0 table 2 ⟨3,[false,false,false]++[false,false]++L,[]++R⟩ =
      some ⟨3,[false,false,false]++L,[]++[true,true]++R⟩ := by rfl
theorem sweepEmpty (L R : List Bool) :
    run0 table 2 ⟨3,[false,false,false,false]++[false,false]++L,[]++R⟩ =
      some ⟨3,[false,false,false,false]++L,[]++[true,true]++R⟩ := by rfl
theorem stop (k : Nat) (r : List Bool) :
    run0 table (7+2*k) (C k (true::true::r)) =
      some (A (rep [true,true] k ++ true::false::r)) := by
  have h1 : run0 table 2 (C k (true::true::r)) = some (D [false,false,false] k (false::r)) := by rfl
  have h2 := clear table [false,false,false] sweepStop k (false::r)
  have h3 : run0 table 5 (D [false,false,false] 0 (rep [true,true] k ++ false::r)) =
      some (A (true :: (rep [true,true] k ++ false::r))) := by rfl
  have h := join0 (join0 h1 h2) h3
  rw [ones_comm] at h
  rw [show 2+2*k+5=7+2*k by omega] at h
  exact h
theorem empty (k : Nat) :
    run0 table (7+2*k) (C k []) = some (A (rep [true,true] (k+1))) := by
  have h1 : run0 table 1 (C k []) = some (D [false,false,false,false] k []) := by rfl
  have h2 := clear table [false,false,false,false] sweepEmpty k []
  have h3 : run0 table 6 (D [false,false,false,false] 0 (rep [true,true] k ++ [])) =
      some (A (rep [true,true] (k+1))) := by
    simp only [List.append_nil]
    rfl
  have h := join0 (join0 h1 h2) h3
  rw [show 1+2*k+6=7+2*k by omega] at h
  exact h
theorem never (m : Machine) (hm : compatible table m) : NeverHalts m :=
  Agent4PairCounter.never table 7 5 2 7 7 entry anchor carry stop empty (by decide) (by decide) m hm
#print axioms never
end M2878
end BB6Coverage.Agent4PairCases
