import SweepPumping
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace BB6Coverage.Agent1Raw57LF0M1242
open BB6Coverage BB6Coverage.Agent31Pump

def table : PartialMachine := fun s => match s.1.val,s.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 0,true => some (some ⟨false,false,5⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 1,true => some (some ⟨false,true,3⟩)
  | 2,false => some (some ⟨false,true,3⟩)
  | 3,false => some (some ⟨true,false,3⟩)
  | 3,true => some (some ⟨true,true,4⟩)
  | 4,false => some (some ⟨false,true,1⟩)
  | 4,true => some (some ⟨false,false,0⟩)
  | 5,false => some (some ⟨true,false,5⟩)
  | 5,true => some (some ⟨true,true,1⟩)
  | _,_ => none

abbrev I : List Bool := [true,false]
abbrev J : List Bool := [false,true]
abbrev T : List Bool := [true,true]
abbrev Z : List Bool := [false,false]

def X (n : Nat) (R : List Bool) : Z0 := ⟨3,I++rep I n++T,R⟩
def Y (n : Nat) (R : List Bool) : Z0 := ⟨3,Z++rep I n++T,R⟩

theorem shrink (n : Nat) (R : List Bool) :
    run0 table 8 (Y (n+1) R) = some (Y n (J++R)) := by cases n <;> rfl
theorem base (R : List Bool) : run0 table 8 (Y 0 R) = some (X 0 R) := by rfl

theorem collapse (n : Nat) (R : List Bool) :
    run0 table (8*n+8) (Y n R) = some (X 0 (rep J n++R)) := by
  induction n generalizing R with
  | zero => exact base R
  | succ n ih =>
    have h := join0 (shrink n R) (ih (J++R))
    rw [show 8*(n+1)+8=8+(8*n+8) by omega]
    simpa only [rep,List.append_assoc,← rep_snoc J n] using h

theorem carryAtom (n : Nat) (R : List Bool) :
    run0 table 4 (X n (J++J++R)) = some (Y (n+1) (T++R)) := by rfl
theorem mark (n : Nat) (R : List Bool) :
    run0 table 10 (X n (J++T++R)) = some (X (n+1) (Z++R)) := by rfl
theorem advance (n : Nat) (R : List Bool) :
    run0 table 4 (X n (Z++J++R)) = some (X (n+2) R) := by rfl
theorem extend (n : Nat) :
    run0 table 4 (X n []) = some (Y (n+2) []) := by rfl
theorem extendZ (n : Nat) :
    run0 table 4 (X n Z) = some (Y (n+2) []) := by rfl

def accCost : Nat → Nat
  | 0 => 0
  | n+1 => accCost n + 4 + (8*(3*n+1)+8) + accCost n + 10 + 4

theorem repAdd (B : List Bool) (n k : Nat) :
    rep B (n+k) = rep B n++rep B k := by
  induction k with
  | zero => simp [rep]
  | succ k ih =>
    rw [show n+(k+1)=(n+k)+1 by omega]
    simp only [rep,ih]
    rw [← List.append_assoc,← rep_snoc B n,List.append_assoc]

theorem acc (n : Nat) (R : List Bool) :
    run0 table (accCost n) (X 0 (rep J (3*n)++R)) = some (X (3*n) R) := by
  induction n generalizing R with
  | zero => rfl
  | succ n ih =>
    have h1 := ih (J++J++J++R)
    have h2 := carryAtom (3*n) (J++R)
    have h3 := collapse (3*n+1) (T++(J++R))
    have h4 := ih (J++T++J++R)
    have h5 := mark (3*n) (J++R)
    have h6 := advance (3*n+1) R
    have hr : rep J (3*n+1)++(T++(J++R)) = rep J (3*n)++(J++T++J++R) := by
      rw [repAdd J (3*n) 1]
      simp only [rep,List.append_nil,List.append_assoc]
    rw [hr] at h3
    have h := join0 (join0 (join0 (join0 (join0 h1 h2) h3) h4) h5) h6
    have hk : 3*(n+1)=3*n+3 := by omega
    rw [hk,repAdd J (3*n) 3]
    simpa only [accCost,rep,List.append_assoc,List.nil_append,List.append_nil] using h

theorem carry (n : Nat) (R : List Bool) :
    run0 table (4+(8*(3*n+1)+8)+accCost n+10) (X (3*n) (J++J++R)) =
      some (X (3*n+1) (Z++R)) := by
  have h1 := carryAtom (3*n) R
  have h2 := collapse (3*n+1) (T++R)
  have h3 := acc n (J++T++R)
  have h4 := mark (3*n) R
  have hr : rep J (3*n+1)++(T++R) = rep J (3*n)++(J++T++R) := by
    rw [repAdd J (3*n) 1]
    simp only [rep,List.append_nil,List.append_assoc]
  rw [hr] at h2
  exact join0 (join0 (join0 h1 h2) h3) h4

def family (n : Nat) : Z0 := Y (3*n) []
theorem entry : run0 table 3 ⟨0,[],[]⟩ = some (family 0) := by rfl

def growCost (n : Nat) : Nat :=
    (8*(3*n)+8) + accCost n + 4 + (8*(3*n+2)+8) + accCost n +
    (4+(8*(3*n+1)+8)+accCost n+10) + 4
theorem growth (n : Nat) :
    run0 table (growCost n) (family n) = some (family (n+1)) := by
  have h1 := collapse (3*n) []
  have h2 := acc n []
  have h3 := extend (3*n)
  have h4 := collapse (3*n+2) []
  have h5 := acc n (J++J)
  have h6 := carry n []
  have h7 := extendZ (3*n+1)
  rw [repAdd J (3*n) 2] at h4
  simp only [rep,List.append_nil] at h4
  have h := join0 (join0 (join0 (join0 (join0 (join0 h1 h2) h3) h4) h5) h6) h7
  unfold family growCost
  rw [show 3*(n+1)=3*n+1+2 by omega]
  exact h

theorem never (m : Machine) (hm : compatible table m) : NeverHalts m :=
  never_of_growth table family 3 growCost entry (by intro n; unfold growCost; omega) growth m hm
#print axioms never
end BB6Coverage.Agent1Raw57LF0M1242
