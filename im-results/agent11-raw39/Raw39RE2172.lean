import SweepPumping
open BB6Coverage BB6Coverage.Agent31Pump BB6Coverage.Agent50Zipper
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedVariables false

namespace BB6.Agent11Raw39RE2172

/-- The exact 11-transition partial machine at Raw39 0RE leaf 2172.
    Its only undefined slot is B/1. -/
def table : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0,false => some (some ⟨true,true,1⟩)   -- 1RB
  | 0,true  => some (some ⟨false,true,4⟩)  -- 0RE
  | 1,false => some (some ⟨true,true,2⟩)   -- 1RC
  | 2,false => some (some ⟨false,true,3⟩)  -- 0RD
  | 2,true  => some (some ⟨true,false,4⟩)  -- 1LE
  | 3,false => some (some ⟨true,false,3⟩)  -- 1LD
  | 3,true  => some (some ⟨false,true,0⟩)  -- 0RA
  | 4,false => some (some ⟨true,false,4⟩)  -- 1LE
  | 4,true  => some (some ⟨true,false,5⟩)  -- 1LF
  | 5,false => some (some ⟨true,true,0⟩)   -- 1RA
  | 5,true  => some (some ⟨false,false,5⟩) -- 0LF
  | _,_ => none

abbrev O (n : Nat) : List Bool := rep [true] n
abbrev Z (n : Nat) : List Bool := rep [false] n
def block : List Bool := [true,true,true,false,false,false,false,false]
def suffix : List Bool := [true,true,true,true,true,true,false,true,true,true]

/-- Four phase-boundary configurations. The repeated block is an unbounded
    stack tail; every phase leaves its arbitrary continuation untouched. -/
def A (n : Nat) (Y : List Bool) : Z0 :=
  ⟨0,[true,true,true],
    [false,false,false,true] ++ O 2 ++ Z 16 ++ rep block n ++ suffix ++ Y⟩

def B (n : Nat) (Y : List Bool) : Z0 :=
  ⟨0,[true,true,true],
    [false,false,false,true] ++ O 6 ++ Z 14 ++ rep block n ++ suffix ++ Y⟩

def C (n : Nat) (Y : List Bool) : Z0 :=
  ⟨0,[true,true,true],
    [false,false,false,true] ++ O 2 ++ Z 2 ++ O 3 ++ [false] ++ O 4 ++ Z 10 ++
      rep block n ++ suffix ++ Y⟩

def D (n : Nat) (Y : List Bool) : Z0 :=
  ⟨0,[true,true,true],
    [false,false,false,true] ++ O 9 ++ [false] ++ O 4 ++ Z 10 ++
      rep block n ++ suffix ++ Y⟩

/-- The four exact macro phases. -/
theorem phaseAB (n : Nat) (Y : List Bool) :
    run0 table 92 (A n Y) = some (B n Y) := by
  rfl

theorem phaseBC (n : Nat) (Y : List Bool) :
    run0 table 180 (B n Y) = some (C n Y) := by
  rfl

theorem phaseCD (n : Nat) (Y : List Bool) :
    run0 table 92 (C n Y) = some (D n Y) := by
  rfl

theorem phaseDA (n : Nat) (Y : List Bool) :
    run0 table 364 (D n Y) = some (A (n+1) Y) := by
  cases n <;> rfl

theorem cycle (n : Nat) (Y : List Bool) :
    run0 table 728 (A n Y) = some (A (n+1) Y) := by
  have h := join0 (join0 (join0 (phaseAB n Y) (phaseBC n Y)) (phaseCD n Y)) (phaseDA n Y)
  simpa only [show 92+180+92+364=728 by omega] using h

/-- Exact entry from the blank tape into the counter cycle. -/
theorem entry : run0 table 1703 ⟨0,[],[]⟩ = some (A 0 []) := by
  rfl

theorem iter (n : Nat) :
    run0 table (728*n) (A 0 []) = some (A n []) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    have h := join0 ih (cycle n [])
    simpa [Nat.mul_succ, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using h

/-- The machine has runs of arbitrarily large finite length. -/
theorem unbounded : ∀ k, ∃ t c, k ≤ t ∧ run0 table t ⟨0,[],[]⟩ = some c := by
  intro k
  refine ⟨1703+728*k,A k [],by omega,?_⟩
  have h := join0 entry (iter k)
  simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using h

/-- Every total completion of the partial table is nonhalting. -/
theorem never (m : Machine) (hm : compatible table m) : NeverHalts m := by
  intro n
  obtain ⟨t,c,ht,hr⟩ := unbounded n
  have hz : (zrun table t start).map project = some c :=
    (run_project table t start).trans hr
  cases h : zrun table t start with
  | none => simp [h] at hz
  | some z =>
    have H := zrun_sound table m hm t start z h
    rw [start_embed] at H
    rw [show t=n+(t-n) by omega,run_append] at H
    cases he : run m n blank with
    | none => simp [he] at H
    | some c => rfl

#print axioms phaseAB
#print axioms phaseBC
#print axioms phaseCD
#print axioms phaseDA
#print axioms cycle
#print axioms entry
#print axioms iter
#print axioms unbounded
#print axioms never

end BB6.Agent11Raw39RE2172
