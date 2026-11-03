import Lean

namespace BB6.Agent12.RootPair

structure Instr where
  write : Bool
  right : Bool
  next : Fin 6
  deriving DecidableEq, Repr

abbrev Table := Fin 6 → Bool → Option Instr

-- Literal rows of 2026-10-24 holdout #146, blank root A.
def tm146 : Table
| 0, false => some ⟨true, true, 1⟩
| 0, true  => some ⟨true, false, 1⟩
| 1, false => some ⟨true, true, 2⟩
| 1, true  => some ⟨false, false, 0⟩
| 2, false => some ⟨true, true, 3⟩
| 2, true  => some ⟨false, true, 4⟩
| 3, false => some ⟨true, false, 0⟩
| 3, true  => some ⟨false, false, 1⟩
| 4, false => some ⟨true, true, 5⟩
| 4, true  => none
| 5, false => some ⟨true, true, 1⟩
| 5, true  => some ⟨true, false, 3⟩

def tm411 : Table
| 0, false => some ⟨true, true, 1⟩
| 0, true  => some ⟨false, true, 2⟩
| 1, false => some ⟨true, false, 2⟩
| 1, true  => some ⟨true, true, 2⟩
| 2, false => some ⟨true, false, 3⟩
| 2, true  => some ⟨false, true, 1⟩
| 3, false => some ⟨true, false, 0⟩
| 3, true  => some ⟨false, false, 4⟩
| 4, false => some ⟨true, false, 5⟩
| 4, true  => none
| 5, false => some ⟨true, false, 2⟩
| 5, true  => some ⟨true, true, 0⟩

-- Row 411 states A B C D E F map to row 146 states D A B C E F.
def stateMap : Fin 6 → Fin 6
| 0 => 3
| 1 => 0
| 2 => 1
| 3 => 2
| 4 => 4
| 5 => 5

def reflectInstr (i : Instr) : Instr := ⟨i.write, !i.right, stateMap i.next⟩

theorem twelve_entry_iso : ∀ s : Fin 6, ∀ bit : Bool,
    (tm411 s bit).map reflectInstr = tm146 (stateMap s) bit := by
  decide

structure Config where
  state : Fin 6
  head : Int
  tape : Int → Bool

private theorem config_ext (a b : Config)
    (hs : a.state = b.state) (hh : a.head = b.head)
    (ht : a.tape = b.tape) : a = b := by
  cases a with
  | mk as ah tap =>
    cases b with
    | mk bs bh bt =>
      dsimp at hs hh ht
      cases hs
      cases hh
      cases ht
      rfl

def reflectConfig (c : Config) : Config :=
  ⟨stateMap c.state, -c.head, fun p => c.tape (-p)⟩

def step (tm : Table) (c : Config) : Option Config :=
  (tm c.state (c.tape c.head)).map fun i =>
    ⟨i.next, c.head + (if i.right then 1 else -1),
      fun p => if p = c.head then i.write else c.tape p⟩

private theorem int_neg_eq_iff (p h : Int) : (-p = h) ↔ (p = -h) := by
  omega

theorem step_iso (c : Config) :
    (step tm411 c).map reflectConfig = step tm146 (reflectConfig c) := by
  have ht := twelve_entry_iso c.state (c.tape c.head)
  cases h : tm411 c.state (c.tape c.head) with
  | none =>
    simp only [h, Option.map_none] at ht
    simp [step, h, ← ht, reflectConfig]
  | some i =>
    simp only [h, Option.map_some] at ht
    simp only [step, h, Option.map_some]
    have ht' : tm146 (reflectConfig c).state ((reflectConfig c).tape (reflectConfig c).head) = some (reflectInstr i) := by
      simpa [reflectConfig] using ht.symm
    rw [ht']
    simp only [Option.map_some]
    apply congrArg some
    cases i with
    | mk wr dir target =>
      apply config_ext
      · rfl
      · cases dir <;> simp [reflectConfig, reflectInstr] <;> omega
      · funext p
        simp only [reflectConfig, reflectInstr]
        by_cases hp : p = -c.head
        · have hn : -p = c.head := (int_neg_eq_iff p c.head).2 hp
          simp [hp, hn]
        · have hn : -p ≠ c.head := by
            intro heq
            exact hp ((int_neg_eq_iff p c.head).1 heq)
          simp [hp, hn]

def blank (s : Fin 6) : Config := ⟨s, 0, fun _ => false⟩

theorem blank_root : reflectConfig (blank 0) = blank 3 := by
  rfl

def run (tm : Table) : Nat → Config → Option Config
| 0, c => some c
| n+1, c => (step tm c).bind (run tm n)

theorem run_iso (n : Nat) (c : Config) :
    (run tm411 n c).map reflectConfig = run tm146 n (reflectConfig c) := by
  induction n generalizing c with
  | zero => rfl
  | succ n ih =>
    simp only [run]
    rw [Option.map_bind]
    cases hstep : step tm411 c with
    | none =>
      have hs : step tm146 (reflectConfig c) = none := by
        simpa [hstep] using (step_iso c).symm
      simp [hstep, hs]
    | some d =>
      have hs : step tm146 (reflectConfig c) = some (reflectConfig d) := by
        simpa [hstep] using (step_iso c).symm
      simp [hstep, hs, ih]

theorem blank_halting_equiv :
    (∃ n, run tm411 n (blank 0) = none) ↔
    (∃ n, run tm146 n (blank 3) = none) := by
  constructor
  · rintro ⟨n, hn⟩
    refine ⟨n, ?_⟩
    have h := run_iso n (blank 0)
    rw [hn, blank_root] at h
    simpa using h.symm
  · rintro ⟨n, hn⟩
    refine ⟨n, ?_⟩
    have h := run_iso n (blank 0)
    rw [blank_root, hn] at h
    cases hrun : run tm411 n (blank 0) with
    | none => rfl
    | some d => simp [hrun] at h


-- Exact original BusyCoq Sk1Machines_v2.TM26.tm, the left-right reflection of row 411.
def tm26 : Table
| 0, false => some ⟨true, false, 1⟩
| 0, true  => some ⟨false, false, 2⟩
| 1, false => some ⟨true, true, 2⟩
| 1, true  => some ⟨true, false, 2⟩
| 2, false => some ⟨true, true, 3⟩
| 2, true  => some ⟨false, false, 1⟩
| 3, false => some ⟨true, true, 0⟩
| 3, true  => some ⟨false, true, 4⟩
| 4, false => some ⟨true, true, 5⟩
| 4, true  => none
| 5, false => some ⟨true, true, 2⟩
| 5, true  => some ⟨true, false, 0⟩

def mirrorInstr (i : Instr) : Instr := ⟨i.write, !i.right, i.next⟩

theorem original_tm26_reflects_411 : ∀ s : Fin 6, ∀ bit : Bool,
    (tm411 s bit).map mirrorInstr = tm26 s bit := by
  decide

def bareReflect (c : Config) : Config :=
  ⟨c.state, -c.head, fun p => c.tape (-p)⟩

theorem original_tm26_step_iso (c : Config) :
    (step tm411 c).map bareReflect = step tm26 (bareReflect c) := by
  have ht := original_tm26_reflects_411 c.state (c.tape c.head)
  cases h : tm411 c.state (c.tape c.head) with
  | none =>
    simp only [h, Option.map_none] at ht
    simp [step, h, ← ht, bareReflect]
  | some i =>
    simp only [h, Option.map_some] at ht
    simp only [step, h, Option.map_some]
    have ht' : tm26 (bareReflect c).state ((bareReflect c).tape (bareReflect c).head) = some (mirrorInstr i) := by
      simpa [bareReflect] using ht.symm
    rw [ht']
    simp only [Option.map_some]
    apply congrArg some
    cases i with
    | mk wr dir target =>
      apply config_ext
      · rfl
      · cases dir <;> simp [bareReflect, mirrorInstr] <;> omega
      · funext p
        simp only [bareReflect, mirrorInstr]
        by_cases hp : p = -c.head
        · have hn : -p = c.head := (int_neg_eq_iff p c.head).2 hp
          simp [hp, hn]
        · have hn : -p ≠ c.head := by
            intro heq
            exact hp ((int_neg_eq_iff p c.head).1 heq)
          simp [hp, hn]

theorem original_tm26_run_iso (n : Nat) (c : Config) :
    (run tm411 n c).map bareReflect = run tm26 n (bareReflect c) := by
  induction n generalizing c with
  | zero => rfl
  | succ n ih =>
    simp only [run]
    rw [Option.map_bind]
    cases hstep : step tm411 c with
    | none =>
      have hs : step tm26 (bareReflect c) = none := by
        simpa [hstep] using (original_tm26_step_iso c).symm
      simp [hstep, hs]
    | some d =>
      have hs : step tm26 (bareReflect c) = some (bareReflect d) := by
        simpa [hstep] using (original_tm26_step_iso c).symm
      simp [hstep, hs, ih]

theorem original_tm26_blank_root : bareReflect (blank 0) = blank 0 := by
  rfl

theorem original_tm26_blank_halting_equiv :
    (∃ n, run tm411 n (blank 0) = none) ↔
    (∃ n, run tm26 n (blank 0) = none) := by
  constructor
  · rintro ⟨n, hn⟩
    refine ⟨n, ?_⟩
    have h := original_tm26_run_iso n (blank 0)
    rw [hn, original_tm26_blank_root] at h
    simpa using h.symm
  · rintro ⟨n, hn⟩
    refine ⟨n, ?_⟩
    have h := original_tm26_run_iso n (blank 0)
    rw [original_tm26_blank_root, hn] at h
    cases hrun : run tm411 n (blank 0) with
    | none => rfl
    | some d => simp [hrun] at h

#print axioms BB6.Agent12.RootPair.original_tm26_blank_halting_equiv

#print axioms BB6.Agent12.RootPair.blank_halting_equiv
end BB6.Agent12.RootPair
