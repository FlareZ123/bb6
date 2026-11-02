import Frontier

namespace BB6.Bridge

/-- Head-relative tape with all cells represented, not a bounded window. -/
structure Tape where
  cur : Bool
  left : Nat → Bool
  right : Nat → Bool

def symbol (t : Tape) : Int → Bool
  | .ofNat 0 => t.cur
  | .ofNat (n+1) => t.right n
  | .negSucc n => t.left n

def goRight (t : Tape) (w : Bool) : Tape :=
  ⟨t.right 0, (fun n => if n=0 then w else t.left (n-1)), fun n => t.right (n+1)⟩

def goLeft (t : Tape) (w : Bool) : Tape :=
  ⟨t.left 0, (fun n => t.left (n+1)), fun n => if n=0 then w else t.right (n-1)⟩

theorem at_goRight (t : Tape) (w : Bool) (k : Int) :
    symbol (goRight t w) k = if k = -1 then w else symbol t (k+1) := by
  cases k with
  | ofNat n =>
    cases n with
    | zero => rfl
    | succ n => rfl
  | negSucc n =>
    cases n with
    | zero => rfl
    | succ n =>
      have hneq : (Int.negSucc (n+1) : Int) ≠ -1 := by omega
      have hshift : (Int.negSucc (n+1) : Int) + 1 = Int.negSucc n := by omega
      simp [symbol, goRight, hneq, hshift]

theorem at_goLeft (t : Tape) (w : Bool) (k : Int) :
    symbol (goLeft t w) k = if k = 1 then w else symbol t (k-1) := by
  cases k with
  | ofNat n =>
    cases n with
    | zero => rfl
    | succ n =>
      cases n with
      | zero => rfl
      | succ n =>
        change t.right n = if (Int.ofNat (n + 2) : Int) = 1 then w
          else symbol t ((Int.ofNat (n + 2) : Int) - 1)
        have hneq : (Int.ofNat (n + 2) : Int) ≠ 1 := by
          simp only [Int.ofNat_eq_natCast, Int.natCast_add]
          omega
        have hshift : (Int.ofNat (n+2) : Int) - 1 = Int.ofNat (n+1) := by
          simp only [Int.ofNat_eq_natCast, Int.natCast_add]
          omega
        rw [if_neg hneq, hshift]
        rfl
  | negSucc n =>
    simp [symbol, goLeft]

structure Cfg where
  state : Fin 6
  head : Int
  tape : Tape

def toAbsolute (c : Cfg) : BB6Coverage.Config :=
  { state := c.state, head := c.head, tape := fun x => symbol c.tape (x - c.head) }

def step (m : BB6Coverage.Machine) (c : Cfg) : Option Cfg :=
  (m (c.state, c.tape.cur)).map fun mv =>
    {state := mv.next,
     head := c.head + (if mv.right then 1 else -1),
     tape := if mv.right then goRight c.tape mv.write else goLeft c.tape mv.write}

private theorem right_absolute (t : Tape) (h x : Int) (w : Bool) :
  symbol (goRight t w) (x - (h + 1)) =
    if x = h then w else symbol t (x - h) := by
  rw [at_goRight]
  have hiff : (x - (h+1) = -1) ↔ (x = h) := by omega
  have hpos : x - (h+1)+1 = x - h := by omega
  simp only [hiff, hpos]

private theorem left_absolute (t : Tape) (h x : Int) (w : Bool) :
  symbol (goLeft t w) (x - (h - 1)) =
    if x = h then w else symbol t (x - h) := by
  rw [at_goLeft]
  have hiff : (x - (h-1) = 1) ↔ (x = h) := by omega
  have hpos : x - (h-1)-1 = x - h := by omega
  simp only [hiff, hpos]

/-- The exact one-step equivalence between a relative stream tape and the
original absolute Int-indexed Agent8 six-state machine. -/
theorem step_absolute (m : BB6Coverage.Machine) (c : Cfg) :
    BB6Coverage.rawStep m (toAbsolute c) = (step m c).map toAbsolute := by
  unfold BB6Coverage.rawStep step
  change (m (c.state, symbol c.tape (c.head-c.head))).map
    (BB6Coverage.applyMove (toAbsolute c)) = _
  have hread : symbol c.tape (c.head-c.head) = c.tape.cur := by simp [symbol]
  rw [hread]
  cases hm : m (c.state, c.tape.cur) with
  | none => simp [hm]
  | some mv =>
    simp only [hm, Option.map_some]
    apply congrArg some
    cases hr : mv.right <;> simp only [toAbsolute, BB6Coverage.applyMove, hr,
      Bool.false_eq_true, Bool.true_eq_false, ite_false, ite_true]
    · congr 1
      funext x
      exact (left_absolute c.tape c.head x mv.write).symm
    · congr 1
      funext x
      exact (right_absolute c.tape c.head x mv.write).symm

def run (m : BB6Coverage.Machine) : Nat → Cfg → Option Cfg
  | 0, c => some c
  | n + 1, c => (run m n c).bind (step m)

theorem run_absolute (m : BB6Coverage.Machine) (n : Nat) (c : Cfg) :
    BB6Coverage.run m n (toAbsolute c) = (run m n c).map toAbsolute := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [BB6Coverage.run, run, ih]
    cases hr : run m n c with
    | none => simp [hr]
    | some d => simp [hr, step_absolute]

def initialRelative : Cfg :=
  { state := ⟨0, by decide⟩, head := 0,
    tape := ⟨false, (fun _ => false), (fun _ => false)⟩ }

theorem initial_absolute : toAbsolute initialRelative = BB6Coverage.blank := by
  unfold toAbsolute initialRelative BB6Coverage.blank
  congr 1
  funext x
  cases x with
  | ofNat n => cases n <;> rfl
  | negSucc n => rfl

/-- Preserves each blank-start trace and attempted-halt convention on the
entire infinite tape. -/
theorem blank_run_absolute (m : BB6Coverage.Machine) (n : Nat) :
    BB6Coverage.run m n BB6Coverage.blank =
      (run m n initialRelative).map toAbsolute := by
  rw [← initial_absolute]
  exact run_absolute m n initialRelative

theorem relative_never_iff_absolute_never (m : BB6Coverage.Machine) :
    (∀ n, (run m n initialRelative).isSome = true) ↔
       BB6Coverage.NeverHalts m := by
  constructor
  · intro h n
    rw [blank_run_absolute]
    simpa using h n
  · intro h n
    have hn := h n
    rw [blank_run_absolute] at hn
    simpa using hn

#print axioms at_goRight
#print axioms at_goLeft
#print axioms step_absolute
#print axioms blank_run_absolute
#print axioms relative_never_iff_absolute_never
end BB6.Bridge
