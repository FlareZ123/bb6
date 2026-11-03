-- Exact root-sensitive table reflection and semantics for historical BB(6) roots
-- Oct24 row146 1RB1LB_1RC0LA_1RD0RE_1LA0LB_1RF---_1RB1LD
-- Oct24 row411 1RB0RC_1LC1RC_1LD0RB_1LA0LE_1LF---_1LC1RA
-- The root of row411 corresponds to D-start row146, not A-start row146.
-- This bridge does not decide either machine.
namespace BB6Row146Conjugacy

inductive State where
  | A | B | C | D | E | F
  deriving DecidableEq, Repr

inductive Direction where
  | L | R
  deriving DecidableEq, Repr

structure Rule where
  write : Bool
  dir : Direction
  next : State
  deriving DecidableEq, Repr

abbrev Machine := State → Bool → Option Rule

def row146 : Machine
  | .A, false => some ⟨true, .R, .B⟩
  | .A, true  => some ⟨true, .L, .B⟩
  | .B, false => some ⟨true, .R, .C⟩
  | .B, true  => some ⟨false, .L, .A⟩
  | .C, false => some ⟨true, .R, .D⟩
  | .C, true  => some ⟨false, .R, .E⟩
  | .D, false => some ⟨true, .L, .A⟩
  | .D, true  => some ⟨false, .L, .B⟩
  | .E, false => some ⟨true, .R, .F⟩
  | .E, true  => none
  | .F, false => some ⟨true, .R, .B⟩
  | .F, true  => some ⟨true, .L, .D⟩

def row411 : Machine
  | .A, false => some ⟨true, .R, .B⟩
  | .A, true  => some ⟨false, .R, .C⟩
  | .B, false => some ⟨true, .L, .C⟩
  | .B, true  => some ⟨true, .R, .C⟩
  | .C, false => some ⟨true, .L, .D⟩
  | .C, true  => some ⟨false, .R, .B⟩
  | .D, false => some ⟨true, .L, .A⟩
  | .D, true  => some ⟨false, .L, .E⟩
  | .E, false => some ⟨true, .L, .F⟩
  | .E, true  => none
  | .F, false => some ⟨true, .L, .C⟩
  | .F, true  => some ⟨true, .R, .A⟩

def rename : State → State
  | .A => .B
  | .B => .C
  | .C => .D
  | .D => .A
  | .E => .E
  | .F => .F

def mirror : Direction → Direction
  | .L => .R
  | .R => .L

def renRule (r : Rule) : Rule := ⟨r.write, mirror r.dir, rename r.next⟩

-- All twelve table entries, including the undefined E1 entry.
theorem table_conjugacy (s : State) (b : Bool) :
    row411 (rename s) b = (row146 s b).map renRule := by
  cases s <;> cases b <;> decide

structure Config where
  state : State
  head : Int
  tape : Int → Bool

def delta : Direction → Int
  | .L => -1
  | .R => 1

def step (machine : Machine) (c : Config) : Option Config :=
  match machine c.state (c.tape c.head) with
  | none => none
  | some r => some {
      state := r.next
      head := c.head + delta r.dir
      tape := fun x => if x = c.head then r.write else c.tape x
    }

def flip (c : Config) : Config := {
  state := rename c.state
  head := -c.head
  tape := fun x => c.tape (-x)
}

theorem reflect_written_tape (t : Int → Bool) (h : Int) (b : Bool) :
    (fun x => if x = -h then b else t (-x)) =
    (fun x => if -x = h then b else t (-x)) := by
  funext x
  by_cases hx : x = -h
  · have hy : -x = h := by simp [hx]
    simp [hx]
  · have hy : -x ≠ h := by
      intro eq
      have eq' := congrArg (fun z : Int => -z) eq
      exact hx (by simpa only [Int.neg_neg] using eq')
    simp [hx, hy]

theorem step_conjugacy (c : Config) :
    step row411 (flip c) = (step row146 c).map flip := by
  unfold step flip
  simp only [Int.neg_neg, table_conjugacy]
  cases h : row146 c.state (c.tape c.head) with
  | none => simp
  | some r =>
      cases r with
      | mk bit dir dest =>
          cases dir <;>
            simp [renRule, mirror, rename, delta, Option.map, Int.neg_add, Int.neg_neg,
              reflect_written_tape]

-- Run returns none at the first undefined transition along the trajectory.
def run (machine : Machine) : Nat → Config → Option Config
  | 0, c => some c
  | n + 1, c => (step machine c).bind (run machine n)

theorem run_conjugacy (n : Nat) (c : Config) :
    run row411 n (flip c) = (run row146 n c).map flip := by
  induction n generalizing c with
  | zero => rfl
  | succ n ih =>
      simp only [run]
      rw [step_conjugacy]
      cases h : step row146 c with
      | none => simp
      | some d => simpa using ih d

def blank (s : State) : Config := { state := s, head := 0, tape := fun _ => false }

theorem blank_D_reflects_to_blank_A : flip (blank .D) = blank .A := by
  rfl

theorem rooted_halts_iff :
    (∃ n, run row411 n (blank .A) = none) ↔
    (∃ n, run row146 n (blank .D) = none) := by
  have hg (n : Nat) :
      run row411 n (blank .A) = (run row146 n (blank .D)).map flip := by
    simpa only [blank_D_reflects_to_blank_A] using run_conjugacy n (blank .D)
  constructor
  · rintro ⟨n, h⟩
    refine ⟨n, ?_⟩
    rw [hg] at h
    cases hr : run row146 n (blank .D) with
    | none => rfl
    | some d => simp [hr] at h
  · rintro ⟨n, h⟩
    exact ⟨n, by rw [hg, h]; rfl⟩

end BB6Row146Conjugacy

#print axioms BB6Row146Conjugacy.rooted_halts_iff
#print axioms BB6Row146Conjugacy.table_conjugacy
