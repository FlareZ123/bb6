import Lean.Elab.Tactic.Omega

namespace BB6.Padding

/-- Finite list as a half-tape, read as false beyond the end. -/
def bitAt (xs : List Bool) (n : Nat) : Bool := (xs[n]?).getD false
def TapeEq (xs ys : List Bool) : Prop := ∀ n, bitAt xs n = bitAt ys n

@[simp] theorem bitAt_nil (n : Nat) : bitAt [] n = false := by simp [bitAt]
@[simp] theorem bitAt_cons_zero (x : Bool) (xs : List Bool) :
  bitAt (x::xs) 0 = x := rfl
@[simp] theorem bitAt_cons_succ (x : Bool) (xs : List Bool) (n : Nat) :
  bitAt (x::xs) (n+1) = bitAt xs n := rfl

theorem tapeEq_refl (xs : List Bool) : TapeEq xs xs := fun _ => rfl
theorem tapeEq_symm {xs ys : List Bool} (h : TapeEq xs ys) : TapeEq ys xs :=
  fun n => (h n).symm
theorem tapeEq_trans {xs ys zs : List Bool}
    (h : TapeEq xs ys) (g : TapeEq ys zs) : TapeEq xs zs :=
  fun n => (h n).trans (g n)
theorem tapeEq_head {xs ys : List Bool} (h : TapeEq xs ys) :
  bitAt xs 0 = bitAt ys 0 := h 0
theorem tapeEq_tail {xs ys : List Bool} (h : TapeEq xs ys) :
  TapeEq (xs.drop 1) (ys.drop 1) := by
  intro n
  cases xs <;> cases ys <;>
    simpa [bitAt, List.drop] using h (n+1)
theorem tapeEq_cons (x : Bool) {xs ys : List Bool} (h : TapeEq xs ys) :
  TapeEq (x::xs) (x::ys) := by
  intro n
  cases n with
  | zero => rfl
  | succ n => exact h n

theorem tapeEq_pad (xs : List Bool) (n : Nat) :
  TapeEq xs (xs ++ List.replicate n false) := by
  induction xs with
  | nil =>
    intro i
    simp [bitAt, List.getElem?_replicate]
    split <;> rfl
  | cons x xs ih =>
    simpa only [List.cons_append] using tapeEq_cons x ih

structure Config where
  left : List Bool
  bit : Bool
  right : List Bool
  state : Nat
  deriving Repr

def CfgEq (c d : Config) : Prop :=
  TapeEq c.left d.left ∧ c.bit = d.bit ∧ TapeEq c.right d.right ∧ c.state = d.state

def goLeft (c : Config) (write : Bool) (st : Nat) : Config :=
  ⟨c.left.drop 1, bitAt c.left 0, write::c.right, st⟩
def goRight (c : Config) (write : Bool) (st : Nat) : Config :=
  ⟨write::c.left, bitAt c.right 0, c.right.drop 1, st⟩
def goStay (c : Config) (write : Bool) (st : Nat) : Config :=
  ⟨c.left, write, c.right, st⟩

theorem goLeft_congr {c d : Config} (h : CfgEq c d) (write : Bool) (st : Nat) :
  CfgEq (goLeft c write st) (goLeft d write st) := by
  rcases h with ⟨hl,hb,hr,hs⟩
  exact ⟨tapeEq_tail hl, tapeEq_head hl, tapeEq_cons write hr, rfl⟩
theorem goRight_congr {c d : Config} (h : CfgEq c d) (write : Bool) (st : Nat) :
  CfgEq (goRight c write st) (goRight d write st) := by
  rcases h with ⟨hl,hb,hr,hs⟩
  exact ⟨tapeEq_cons write hl, tapeEq_head hr, tapeEq_tail hr, rfl⟩
theorem goStay_congr {c d : Config} (h : CfgEq c d) (write : Bool) (st : Nat) :
  CfgEq (goStay c write st) (goStay d write st) := by
  exact ⟨h.1,rfl,h.2.2.1,rfl⟩

inductive Dir where | left | right | stay
abbrev Instr := Bool × Dir × Nat

/-- Arbitrary deterministic two-symbol rule table; none denotes frozen halt. -/
def step (delta : Nat → Bool → Option Instr) (c : Config) : Config :=
  match delta c.state c.bit with
  | none => c
  | some (w,Dir.left,n) => goLeft c w n
  | some (w,Dir.right,n) => goRight c w n
  | some (w,Dir.stay,n) => goStay c w n

theorem step_congr (delta : Nat → Bool → Option Instr) {c d : Config}
    (h : CfgEq c d) : CfgEq (step delta c) (step delta d) := by
  rcases h with ⟨hl,hb,hr,hs⟩
  have heq : delta c.state c.bit = delta d.state d.bit := by rw [hb, hs]
  unfold step
  rw [heq]
  split
  · exact ⟨hl,hb,hr,hs⟩
  · exact goLeft_congr ⟨hl,hb,hr,hs⟩ _ _
  · exact goRight_congr ⟨hl,hb,hr,hs⟩ _ _
  · exact goStay_congr ⟨hl,hb,hr,hs⟩ _ _

def run (delta : Nat → Bool → Option Instr) : Nat → Config → Config
  | 0, c => c
  | n+1, c => step delta (run delta n c)

theorem run_congr (delta : Nat → Bool → Option Instr) (n : Nat)
    {c d : Config} (h : CfgEq c d) :
    CfgEq (run delta n c) (run delta n d) := by
  induction n with
  | zero => exact h
  | succ n ih => exact step_congr delta ih

/-- Unbounded primitive runs preserve equivalence under padding both half-tapes. -/
theorem run_pad (delta : Nat → Bool → Option Instr) (n p q : Nat)
    (c : Config) :
    CfgEq (run delta n c)
      (run delta n ⟨c.left ++ List.replicate p false,
        c.bit, c.right ++ List.replicate q false, c.state⟩) := by
  exact run_congr delta n ⟨tapeEq_pad _ _, rfl, tapeEq_pad _ _, rfl⟩

#print axioms run_pad
end BB6.Padding
