import RelativeTape
import Cryptids.Machines

namespace BB6.ConjectureBridge

private def bit (a : Fin 2) : Bool := a.val == 1
private def unbit (a : Bool) : Fin 2 := if a then 1 else 0
@[simp] private theorem bit_unbit (a : Bool) : bit (unbit a) = a := by cases a <;> rfl
@[simp] private theorem unbit_bit (a : Fin 2) : unbit (bit a) = a := by
  have h : a.val = 0 ∨ a.val = 1 := by omega
  rcases h with h | h
  · apply Fin.ext
    simp [unbit, bit, h]
  · apply Fin.ext
    simp [unbit, bit, h]

private def isRight : Turing.Dir → Bool
 | .left => false
 | .right => true

/-- Converts every external Turing transition into the exact local convention. -/
def toAgent8 (m : ConjectureMachines.Machine 6 2) : BB6Coverage.Machine :=
  fun s => (m.transition s.1 (unbit s.2)).map fun (w,d,q) =>
    {write := bit w, right := isRight d, next := q}

def tapeToRelative (t : ConjectureMachines.Tape (Fin 2)) : BB6.Bridge.Tape :=
  ⟨bit t.head, (fun n => bit (t.left.nth n)), fun n => bit (t.right.nth n)⟩

private theorem toRelative_write_move_right (t : ConjectureMachines.Tape (Fin 2))
    (w : Fin 2) :
    tapeToRelative ((t.write w).move Turing.Dir.right) =
      BB6.Bridge.goRight (tapeToRelative t) (bit w) := by
  cases t with
  | mk a l r =>
    unfold tapeToRelative BB6.Bridge.goRight ConjectureMachines.Tape.move
      ConjectureMachines.Tape.write
    simp only
    congr 1
    funext n
    cases n with
    | zero => simp [ConjectureMachines.ListBlank.nth_zero,
        ConjectureMachines.ListBlank.head_cons]
    | succ n => simp [ConjectureMachines.ListBlank.nth_succ,
        ConjectureMachines.ListBlank.tail_cons]

private theorem toRelative_write_move_left (t : ConjectureMachines.Tape (Fin 2))
    (w : Fin 2) :
    tapeToRelative ((t.write w).move Turing.Dir.left) =
      BB6.Bridge.goLeft (tapeToRelative t) (bit w) := by
  cases t with
  | mk a l r =>
    unfold tapeToRelative BB6.Bridge.goLeft ConjectureMachines.Tape.move
      ConjectureMachines.Tape.write
    simp only
    congr 1
    funext n
    cases n with
    | zero => simp [ConjectureMachines.ListBlank.nth_zero,
        ConjectureMachines.ListBlank.head_cons]
    | succ n => simp [ConjectureMachines.ListBlank.nth_succ,
        ConjectureMachines.ListBlank.tail_cons]

structure Positioned where
  cfg : ConjectureMachines.Cfg 6 2
  head : Int

def toRelative (p : Positioned) : BB6.Bridge.Cfg :=
  { state := p.cfg.state, head := p.head,
    tape := tapeToRelative p.cfg.tape }

def step (m : ConjectureMachines.Machine 6 2) (p : Positioned) : Option Positioned :=
  (m.transition p.cfg.state p.cfg.tape.head).map fun (w,d,q) =>
    { cfg := ⟨q, (p.cfg.tape.write w).move d⟩,
      head := p.head + (if isRight d then 1 else -1) }

theorem step_toRelative (m : ConjectureMachines.Machine 6 2) (p : Positioned) :
    BB6.Bridge.step (toAgent8 m) (toRelative p) =
      (step m p).map toRelative := by
  unfold BB6.Bridge.step step toAgent8 toRelative
  have hb : unbit (tapeToRelative p.cfg.tape).cur = p.cfg.tape.head :=
    unbit_bit _
  rw [hb]
  cases hm : m.transition p.cfg.state p.cfg.tape.head with
  | none => simp [hm]
  | some a =>
    rcases a with ⟨w,d,q⟩
    cases d with
    | left =>
      simp only [hm, Option.map_some]
      apply congrArg some
      congr 1
      exact (toRelative_write_move_left p.cfg.tape w).symm
    | right =>
      simp only [hm, Option.map_some]
      apply congrArg some
      congr 1
      exact (toRelative_write_move_right p.cfg.tape w).symm

def run (m : ConjectureMachines.Machine 6 2) : Nat → Positioned → Option Positioned
  | 0, p => some p
  | n + 1, p => (run m n p).bind (step m)

theorem run_toRelative (m : ConjectureMachines.Machine 6 2) (p : Positioned) (n : Nat) :
    BB6.Bridge.run (toAgent8 m) n (toRelative p) =
      (run m n p).map toRelative := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [BB6.Bridge.run, run, ih]
    cases h : run m n p with
    | none => simp [h]
    | some q => simp [h, step_toRelative]

def initialPositioned : Positioned := ⟨ConjectureMachines.init, 0⟩

private theorem empty_nth (n : Nat) :
    (ConjectureMachines.ListBlank.mk ([] : List (Fin 2))).nth n = 0 := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simpa only [ConjectureMachines.ListBlank.nth_succ,
      ConjectureMachines.ListBlank.tail_mk, List.tail_nil] using ih

theorem initial_toRelative : toRelative initialPositioned = BB6.Bridge.initialRelative := by
  unfold toRelative initialPositioned BB6.Bridge.initialRelative tapeToRelative
    ConjectureMachines.init ConjectureMachines.Tape.mk₁
    ConjectureMachines.Tape.mk₂ ConjectureMachines.Tape.mk'
  have hzero :
      (ConjectureMachines.ListBlank.mk ([] : List (Fin 2))).head = 0 := rfl
  simp only [BB6.Bridge.Cfg.mk.injEq, BB6.Bridge.Tape.mk.injEq]
  simp [bit, empty_nth, hzero, ConjectureMachines.ListBlank.nth_succ]

theorem blank_run_toAbsolute (m : ConjectureMachines.Machine 6 2) (n : Nat) :
    BB6Coverage.run (toAgent8 m) n BB6Coverage.blank =
       (run m n initialPositioned).map
        (BB6.Bridge.toAbsolute ∘ toRelative) := by
  rw [← BB6.Bridge.initial_absolute, ← initial_toRelative]
  rw [BB6.Bridge.run_absolute, run_toRelative]
  exact Option.map_map _ _ _

inductive Reachable (m : ConjectureMachines.Machine 6 2) :
    ConjectureMachines.Cfg 6 2 → Prop where
  | root : Reachable m ConjectureMachines.init
  | next {a b} (h : Reachable m a) (step : ConjectureMachines.step m a = some b) :
      Reachable m b

private theorem step_source (m : ConjectureMachines.Machine 6 2) (p : Positioned) :
    (step m p).map Positioned.cfg = ConjectureMachines.step m p.cfg := by
  cases h : m.transition p.cfg.state p.cfg.tape.head with
  | none => simp [step, ConjectureMachines.step, h]
  | some a => rcases a with ⟨w,d,q⟩; simp [step, ConjectureMachines.step, h]

private theorem positioned_runs_all (m : ConjectureMachines.Machine 6 2)
    (hlive : ∀ c, Reachable m c → (ConjectureMachines.step m c).isSome = true) :
    ∀ n, ∃ p, run m n initialPositioned = some p ∧ Reachable m p.cfg := by
  intro n
  induction n with
  | zero => exact ⟨initialPositioned, rfl, .root⟩
  | succ n ih =>
    obtain ⟨p, hp, hreach⟩ := ih
    have hstep := hlive p.cfg hreach
    cases hs : step m p with
    | none =>
      have heq := step_source m p
      rw [hs] at heq
      simp only [Option.map_none] at heq
      rw [← heq] at hstep
      simp at hstep
    | some q =>
      refine ⟨q, by simp [run, hp, hs], ?_⟩
      apply Reachable.next hreach
      have heq := step_source m p
      rw [hs] at heq
      simpa using heq.symm

/-- Source nonhalting closure on all reachable states implies local NeverHalts. -/
theorem reachable_live_implies_never (m : ConjectureMachines.Machine 6 2)
    (hlive : ∀ c, Reachable m c → (ConjectureMachines.step m c).isSome = true) :
    BB6Coverage.NeverHalts (toAgent8 m) := by
  intro n
  obtain ⟨p, hp, _⟩ := positioned_runs_all m hlive n
  rw [blank_run_toAbsolute, hp]
  rfl

#print axioms reachable_live_implies_never
#print axioms initial_toRelative
#print axioms blank_run_toAbsolute
#print axioms run_toRelative
#print axioms toRelative_write_move_right
#print axioms toRelative_write_move_left
#print axioms step_toRelative
end BB6.ConjectureBridge
