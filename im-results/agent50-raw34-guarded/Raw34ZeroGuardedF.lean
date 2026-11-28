import Frontier
import Lean.Elab.Tactic.Omega
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace BB6.Agent50Raw34ZeroGuardedF
open BB6Coverage

/-!
NEW Raw34 zero-predecessor guard: every transition *into D* is
0RD, which writes 0 immediately left of D's new head. Whenever
D1=(bw,L,F) is executed, its F successor necessarily scans that
marked 0, so F1 is never queried. Arbitrary F1=HALT is permitted.

The source authentic fixed root is A0=1RB, B0=1RC, C0=0RD,
D0=1LC. A1,B1,C1,E0 are ordinary moves into A/B/C or 0RD.
The three unassigned outcomes F1,E0,E1 remain arbitrary.
-/

def safeMove (v : Move) : Prop :=
  v.next = 0 ∨ v.next = 1 ∨ v.next = 2 ∨
    v = ⟨false,true,3⟩

def parent (a1 b1 c1 f0 : Move) (bw : Bool) : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 0,true  => some (some a1)
  | 1,false => some (some ⟨true,true,2⟩)
  | 1,true  => some (some b1)
  | 2,false => some (some ⟨false,true,3⟩)
  | 2,true  => some (some c1)
  | 3,false => some (some ⟨true,false,2⟩)
  | 3,true  => some (some ⟨bw,false,5⟩)
  | 5,false => some (some f0)
  | _,_ => none

/-- A/B/C unrestricted; D has a 0 immediately left; F scans a 0. -/
def Inv (c : Config) : Prop :=
  c.state = 0 ∨ c.state = 1 ∨ c.state = 2 ∨
  (c.state = 3 ∧ c.tape (c.head-1) = false) ∨
  (c.state = 5 ∧ c.tape c.head = false)

theorem blank_inv : Inv blank := by
  left
  rfl

/-- All allowed variable actions preserve the invariant even when
    the tape outside the two inspected positions is arbitrary. -/
theorem safe_move_inv (c : Config) (v : Move)
    (hv : safeMove v) : Inv (applyMove c v) := by
  rcases hv with h0 | h1 | h2 | hD
  · simp [Inv,applyMove,h0]
  · simp [Inv,applyMove,h1]
  · simp [Inv,applyMove,h2]
  · subst v
    right; right; right; left
    refine ⟨rfl, ?_⟩
    have haddr : c.head + (1 : Int) - 1 = c.head := by omega
    simp [applyMove,haddr]

theorem zero_entry_F (c : Config) (bw : Bool)
    (h : c.tape (c.head - 1) = false) :
    Inv (applyMove c ⟨bw,false,5⟩) := by
  right; right; right; right
  refine ⟨rfl, ?_⟩
  have haddr : c.head + (-1 : Int) = c.head - 1 := by omega
  have hneq : c.head - 1 ≠ c.head := by omega
  simpa [applyMove,haddr,hneq] using h

/-- Fully source-authentic invariant preservation, including D0=1LC.
    No arbitrary unassigned transition is evaluated by this theorem. -/
theorem live_step
    (a1 b1 c1 f0 : Move) (bw : Bool)
    (ha : safeMove a1) (hb : safeMove b1)
    (hc : safeMove c1) (he : safeMove f0)
    (m : Machine) (hm : compatible (parent a1 b1 c1 f0 bw) m)
    (c : Config) (hI : Inv c) :
    ∃ d, rawStep m c = some d ∧ Inv d := by
  rcases c with ⟨q,h,T⟩
  have emit (v : Move) (hv : m (q,T h) = some v)
      (hs : Inv (applyMove ⟨q,h,T⟩ v)) :
      ∃ d, rawStep m ⟨q,h,T⟩ = some d ∧ Inv d := by
    refine ⟨applyMove ⟨q,h,T⟩ v, ?_, hs⟩
    simp [rawStep, readSlot, hv]
  change q = 0 ∨ q = 1 ∨ q = 2 ∨
    (q = 3 ∧ T (h-1) = false) ∨
    (q = 5 ∧ T h = false) at hI
  rcases hI with hA | hB | hC | hD | hE
  · subst q
    cases hbit : T h with
    | false =>
      have hmv : m (0,T h) = some ⟨true,true,1⟩ := by
        simpa [hbit] using
          (hm (0,false) (some (⟨true,true,1⟩ : Move)) (by rfl))
      exact emit ⟨true,true,1⟩ hmv
        (safe_move_inv _ _ (by simp [safeMove]))
    | true =>
      have hmv : m (0,T h) = some a1 := by
        simpa [hbit] using (hm (0,true) (some a1) (by rfl))
      exact emit a1 hmv (safe_move_inv _ _ ha)
  · subst q
    cases hbit : T h with
    | false =>
      have hmv : m (1,T h) = some ⟨true,true,2⟩ := by
        simpa [hbit] using
          (hm (1,false) (some (⟨true,true,2⟩ : Move)) (by rfl))
      exact emit ⟨true,true,2⟩ hmv
        (safe_move_inv _ _ (by simp [safeMove]))
    | true =>
      have hmv : m (1,T h) = some b1 := by
        simpa [hbit] using (hm (1,true) (some b1) (by rfl))
      exact emit b1 hmv (safe_move_inv _ _ hb)
  · subst q
    cases hbit : T h with
    | false =>
      have hmv : m (2,T h) = some ⟨false,true,3⟩ := by
        simpa [hbit] using
          (hm (2,false) (some (⟨false,true,3⟩ : Move)) (by rfl))
      exact emit ⟨false,true,3⟩ hmv
        (safe_move_inv _ _ (by simp [safeMove]))
    | true =>
      have hmv : m (2,T h) = some c1 := by
        simpa [hbit] using (hm (2,true) (some c1) (by rfl))
      exact emit c1 hmv (safe_move_inv _ _ hc)
  · rcases hD with ⟨hq, hzero⟩
    subst q
    cases hbit : T h with
    | false =>
      have hmv : m (3,T h) = some ⟨true,false,2⟩ := by
        simpa [hbit] using
          (hm (3,false) (some (⟨true,false,2⟩ : Move)) (by rfl))
      exact emit ⟨true,false,2⟩ hmv
        (safe_move_inv _ _ (by simp [safeMove]))
    | true =>
      have hmv : m (3,T h) = some ⟨bw,false,5⟩ := by
        simpa [hbit] using
          (hm (3,true) (some (⟨bw,false,5⟩ : Move)) (by rfl))
      exact emit ⟨bw,false,5⟩ hmv (zero_entry_F _ bw hzero)
  · rcases hE with ⟨hq, hzero⟩
    subst q
    have hmv : m (5,T h) = some f0 := by
      simpa [hzero] using (hm (5,false) (some f0) (by rfl))
    exact emit f0 hmv (safe_move_inv _ _ he)

theorem live_all
    (a1 b1 c1 f0 : Move) (bw : Bool)
    (ha : safeMove a1) (hb : safeMove b1)
    (hc : safeMove c1) (he : safeMove f0)
    (m : Machine) (hm : compatible (parent a1 b1 c1 f0 bw) m) :
    ∀ n, ∃ c, run m n blank = some c ∧ Inv c := by
  intro n
  induction n with
  | zero => exact ⟨blank, rfl, blank_inv⟩
  | succ n ih =>
    obtain ⟨c,hc0,hi⟩ := ih
    obtain ⟨d,hstep,hd0⟩ :=
      live_step a1 b1 c1 f0 bw ha hb hc he m hm c hi
    exact ⟨d, by simp [run,hc0,hstep], hd0⟩

/-- D1's left sweep can only reach F0, never F1. Consequently *all*
    completions are nonhalting, even an F1=HALT completion. -/
theorem never
    (a1 b1 c1 f0 : Move) (bw : Bool)
    (ha : safeMove a1) (hb : safeMove b1)
    (hc : safeMove c1) (he : safeMove f0)
    (m : Machine) (hm : compatible (parent a1 b1 c1 f0 bw) m) :
    NeverHalts m := by
  intro n
  obtain ⟨c,hc0,_⟩ := live_all a1 b1 c1 f0 bw ha hb hc he m hm n
  simp [hc0]

/-- Concrete executable source-pattern example of the full theorem. -/
def witness : PartialMachine :=
  parent ⟨false,false,0⟩ ⟨false,false,0⟩
    ⟨false,false,0⟩ ⟨false,false,0⟩ false

theorem witness_never (m : Machine)
    (hm : compatible witness m) : NeverHalts m := by
  exact never _ _ _ _ _ (by decide) (by decide)
    (by decide) (by decide) m hm

#print axioms safe_move_inv
#print axioms zero_entry_F
#print axioms live_step
#print axioms live_all
#print axioms never
#print axioms witness_never
end BB6.Agent50Raw34ZeroGuardedF
