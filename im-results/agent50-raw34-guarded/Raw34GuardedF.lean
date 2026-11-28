import Frontier
import Lean.Elab.Tactic.Omega
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace BB6.Agent50Raw34GuardedF
open BB6Coverage

/-!
A local *tape-sensitive*, universally nonhalting Raw34 certificate.

The source fixes A0=1RB, B0=1RC, C0=0RD, D0=1LC, and
B1=(write b, L, F). Other assigned instructions A1,C1,D1,F1
may be any ordinary move to A,C,D or exactly 1RB.
F0 and E0,E1 are arbitrary/unassigned.

Every transition entering B is 1RB and thus writes a 1 immediately
to the left of B's head. Consequently when B1 enters F by moving
left, F always reads 1. F0 is unreachable in EVERY compatible total
machine, even if it is HALT. State E is likewise unreachable.

This avoids simulation horizons or hypotheses about distant tape
symbols, and works for arbitrary tape growth/counters.
-/

/-- Ordinary target A,C,D, or a protected jump into B which writes
    a 1 on the cell immediately to the left of B's new head. -/
def safeMove (v : Move) : Prop :=
  v.next = 0 ∨ v.next = 2 ∨ v.next = 3 ∨
    v = ⟨true,true,1⟩

/-- F0, E0, and E1 deliberately unassigned. The four variable
    instructions a1,c1,d1,f1 range over all safeMove values. -/
def parent (a1 c1 d1 f1 : Move) (bw : Bool) : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 0,true  => some (some a1)
  | 1,false => some (some ⟨true,true,2⟩)
  | 1,true  => some (some ⟨bw,false,5⟩)
  | 2,false => some (some ⟨false,true,3⟩)
  | 2,true  => some (some c1)
  | 3,false => some (some ⟨true,false,2⟩)
  | 3,true  => some (some d1)
  | 5,true  => some (some f1)
  | _,_ => none

/-- States A,C,D are unrestricted. B must have a marked cell
    immediately left; F must currently be scanning a marked cell.
    E is not in the invariant. -/
def Inv (c : Config) : Prop :=
  c.state = 0 ∨ c.state = 2 ∨ c.state = 3 ∨
  (c.state = 1 ∧ c.tape (c.head-1) = true) ∨
  (c.state = 5 ∧ c.tape c.head = true)

theorem blank_inv : Inv blank := by
  left
  rfl

/-- Any safeMove lands inside the invariant, independently of tape. -/
theorem safe_move_inv (c : Config) (v : Move)
    (hv : safeMove v) : Inv (applyMove c v) := by
  rcases hv with h0 | h2 | h3 | hB
  · simp [Inv,applyMove,h0]
  · simp [Inv,applyMove,h2]
  · simp [Inv,applyMove,h3]
  · subst v
    right; right; right; left
    refine ⟨rfl, ?_⟩
    have haddr : c.head + (1 : Int) - 1 = c.head := by omega
    simp [applyMove,haddr]

/-- B1 moves one cell left into F without altering the marked
    predecessor. Its write bit may be either 0 or 1. -/
theorem guarded_enter_F (c : Config) (bw : Bool)
    (h : c.tape (c.head - 1) = true) :
    Inv (applyMove c ⟨bw,false,5⟩) := by
  right; right; right; right
  refine ⟨rfl, ?_⟩
  have haddr : c.head + (-1 : Int) = c.head - 1 := by omega
  have hneq : c.head - 1 ≠ c.head := by omega
  simpa [applyMove,haddr,hneq] using h

/-- Source-original, arbitrary-tape one-step inductive closure.
    No potential HALT instruction in F0 or E is consulted. -/
theorem live_step
    (a1 c1 d1 f1 : Move) (bw : Bool)
    (ha : safeMove a1) (hc : safeMove c1)
    (hd : safeMove d1) (he : safeMove f1)
    (m : Machine) (hm : compatible (parent a1 c1 d1 f1 bw) m)
    (c : Config) (hI : Inv c) :
    ∃ d, rawStep m c = some d ∧ Inv d := by
  rcases c with ⟨q,h,T⟩
  have emit (v : Move) (hv : m (q,T h) = some v)
      (hs : Inv (applyMove ⟨q,h,T⟩ v)) :
      ∃ d, rawStep m ⟨q,h,T⟩ = some d ∧ Inv d := by
    refine ⟨applyMove ⟨q,h,T⟩ v, ?_, hs⟩
    simp [rawStep, readSlot, hv]
  change q = 0 ∨ q = 2 ∨ q = 3 ∨
    (q = 1 ∧ T (h-1) = true) ∨
    (q = 5 ∧ T h = true) at hI
  rcases hI with hA | hC | hD | hB | hE
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
      have hmv : m (2,T h) = some ⟨false,true,3⟩ := by
        simpa [hbit] using
          (hm (2,false) (some (⟨false,true,3⟩ : Move)) (by rfl))
      exact emit ⟨false,true,3⟩ hmv
        (safe_move_inv _ _ (by simp [safeMove]))
    | true =>
      have hmv : m (2,T h) = some c1 := by
        simpa [hbit] using (hm (2,true) (some c1) (by rfl))
      exact emit c1 hmv (safe_move_inv _ _ hc)
  · subst q
    cases hbit : T h with
    | false =>
      have hmv : m (3,T h) = some ⟨true,false,2⟩ := by
        simpa [hbit] using
          (hm (3,false) (some (⟨true,false,2⟩ : Move)) (by rfl))
      exact emit ⟨true,false,2⟩ hmv
        (safe_move_inv _ _ (by simp [safeMove]))
    | true =>
      have hmv : m (3,T h) = some d1 := by
        simpa [hbit] using (hm (3,true) (some d1) (by rfl))
      exact emit d1 hmv (safe_move_inv _ _ hd)
  · rcases hB with ⟨hq, hmarked⟩
    subst q
    cases hbit : T h with
    | false =>
      have hmv : m (1,T h) = some ⟨true,true,2⟩ := by
        simpa [hbit] using
          (hm (1,false) (some (⟨true,true,2⟩ : Move)) (by rfl))
      exact emit ⟨true,true,2⟩ hmv
        (safe_move_inv _ _ (by simp [safeMove]))
    | true =>
      have hmv : m (1,T h) = some ⟨bw,false,5⟩ := by
        simpa [hbit] using
          (hm (1,true) (some (⟨bw,false,5⟩ : Move)) (by rfl))
      exact emit ⟨bw,false,5⟩ hmv
        (guarded_enter_F _ bw hmarked)
  · rcases hE with ⟨hq, hmarked⟩
    subst q
    have hmv : m (5,T h) = some f1 := by
      simpa [hmarked] using (hm (5,true) (some f1) (by rfl))
    exact emit f1 hmv (safe_move_inv _ _ he)

/-- The invariant holds at every actual blank-tape time, for every
    compatible total machine. -/
theorem live_all
    (a1 c1 d1 f1 : Move) (bw : Bool)
    (ha : safeMove a1) (hc : safeMove c1)
    (hd : safeMove d1) (he : safeMove f1)
    (m : Machine) (hm : compatible (parent a1 c1 d1 f1 bw) m) :
    ∀ n, ∃ c, run m n blank = some c ∧ Inv c := by
  intro n
  induction n with
  | zero => exact ⟨blank, rfl, blank_inv⟩
  | succ n ih =>
    obtain ⟨c,hc0,hi⟩ := ih
    obtain ⟨d,hstep,hd0⟩ :=
      live_step a1 c1 d1 f1 bw ha hc hd he m hm c hi
    exact ⟨d, by simp [run,hc0,hstep], hd0⟩

/-- Every completion of these 9 known instructions never halts.
    It is valid even when F0, E0, or E1 are assigned HALT. -/
theorem never
    (a1 c1 d1 f1 : Move) (bw : Bool)
    (ha : safeMove a1) (hc : safeMove c1)
    (hd : safeMove d1) (he : safeMove f1)
    (m : Machine) (hm : compatible (parent a1 c1 d1 f1 bw) m) :
    NeverHalts m := by
  intro n
  obtain ⟨c,hc0,_⟩ := live_all a1 c1 d1 f1 bw ha hc hd he m hm n
  simp [hc0]

/-- The first nontrivial counter-like holdout found by the depth-three
    Raw34 D1=0LD / C1=0LA exploratory split, completely discharged. -/
def witnessA : PartialMachine :=
  parent ⟨true,false,0⟩ ⟨false,false,0⟩
    ⟨false,false,3⟩ ⟨true,true,0⟩ false

theorem witnessA_never (m : Machine)
    (hm : compatible witnessA m) : NeverHalts m := by
  exact never _ _ _ _ _ (by decide) (by decide) (by decide)
    (by decide) m hm

/-- A distinct F1=0RC, A1=1RA right-moving counter-like holdout. -/
def witnessB : PartialMachine :=
  parent ⟨true,true,0⟩ ⟨false,false,0⟩
    ⟨false,false,3⟩ ⟨false,true,2⟩ false

theorem witnessB_never (m : Machine)
    (hm : compatible witnessB m) : NeverHalts m := by
  exact never _ _ _ _ _ (by decide) (by decide) (by decide)
    (by decide) m hm

#print axioms blank_inv
#print axioms safe_move_inv
#print axioms guarded_enter_F
#print axioms live_step
#print axioms live_all
#print axioms never
#print axioms witnessA_never
#print axioms witnessB_never
end BB6.Agent50Raw34GuardedF
