import Frontier
import Lean.Elab.Tactic.Omega
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace BB6.Agent50Raw34CausalGuardF
open BB6Coverage

/-!
A two-stage causal invariant, beyond a one-cell control-graph criterion.

The first Raw34 moves have B0=1RC and C0=0RD. Whenever C is entered
from B, 1RC marks C's immediate left neighbor as 1. Whenever C
is entered from D via D0=1LC (or a permitted D1=0LC/1LC), the source
D predecessor's left-neighbor was 0 from a prior 0RD, hence C
directly scans 0. Therefore C1=(bw,L,F) can only be executed if its
left neighbor is 1, and F then scans 1. F0 is unreachable even when
it is assigned HALT. The unrestricted tape outside these guards
may be arbitrarily large.
-/

/-- Moves from A, B and F1 may stay inside A/B, or enter C with a
    marked-1 predecessor via 1RC, or enter D with marked-0 via 0RD. -/
def safeMove (v : Move) : Prop :=
  v.next = 0 ∨ v.next = 1 ∨
  v = ⟨true,true,2⟩ ∨ v = ⟨false,true,3⟩

/-- D's second action may also return leftward directly into C.
    Since D has a marked zero one cell left, C then scans zero. -/
def dSafeMove (v : Move) : Prop :=
  safeMove v ∨ v = ⟨false,false,2⟩ ∨ v = ⟨true,false,2⟩

def parent (a1 b1 d1 f1 : Move) (bw : Bool) : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 0,true  => some (some a1)
  | 1,false => some (some ⟨true,true,2⟩)
  | 1,true  => some (some b1)
  | 2,false => some (some ⟨false,true,3⟩)
  | 2,true  => some (some ⟨bw,false,5⟩)
  | 3,false => some (some ⟨true,false,2⟩)
  | 3,true  => some (some d1)
  | 5,true  => some (some f1)
  | _,_ => none

/-- For C, either C is scanning 0, or its immediate left cell is
    known to be 1. For D, the immediate left cell is known to be 0.
    For F, the scanned symbol is 1. A/B have no tape constraint. -/
def Inv (c : Config) : Prop :=
  c.state = 0 ∨ c.state = 1 ∨
  (c.state = 2 ∧
    (c.tape c.head = false ∨ c.tape (c.head-1) = true)) ∨
  (c.state = 3 ∧ c.tape (c.head-1) = false) ∨
  (c.state = 5 ∧ c.tape c.head = true)

theorem blank_inv : Inv blank := by
  left
  rfl

theorem safe_move_inv (c : Config) (v : Move)
    (hv : safeMove v) : Inv (applyMove c v) := by
  rcases hv with hA | hB | hC | hD
  · simp [Inv,applyMove,hA]
  · simp [Inv,applyMove,hB]
  · subst v
    right; right; left
    refine ⟨rfl, Or.inr ?_⟩
    have haddr : c.head + (1 : Int) - 1 = c.head := by omega
    simp [applyMove,haddr]
  · subst v
    right; right; right; left
    refine ⟨rfl, ?_⟩
    have haddr : c.head + (1 : Int) - 1 = c.head := by omega
    simp [applyMove,haddr]

/-- D, whose left-neighbor was set to 0 upon entering from 0RD,
    can turn left into C and force C's scanned symbol to zero. -/
theorem return_C (c : Config) (bw : Bool)
    (hzero : c.tape (c.head - 1) = false) :
    Inv (applyMove c ⟨bw,false,2⟩) := by
  right; right; left
  refine ⟨rfl, Or.inl ?_⟩
  have haddr : c.head + (-1 : Int) = c.head - 1 := by omega
  have hneq : c.head - 1 ≠ c.head := by omega
  simpa [applyMove,haddr,hneq] using hzero

/-- C1 has been reached reading 1, so C's left neighbor is
    necessarily marked 1; a left-moving C1 then enters E1. -/
theorem enter_F (c : Config) (bw : Bool)
    (hleft : c.tape (c.head - 1) = true) :
    Inv (applyMove c ⟨bw,false,5⟩) := by
  right; right; right; right
  refine ⟨rfl, ?_⟩
  have haddr : c.head + (-1 : Int) = c.head - 1 := by omega
  have hneq : c.head - 1 ≠ c.head := by omega
  simpa [applyMove,haddr,hneq] using hleft

theorem live_step
    (a1 b1 d1 f1 : Move) (bw : Bool)
    (ha : safeMove a1) (hb : safeMove b1)
    (hd : dSafeMove d1) (he : safeMove f1)
    (m : Machine) (hm : compatible (parent a1 b1 d1 f1 bw) m)
    (c : Config) (hI : Inv c) :
    ∃ d, rawStep m c = some d ∧ Inv d := by
  rcases c with ⟨q,h,T⟩
  have emit (v : Move) (hv : m (q,T h) = some v)
      (hs : Inv (applyMove ⟨q,h,T⟩ v)) :
      ∃ d, rawStep m ⟨q,h,T⟩ = some d ∧ Inv d := by
    refine ⟨applyMove ⟨q,h,T⟩ v, ?_, hs⟩
    simp [rawStep, readSlot, hv]
  change q = 0 ∨ q = 1 ∨
    (q = 2 ∧ (T h = false ∨ T (h-1) = true)) ∨
    (q = 3 ∧ T (h-1) = false) ∨
    (q = 5 ∧ T h = true) at hI
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
  · rcases hC with ⟨hq, hc⟩
    subst q
    cases hbit : T h with
    | false =>
      have hmv : m (2,T h) = some ⟨false,true,3⟩ := by
        simpa [hbit] using
          (hm (2,false) (some (⟨false,true,3⟩ : Move)) (by rfl))
      exact emit ⟨false,true,3⟩ hmv
        (safe_move_inv _ _ (by simp [safeMove]))
    | true =>
      have hleft : T (h-1) = true := by
        rcases hc with hzero | hleft
        · rw [hbit] at hzero
          cases hzero
        · exact hleft
      have hmv : m (2,T h) = some ⟨bw,false,5⟩ := by
        simpa [hbit] using
          (hm (2,true) (some (⟨bw,false,5⟩ : Move)) (by rfl))
      exact emit ⟨bw,false,5⟩ hmv (enter_F _ bw hleft)
  · rcases hD with ⟨hq, hzero⟩
    subst q
    cases hbit : T h with
    | false =>
      have hmv : m (3,T h) = some ⟨true,false,2⟩ := by
        simpa [hbit] using
          (hm (3,false) (some (⟨true,false,2⟩ : Move)) (by rfl))
      exact emit ⟨true,false,2⟩ hmv (return_C _ true hzero)
    | true =>
      have hmv : m (3,T h) = some d1 := by
        simpa [hbit] using (hm (3,true) (some d1) (by rfl))
      rcases hd with hs | hz | ho
      · exact emit d1 hmv (safe_move_inv _ _ hs)
      · subst d1
        exact emit ⟨false,false,2⟩ hmv (return_C _ false hzero)
      · subst d1
        exact emit ⟨true,false,2⟩ hmv (return_C _ true hzero)
  · rcases hE with ⟨hq, hmarked⟩
    subst q
    have hmv : m (5,T h) = some f1 := by
      simpa [hmarked] using (hm (5,true) (some f1) (by rfl))
    exact emit f1 hmv (safe_move_inv _ _ he)

theorem live_all
    (a1 b1 d1 f1 : Move) (bw : Bool)
    (ha : safeMove a1) (hb : safeMove b1)
    (hd : dSafeMove d1) (he : safeMove f1)
    (m : Machine) (hm : compatible (parent a1 b1 d1 f1 bw) m) :
    ∀ n, ∃ c, run m n blank = some c ∧ Inv c := by
  intro n
  induction n with
  | zero => exact ⟨blank, rfl, blank_inv⟩
  | succ n ih =>
    obtain ⟨c,hc0,hi⟩ := ih
    obtain ⟨d,hstep,hd0⟩ :=
      live_step a1 b1 d1 f1 bw ha hb hd he m hm c hi
    exact ⟨d, by simp [run,hc0,hstep], hd0⟩

theorem never
    (a1 b1 d1 f1 : Move) (bw : Bool)
    (ha : safeMove a1) (hb : safeMove b1)
    (hd : dSafeMove d1) (he : safeMove f1)
    (m : Machine) (hm : compatible (parent a1 b1 d1 f1 bw) m) :
    NeverHalts m := by
  intro n
  obtain ⟨c,hc0,_⟩ := live_all a1 b1 d1 f1 bw ha hb hd he m hm n
  simp [hc0]

/-- An example with F0 explicitly free: all of its completions never halt. -/
def witness : PartialMachine :=
  parent ⟨false,false,0⟩ ⟨false,false,0⟩
    ⟨false,false,2⟩ ⟨false,false,0⟩ false

theorem witness_never (m : Machine)
    (hm : compatible witness m) : NeverHalts m := by
  exact never _ _ _ _ _ (by simp [safeMove]) (by simp [safeMove])
    (by simp [dSafeMove,safeMove]) (by simp [safeMove]) m hm

#print axioms safe_move_inv
#print axioms return_C
#print axioms enter_F
#print axioms live_step
#print axioms live_all
#print axioms never
#print axioms witness_never
end BB6.Agent50Raw34CausalGuardF
