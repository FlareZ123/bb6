import Frontier
import Lean.Elab.Tactic.Omega
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace BB6.Agent50Raw34InitialZeroGuardF
open BB6Coverage

/-!
Guard at initial state A: at the blank start the cell immediately
left of A's head is 0. Every later transition into A is forced to be
0RA, preserving that 0 predecessor. A1=(bw,L,F) consequently enters
F scanning a 0, and F1 is never read (even if assigned HALT).

Other source fixed rows are B0=1RC C0=0RD D0=1LC, A0=1RB.
The unrestricted A1,B1,C1,D1,F0 root entries are allocated as
A1 left into F, B1/C1/D1/F0 any of 12 ordinary moves to B,C,D
or the special guarded A-entry move 0RA. F1,E0,E1 are free.
-/

def safeMove (v : Move) : Prop :=
  v.next = 1 ∨ v.next = 2 ∨ v.next = 3 ∨
    v = ⟨false,true,0⟩

def parent (b1 c1 d1 f0 : Move) (bw : Bool) : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 0,true  => some (some ⟨bw,false,5⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 1,true  => some (some b1)
  | 2,false => some (some ⟨false,true,3⟩)
  | 2,true  => some (some c1)
  | 3,false => some (some ⟨true,false,2⟩)
  | 3,true  => some (some d1)
  | 5,false => some (some f0)
  | _,_ => none

def Inv (c : Config) : Prop :=
  c.state = 1 ∨ c.state = 2 ∨ c.state = 3 ∨
  (c.state = 0 ∧ c.tape (c.head-1) = false) ∨
  (c.state = 5 ∧ c.tape c.head = false)

/-- Unlike the other guarded families, initial A itself requires
    the marked-neighbor invariant. Blank tape supplies that mark. -/
theorem blank_inv : Inv blank := by
  right; right; right; left
  exact ⟨rfl, rfl⟩

theorem safe_move_inv (c : Config) (v : Move)
    (hv : safeMove v) : Inv (applyMove c v) := by
  rcases hv with hB | hC | hD | hA
  · simp [Inv,applyMove,hB]
  · simp [Inv,applyMove,hC]
  · simp [Inv,applyMove,hD]
  · subst v
    right; right; right; left
    refine ⟨rfl, ?_⟩
    have haddr : c.head + (1 : Int) - 1 = c.head := by omega
    simp [applyMove,haddr]

theorem marked_enter_F (c : Config) (bw : Bool)
    (h : c.tape (c.head - 1) = false) :
    Inv (applyMove c ⟨bw,false,5⟩) := by
  right; right; right; right
  refine ⟨rfl, ?_⟩
  have haddr : c.head + (-1 : Int) = c.head - 1 := by omega
  have hneq : c.head - 1 ≠ c.head := by omega
  simpa [applyMove,haddr,hneq] using h

theorem live_step
    (b1 c1 d1 f0 : Move) (bw : Bool)
    (hb : safeMove b1) (hc : safeMove c1)
    (hd : safeMove d1) (he : safeMove f0)
    (m : Machine) (hm : compatible (parent b1 c1 d1 f0 bw) m)
    (c : Config) (hI : Inv c) :
    ∃ d, rawStep m c = some d ∧ Inv d := by
  rcases c with ⟨q,h,T⟩
  have emit (v : Move) (hv : m (q,T h) = some v)
      (hs : Inv (applyMove ⟨q,h,T⟩ v)) :
      ∃ d, rawStep m ⟨q,h,T⟩ = some d ∧ Inv d := by
    refine ⟨applyMove ⟨q,h,T⟩ v, ?_, hs⟩
    simp [rawStep, readSlot, hv]
  change q = 1 ∨ q = 2 ∨ q = 3 ∨
    (q = 0 ∧ T (h-1) = false) ∨
    (q = 5 ∧ T h = false) at hI
  rcases hI with hB | hC | hD | hA | hE
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
  · rcases hA with ⟨hq, hzero⟩
    subst q
    cases hbit : T h with
    | false =>
      have hmv : m (0,T h) = some ⟨true,true,1⟩ := by
        simpa [hbit] using
          (hm (0,false) (some (⟨true,true,1⟩ : Move)) (by rfl))
      exact emit ⟨true,true,1⟩ hmv
        (safe_move_inv _ _ (by simp [safeMove]))
    | true =>
      have hmv : m (0,T h) = some ⟨bw,false,5⟩ := by
        simpa [hbit] using
          (hm (0,true) (some (⟨bw,false,5⟩ : Move)) (by rfl))
      exact emit ⟨bw,false,5⟩ hmv (marked_enter_F _ bw hzero)
  · rcases hE with ⟨hq, hzero⟩
    subst q
    have hmv : m (5,T h) = some f0 := by
      simpa [hzero] using (hm (5,false) (some f0) (by rfl))
    exact emit f0 hmv (safe_move_inv _ _ he)

theorem live_all
    (b1 c1 d1 f0 : Move) (bw : Bool)
    (hb : safeMove b1) (hc : safeMove c1)
    (hd : safeMove d1) (he : safeMove f0)
    (m : Machine) (hm : compatible (parent b1 c1 d1 f0 bw) m) :
    ∀ n, ∃ c, run m n blank = some c ∧ Inv c := by
  intro n
  induction n with
  | zero => exact ⟨blank, rfl, blank_inv⟩
  | succ n ih =>
    obtain ⟨c,hc0,hi⟩ := ih
    obtain ⟨d,hstep,hd0⟩ :=
      live_step b1 c1 d1 f0 bw hb hc hd he m hm c hi
    exact ⟨d, by simp [run,hc0,hstep], hd0⟩

theorem never
    (b1 c1 d1 f0 : Move) (bw : Bool)
    (hb : safeMove b1) (hc : safeMove c1)
    (hd : safeMove d1) (he : safeMove f0)
    (m : Machine) (hm : compatible (parent b1 c1 d1 f0 bw) m) :
    NeverHalts m := by
  intro n
  obtain ⟨c,hc0,_⟩ := live_all b1 c1 d1 f0 bw hb hc hd he m hm n
  simp [hc0]

def witness : PartialMachine :=
  parent ⟨false,false,1⟩ ⟨false,false,1⟩
    ⟨false,false,1⟩ ⟨false,false,1⟩ false

theorem witness_never (m : Machine)
    (hm : compatible witness m) : NeverHalts m := by
  exact never _ _ _ _ _ (by decide) (by decide)
    (by decide) (by decide) m hm

#print axioms blank_inv
#print axioms safe_move_inv
#print axioms marked_enter_F
#print axioms live_step
#print axioms live_all
#print axioms never
#print axioms witness_never
end BB6.Agent50Raw34InitialZeroGuardF
