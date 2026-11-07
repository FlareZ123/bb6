import Root119Gate
import Root119PrefixShield

namespace BB6Root119

/--
A seven-cell abstraction centered at the head.  The edge bit is arbitrary:
when the head moves, only the newly exposed endpoint is used.
-/
structure WindowState where
  q : Q
  b0 : Bool
  b1 : Bool
  b2 : Bool
  b3 : Bool
  b4 : Bool
  b5 : Bool
  b6 : Bool
  deriving DecidableEq, Repr

def windowOf (c : Conf) : WindowState :=
  ⟨c.q, c.tape (c.h-3), c.tape (c.h-2), c.tape (c.h-1),
    c.tape c.h, c.tape (c.h+1), c.tape (c.h+2), c.tape (c.h+3)⟩

/-- Abstract one-step transition, with the newly exposed tape cell arbitrary. -/
def windowNext (w : WindowState) (edge : Bool) : Option WindowState :=
  match w.q, w.b3 with
  | .A, true => none
  | .A, false => some ⟨.B,w.b1,w.b2,true,w.b4,w.b5,w.b6,edge⟩
  | .B, false => some ⟨.C,edge,w.b0,w.b1,w.b2,true,w.b4,w.b5⟩
  | .B, true => some ⟨.F,edge,w.b0,w.b1,w.b2,true,w.b4,w.b5⟩
  | .C, false => some ⟨.D,edge,w.b0,w.b1,w.b2,true,w.b4,w.b5⟩
  | .C, true => some ⟨.C,edge,w.b0,w.b1,w.b2,false,w.b4,w.b5⟩
  | .D, false => some ⟨.E,edge,w.b0,w.b1,w.b2,false,w.b4,w.b5⟩
  | .D, true => some ⟨.F,w.b1,w.b2,true,w.b4,w.b5,w.b6,edge⟩
  | .E, false => some ⟨.A,w.b1,w.b2,true,w.b4,w.b5,w.b6,edge⟩
  | .E, true => some ⟨.A,edge,w.b0,w.b1,w.b2,true,w.b4,w.b5⟩
  | .F, false => some ⟨.B,edge,w.b0,w.b1,w.b2,true,w.b4,w.b5⟩
  | .F, true => some ⟨.D,w.b1,w.b2,false,w.b4,w.b5,w.b6,edge⟩

/--
The complete reverse-reachable set of the two forbidden B0 windows
1010000 and 1010110 in this seven-cell abstraction.  It has 12 states.
-/
def badWindows : List WindowState :=
  [ ⟨.A,false,true,false,false,false,false,false⟩
  , ⟨.A,true,true,false,false,false,false,false⟩
  , ⟨.A,false,true,false,false,false,true,true⟩
  , ⟨.A,true,true,false,false,false,true,true⟩
  , ⟨.B,true,false,true,false,false,false,false⟩
  , ⟨.B,true,false,false,true,false,false,false⟩
  , ⟨.B,true,false,false,true,false,true,false⟩
  , ⟨.B,true,false,true,false,true,true,false⟩
  , ⟨.B,true,false,false,true,false,false,true⟩
  , ⟨.B,true,false,false,true,false,true,true⟩
  , ⟨.F,false,true,false,false,true,false,false⟩
  , ⟨.F,false,true,false,false,true,false,true⟩
  ]

/-- If an abstract successor is in the bad set, its predecessor is too. -/
theorem bad_preimage_closed (w : WindowState) (edge : Bool) (w' : WindowState)
    (hnext : windowNext w edge = some w') (hbad : w' ∈ badWindows) :
    w ∈ badWindows := by
  simp [badWindows] at hbad
  rcases hbad with hbad | hbad | hbad | hbad | hbad | hbad |
    hbad | hbad | hbad | hbad | hbad | hbad
  all_goals subst w'
  all_goals
    cases w with
    | mk q b0 b1 b2 b3 b4 b5 b6 =>
      cases q <;> cases b3 <;>
        simp [windowNext] at hnext ⊢
      all_goals cases b0 <;> cases b5 <;> cases b6 <;> simp_all [badWindows]

theorem windowOf_right (q : Q) (h : Int) (t : Int → Bool) (w : Bool) :
    windowOf ⟨q,h+1,setBit t h w⟩ =
      ⟨q,t (h-2),t (h-1),w,t (h+1),t (h+2),t (h+3),t (h+4)⟩ := by
  dsimp [windowOf]
  rw [show h+1-3 = h-2 by omega,
      show h+1-2 = h-1 by omega,
      show h+1-1 = h by omega,
      show h+1+1 = h+2 by omega,
      show h+1+2 = h+3 by omega,
      show h+1+3 = h+4 by omega]
  simp [setBit,
    show h-2 ≠ h by omega,
    show h-1 ≠ h by omega,
    show h+1 ≠ h by omega,
    show h+2 ≠ h by omega,
    show h+3 ≠ h by omega,
    show h+4 ≠ h by omega]

theorem windowOf_left (q : Q) (h : Int) (t : Int → Bool) (w : Bool) :
    windowOf ⟨q,h-1,setBit t h w⟩ =
      ⟨q,t (h-4),t (h-3),t (h-2),t (h-1),w,t (h+1),t (h+2)⟩ := by
  dsimp [windowOf]
  rw [show h-1-3 = h-4 by omega,
      show h-1-2 = h-3 by omega,
      show h-1-1 = h-2 by omega,
      show h-1+1 = h by omega,
      show h-1+2 = h+1 by omega,
      show h-1+3 = h+2 by omega]
  simp [setBit,
    show h-4 ≠ h by omega,
    show h-3 ≠ h by omega,
    show h-2 ≠ h by omega,
    show h-1 ≠ h by omega,
    show h+1 ≠ h by omega,
    show h+2 ≠ h by omega]

/-- Every concrete machine step induces one of the abstract window steps. -/
theorem windowOf_next (c d : Conf) (hstep : next c = some d) :
    ∃ edge, windowNext (windowOf c) edge = some (windowOf d) := by
  rcases c with ⟨q,h,t⟩
  cases q with
  | A =>
    cases hs : t h with
    | true => simp [next,hs] at hstep
    | false =>
      simp [next,hs] at hstep
      cases hstep
      refine ⟨t (h+4), ?_⟩
      rw [windowOf_right]
      simp [windowNext,windowOf,hs]
  | B =>
    cases hs : t h with
    | false =>
      simp [next,hs] at hstep
      cases hstep
      refine ⟨t (h-4), ?_⟩
      rw [windowOf_left]
      simp [windowNext,windowOf,hs]
    | true =>
      simp [next,hs] at hstep
      cases hstep
      refine ⟨t (h-4), ?_⟩
      rw [windowOf_left]
      simp [windowNext,windowOf,hs]
  | C =>
    cases hs : t h with
    | false =>
      simp [next,hs] at hstep
      cases hstep
      refine ⟨t (h-4), ?_⟩
      rw [windowOf_left]
      simp [windowNext,windowOf,hs]
    | true =>
      simp [next,hs] at hstep
      cases hstep
      refine ⟨t (h-4), ?_⟩
      rw [windowOf_left]
      simp [windowNext,windowOf,hs]
  | D =>
    cases hs : t h with
    | false =>
      simp [next,hs] at hstep
      cases hstep
      refine ⟨t (h-4), ?_⟩
      rw [windowOf_left]
      simp [windowNext,windowOf,hs]
    | true =>
      simp [next,hs] at hstep
      cases hstep
      refine ⟨t (h+4), ?_⟩
      rw [windowOf_right]
      simp [windowNext,windowOf,hs]
  | E =>
    cases hs : t h with
    | false =>
      simp [next,hs] at hstep
      cases hstep
      refine ⟨t (h+4), ?_⟩
      rw [windowOf_right]
      simp [windowNext,windowOf,hs]
    | true =>
      simp [next,hs] at hstep
      cases hstep
      refine ⟨t (h-4), ?_⟩
      rw [windowOf_left]
      simp [windowNext,windowOf,hs]
  | F =>
    cases hs : t h with
    | false =>
      simp [next,hs] at hstep
      cases hstep
      refine ⟨t (h-4), ?_⟩
      rw [windowOf_left]
      simp [windowNext,windowOf,hs]
    | true =>
      simp [next,hs] at hstep
      cases hstep
      refine ⟨t (h+4), ?_⟩
      rw [windowOf_right]
      simp [windowNext,windowOf,hs]

/-- No blank-reachable concrete configuration has a window in badWindows. -/
theorem windowOf_reach_notBad (c : Conf) (hr : Reach c) :
    windowOf c ∉ badWindows := by
  induction hr with
  | initial =>
      simp [windowOf,blank,badWindows]
  | @follow u v hu hstep ih =>
      obtain ⟨edge,hwindow⟩ := windowOf_next u v hstep
      intro hbad
      have hprev : windowOf u ∈ badWindows :=
        bad_preimage_closed (windowOf u) edge (windowOf v) hwindow hbad
      exact ih hprev

/-- A reachable B0 head with left context 101 cannot have right context 000. -/
theorem Reach_no_B0_prefix101_right000 (c : Conf) (hr : Reach c)
    (hq : c.q = .B) (h0 : c.tape c.h = false)
    (hleft1 : c.tape (c.h-1) = true)
    (hleft2 : c.tape (c.h-2) = false)
    (hleft3 : c.tape (c.h-3) = true)
    (hright1 : c.tape (c.h+1) = false)
    (hright2 : c.tape (c.h+2) = false)
    (hright3 : c.tape (c.h+3) = false) : False := by
  have hmem : windowOf c ∈ badWindows := by
    simp [windowOf,badWindows,hq,h0,hleft1,hleft2,hleft3,hright1,hright2,hright3]
  exact (windowOf_reach_notBad c hr) hmem

/-- A reachable B0 head with left context 101 cannot have right context 110. -/
theorem Reach_no_B0_prefix101_right110 (c : Conf) (hr : Reach c)
    (hq : c.q = .B) (h0 : c.tape c.h = false)
    (hleft1 : c.tape (c.h-1) = true)
    (hleft2 : c.tape (c.h-2) = false)
    (hleft3 : c.tape (c.h-3) = true)
    (hright1 : c.tape (c.h+1) = true)
    (hright2 : c.tape (c.h+2) = true)
    (hright3 : c.tape (c.h+3) = false) : False := by
  have hmem : windowOf c ∈ badWindows := by
    simp [windowOf,badWindows,hq,h0,hleft1,hleft2,hleft3,hright1,hright2,hright3]
  exact (windowOf_reach_notBad c hr) hmem

/-- The synthetic n = 0 shield counterexample is not blank-reachable. -/
theorem oddEvenShieldCounterexample_notReach :
    ¬ Reach oddEvenShieldCounterexample := by
  intro hR
  exact Reach_no_B0_prefix101_right000 oddEvenShieldCounterexample hR rfl
    (by simp [oddEvenShieldCounterexample,oddEvenShieldCounterexampleTape])
    (by simp [oddEvenShieldCounterexample,oddEvenShieldCounterexampleTape])
    (by simp [oddEvenShieldCounterexample,oddEvenShieldCounterexampleTape])
    (by simp [oddEvenShieldCounterexample,oddEvenShieldCounterexampleTape])
    (by simp [oddEvenShieldCounterexample,oddEvenShieldCounterexampleTape])
    (by simp [oddEvenShieldCounterexample,oddEvenShieldCounterexampleTape])
    (by simp [oddEvenShieldCounterexample,oddEvenShieldCounterexampleTape])

#print axioms bad_preimage_closed
#print axioms windowOf_reach_notBad
#print axioms Reach_no_B0_prefix101_right000
#print axioms Reach_no_B0_prefix101_right110
#print axioms oddEvenShieldCounterexample_notReach

end BB6Root119
