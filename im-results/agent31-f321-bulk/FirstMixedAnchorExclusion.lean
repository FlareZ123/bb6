import HighFarTerminalFamily
import Lean.Elab.Tactic.Omega

/-!
Root-specific exclusion of the first mixed H^22/F terminal anchor exposed by
the exact terminal-word equation.

The source-faithful suffix from anchor (19173934,1) is real, but this file
proves that the authentic root orbit cannot reach the only possible
MiddleOdd predecessor of that anchor.  The proof uses exact kernel-reduced
root checkpoints, determinism of CounterMove, strict sum growth, and an
analytic bound across the intervening High block.
-/

set_option maxRecDepth 100000

namespace BB6.Agent31F321FirstMixed
open BB6.Agent31F321Density
open BB6.Agent2F321Bulk
open BB6.Agent31F321HighFarFamily

/-- Local executable form of the exact five-branch CounterMove relation. -/
def rootStep (a d : Nat) : Option (Nat × Nat) :=
  if a ≥ d+2 then some (a-d-2,2*d+3)
  else if a = d+1 then none
  else if a = d then some (2*a+4,1)
  else if 3*a+1 ≤ d then some (4*a+6,d-3*a)
  else if (d-a)%2 = 0 then some (4*a+6,2)
  else some (4*a+6,1)

theorem rootStep_some_of_move {a d A D : Nat}
    (h : CounterMove a d A D) : rootStep a d = some (A,D) := by
  cases h with
  | high d hg => simp [rootStep,hg]
  | equal => simp [rootStep]
  | far d ha hd =>
      simp [rootStep,show ¬(a≥d+2) by omega,
        show ¬(a=d+1) by omega,show ¬(a=d) by omega,hd]
  | middleEven d ha hd hp =>
      simp [rootStep,show ¬(a≥d+2) by omega,
        show ¬(a=d+1) by omega,show ¬(a=d) by omega,
        show ¬(3*a+1≤d) by omega,hp]
  | middleOdd d ha hd hp =>
      simp [rootStep,show ¬(a≥d+2) by omega,
        show ¬(a=d+1) by omega,show ¬(a=d) by omega,
        show ¬(3*a+1≤d) by omega,show ¬((d-a)%2=0) by omega]

theorem move_of_rootStep_some {a d A D : Nat}
    (h : rootStep a d = some (A,D)) : CounterMove a d A D := by
  by_cases h1 : a≥d+2
  · have hp : (a-d-2,2*d+3)=(A,D) :=
      Option.some.inj (by simpa [rootStep,h1] using h)
    rcases Prod.mk.inj hp with ⟨ha,hd⟩
    subst A; subst D
    exact .high a d h1
  · by_cases h2 : a=d+1
    · simp [rootStep,h1,h2] at h
    · by_cases h3 : a=d
      · subst d
        have hp : (2*a+4,1)=(A,D) :=
          Option.some.inj (by simpa [rootStep,h1,h2] using h)
        rcases Prod.mk.inj hp with ⟨ha,hd⟩
        subst A; subst D
        exact .equal a
      · by_cases h4 : 3*a+1≤d
        · have hp : (4*a+6,d-3*a)=(A,D) :=
            Option.some.inj (by simpa [rootStep,h1,h2,h3,h4] using h)
          rcases Prod.mk.inj hp with ⟨ha,hd⟩
          subst A; subst D
          exact .far a d (by omega) h4
        · by_cases h5 : (d-a)%2=0
          · have hp : (4*a+6,2)=(A,D) :=
              Option.some.inj (by
                simpa [rootStep,h1,h2,h3,h4,h5] using h)
            rcases Prod.mk.inj hp with ⟨ha,hd⟩
            subst A; subst D
            exact .middleEven a d (by omega) (by omega) h5
          · have hp : (4*a+6,1)=(A,D) :=
              Option.some.inj (by
                simpa [rootStep,h1,h2,h3,h4,h5] using h)
            rcases Prod.mk.inj hp with ⟨ha,hd⟩
            subst A; subst D
            exact .middleOdd a d (by omega) (by omega) (by omega)

def rootIter : Nat → Nat → Nat → Option (Nat × Nat)
  | 0, a, d => some (a,d)
  | n+1, a, d =>
      (rootIter n a d).bind fun p => rootStep p.1 p.2

theorem rootIter_sound {n a d A D : Nat}
    (h : rootIter n a d = some (A,D)) :
    CounterReach a d n A D := by
  induction n generalizing A D with
  | zero =>
      simp [rootIter] at h
      rcases h with ⟨rfl,rfl⟩
      exact CounterReach.nil
  | succ n ih =>
      simp [rootIter] at h
      cases hx : rootIter n a d with
      | none => simp [hx] at h
      | some p =>
          simp [hx] at h
          have hr := ih hx
          exact CounterReach.step hr (move_of_rootStep_some h)

theorem counterMove_deterministic
    {a d A D B C : Nat}
    (h1 : CounterMove a d A D)
    (h2 : CounterMove a d B C) :
    A=B ∧ D=C := by
  have e1 := rootStep_some_of_move h1
  have e2 := rootStep_some_of_move h2
  rw [e1] at e2
  exact Prod.mk.inj (Option.some.inj e2)

theorem counterReach_deterministic
    {sa sd n A D B C : Nat}
    (h1 : CounterReach sa sd n A D)
    (h2 : CounterReach sa sd n B C) :
    A=B ∧ D=C := by
  induction h1 generalizing B C with
  | nil =>
      cases h2
      exact ⟨rfl,rfl⟩
  | @step n a d A D hr hm ih =>
      cases h2 with
      | @step _ b c B C hr2 hm2 =>
          rcases ih hr2 with ⟨rfl,rfl⟩
          exact counterMove_deterministic hm hm2

theorem counterReach_append
    {sa sd n a d m A D : Nat}
    (h1 : CounterReach sa sd n a d)
    (h2 : CounterReach a d m A D) :
    CounterReach sa sd (n+m) A D := by
  induction h2 with
  | nil => simpa using h1
  | step hr hm ih =>
      simpa [Nat.add_assoc] using CounterReach.step ih hm

theorem counterReach_sum_mono
    {sa sd n A D : Nat}
    (h : CounterReach sa sd n A D) :
    sa+sd ≤ A+D := by
  induction h with
  | nil => omega
  | step hr hm ih =>
      have hs := counter_sum_strict hm
      omega

theorem counterReach_split
    {sa sd n m A D : Nat}
    (h : CounterReach sa sd (n+m) A D) :
    ∃ a d,
      CounterReach sa sd n a d ∧ CounterReach a d m A D := by
  induction m generalizing A D with
  | zero =>
      exact ⟨A,D,by simpa using h,CounterReach.nil⟩
  | succ m ih =>
      rw [show n+(m+1)=(n+m)+1 by omega] at h
      cases h with
      | @step _ x y A D hp hm =>
          rcases ih hp with ⟨a,d,hpre,htail⟩
          exact ⟨a,d,hpre,by
            simpa [Nat.add_assoc] using CounterReach.step htail hm⟩

/-- Exact authentic root checkpoints, kernel-reduced by decide. -/
theorem root_at_404 :
    CounterReach 1 1 404 3501222 4194301 :=
  rootIter_sound (by decide)

theorem root_at_405 :
    CounterReach 1 1 405 14004894 1 :=
  rootIter_sound (by decide)

theorem root_at_427 :
    CounterReach 1 1 427 22465250 2 :=
  rootIter_sound (by decide)

theorem root_sum_before_405
    {n A D : Nat}
    (hn : n≤404)
    (hr : CounterReach 1 1 n A D) :
    A+D ≤ 7695523 := by
  obtain ⟨m,hm⟩ := Nat.exists_eq_add_of_le hn
  have h404 : CounterReach 1 1 (n+m) 3501222 4194301 := by
    simpa [←hm] using root_at_404
  rcases counterReach_split h404 with ⟨a,d,hpre,htail⟩
  rcases counterReach_deterministic hr hpre with ⟨rfl,rfl⟩
  have hs := counterReach_sum_mono htail
  omega

theorem root_sum_after_426
    {n A D : Nat}
    (hn : 427≤n)
    (hr : CounterReach 1 1 n A D) :
    22465252 ≤ A+D := by
  obtain ⟨m,rfl⟩ := Nat.exists_eq_add_of_le hn
  rcases counterReach_split hr with ⟨a,d,hpre,htail⟩
  rcases counterReach_deterministic root_at_427 hpre with ⟨rfl,rfl⟩
  have hs := counterReach_sum_mono htail
  omega

/-- Throughout the only time window in which the target predecessor sum could
    occur, the first counter stays above 5,616,290. -/
theorem root_middle_window_first_large
    {n A D : Nat}
    (hlo : 405≤n)
    (hhi : n≤426)
    (hr : CounterReach 1 1 n A D) :
    5616290 ≤ A := by
  obtain ⟨j,rfl⟩ := Nat.exists_eq_add_of_le hlo
  have hj : j≤21 := by omega
  have hpow : 2^j ≤ 2^21 :=
    Nat.pow_le_pow_right (by decide : 0<2) hj
  have h21 : 2^21 = 2097152 := by decide
  rw [h21] at hpow
  have hb : 2^j*(1+3) ≤ 14004894+1+4 := by omega
  rcases highRun_of_bound hb with ⟨A',D',hh,hA,hD⟩
  have hseg := highRun_counterReach_local hh
  have hroot : CounterReach 1 1 (405+j) A' D' :=
    counterReach_append root_at_405 hseg
  rcases counterReach_deterministic hr hroot with ⟨rfl,rfl⟩
  have hp4 : 4*2^j ≤ 8388608 := by omega
  simp at hA
  omega

/-- The only possible MiddleOdd predecessor first counter for anchor
    (19,173,934,1) is 4,793,482.  No authentic root state with the required
    MiddleOdd guard can have that first counter. -/
theorem first_mixed_anchor_middleOdd_predecessor_unreachable
    {n a d : Nat}
    (hr : CounterReach 1 1 n a d)
    (hR : 4*a+6=19173934)
    (h1 : a<d)
    (h2 : d<3*a+1) :
    False := by
  have ha : a=4793482 := by omega
  subst a
  by_cases hEarly : n≤404
  · have hs := root_sum_before_405 hEarly hr
    omega
  by_cases hLate : 427≤n
  · have hs := root_sum_after_426 hLate hr
    omega
  have hmid := root_middle_window_first_large (by omega) (by omega) hr
  omega

/-- Consequently the concrete H^22/F source-faithful terminal anchor cannot
    be produced by a reachable MiddleOdd reset from the authentic root. -/
theorem first_mixed_anchor_not_from_reachable_middleOdd
    {n a d : Nat}
    (hr : CounterReach 1 1 n a d)
    (hm : CounterMove a d 19173934 1)
    (ha : a<d) :
    False := by
  cases hm with
  | high d hg => omega
  | equal => omega
  | far d h1 h2 => omega
  | middleEven d h1 h2 hp => omega
  | middleOdd d h1 h2 hp =>
      exact first_mixed_anchor_middleOdd_predecessor_unreachable
        hr rfl h1 h2

#print axioms root_at_404
#print axioms root_at_405
#print axioms root_at_427
#print axioms counterReach_deterministic
#print axioms first_mixed_anchor_middleOdd_predecessor_unreachable
#print axioms first_mixed_anchor_not_from_reachable_middleOdd

end BB6.Agent31F321FirstMixed
