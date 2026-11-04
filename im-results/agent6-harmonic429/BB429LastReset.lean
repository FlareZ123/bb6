import BB429Rank
import Lean.Elab.Tactic.Omega

namespace BB429LastReset

/-- A reachable configuration is either in the initial uninterrupted first
    branch, or has a last non-first successful step followed by first steps. -/
def Tail (s : BB429.State) : Prop :=
  (∃ k, BB429.firstRun k (0,0) = some s) ∨
  (∃ j, ∃ p : BB429.State, ∃ seed : BB429.State, ∃ k,
    BB429.run j (0,0) = some p ∧
    p.2 < 2*p.1+3 ∧
    BB429.next p = some seed ∧
    BB429.firstRun k seed = some s)

theorem all_reachable_have_last_reset (n : Nat) (s : BB429.State)
    (hs : BB429.run n (0,0) = some s) : Tail s := by
  induction n generalizing s with
  | zero =>
    left
    refine ⟨0, ?_⟩
    simpa [BB429.run,BB429.firstRun] using hs
  | succ n ih =>
    simp only [BB429.run] at hs
    cases hp : BB429.run n (0,0) with
    | none => simp [hp] at hs
    | some p =>
      simp only [hp, Option.bind_some] at hs
      obtain ⟨u,w⟩ := p
      have ht := ih (u,w) hp
      by_cases hg : 2*u+3 ≤ w
      · have hf : BB429.firstStep (u,w) = some s := by
          rw [BB429.firstStep_is_next u w hg]
          exact hs
        rcases ht with ⟨k,hk⟩ | ⟨j,p,seed,k,hj,hnot,hnon,hk⟩
        · left
          refine ⟨k+1, ?_⟩
          simp only [BB429.firstRun,hk,Option.bind_some]
          exact hf
        · right
          refine ⟨j,p,seed,k+1,hj,hnot,hnon,?_⟩
          simp only [BB429.firstRun,hk,Option.bind_some]
          exact hf
      · right
        have hnot : w < 2*u+3 := by omega
        refine ⟨n,(u,w),s,0,hp,hnot,hs,?_⟩
        rfl

/-- The blank initial configuration cannot execute even one first step. -/
theorem initial_first_step_none : BB429.firstStep (0,0) = none := by
  decide

theorem blank_first_run_only_zero (n : Nat) (s : BB429.State)
    (h : BB429.firstRun n (0,0) = some s) : n=0 := by
  cases n with
  | zero => rfl
  | succ n =>
    have hnone : ∀ k : Nat, BB429.firstRun (k+1) (0,0)=none := by
      intro k
      induction k with
      | zero =>
        change BB429.firstStep (0,0)=none
        exact initial_first_step_none
      | succ k ih =>
        change (BB429.firstRun (k+1) (0,0)).bind BB429.firstStep=none
        rw [ih]
        rfl
    simp [hnone n] at h

/-- Every genuine macro halt must occur after a last non-first transition.
    Its entire subsequent suffix contains only first-branch transitions. -/
theorem halting_has_last_nonfirst (n : Nat) (s : BB429.State)
    (hreach : BB429.run n (0,0)=some s)
    (hhalt : BB429.next s=none) :
    ∃ j, ∃ p : BB429.State, ∃ seed : BB429.State, ∃ k,
      BB429.run j (0,0) = some p ∧
      p.2 < 2*p.1+3 ∧
      BB429.next p = some seed ∧
      BB429.firstRun k seed = some s := by
  have ht := all_reachable_have_last_reset n s hreach
  rcases ht with ⟨k,hk⟩ | hrest
  · have hk0 := blank_first_run_only_zero k s hk
    subst k
    simp only [BB429.firstRun, Option.some.injEq] at hk
    subst s
    simp [BB429.next] at hhalt
  · exact hrest

#print axioms all_reachable_have_last_reset
#print axioms blank_first_run_only_zero
#print axioms halting_has_last_nonfirst
end BB429LastReset
