import M32HighSourceBridge
import Lean.Elab.Tactic.Omega

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace CCert

def sideSpine (n t : Nat) : Nat × Nat × Nat :=
  (t+1, 4*n-1-t, 24*n+24+t)

def sideParent (n : Nat) : Nat × Nat × Nat :=
  (0, 2*n-2, 28*n+24)

/-- A predecessor of a side-spine state is the next spine state, except
    at k=2 where the additional parent is sideParent. -/
private theorem side_spine_preimage (n t : Nat) (hn : 2 ≤ n)
    (ht : t ≤ 4*n-3) (s : Nat × Nat × Nat)
    (hstep : BB6CLine.nextC s = some (sideSpine n t)) :
    s = sideSpine n (t+1) ∨ (t=4*n-3 ∧ s=sideParent n) := by
  rcases s with ⟨a,k,c⟩
  rcases c with _|_|_|_|d
  · rcases a with _|_|a
    · simp [BB6CLine.nextC, sideSpine] at hstep
      omega
    · rcases k with _|k
      · simp [BB6CLine.nextC, sideSpine] at hstep
        omega
      · simp [BB6CLine.nextC, sideSpine] at hstep
        omega
    · simp [BB6CLine.nextC, sideSpine] at hstep
      omega
  · simp [BB6CLine.nextC, sideSpine] at hstep
    omega
  · simp [BB6CLine.nextC, sideSpine] at hstep
    omega
  · simp [BB6CLine.nextC, sideSpine] at hstep
    omega
  · rcases a with _|a
    · by_cases he : k%2=0
      · simp [BB6CLine.nextC, sideSpine, he] at hstep
        omega
      · simp [BB6CLine.nextC, sideSpine, he] at hstep
        omega
    · simp [BB6CLine.nextC, sideSpine] at hstep
      omega

private theorem side_spine_last_no_predecessor (n : Nat) (hn : 2 ≤ n) :
    ∀ s, BB6CLine.nextC s ≠ some (sideSpine n (4*n-1)) := by
  intro s h
  rcases s with ⟨a,k,c⟩
  rcases c with _|_|_|_|d
  · simp [BB6CLine.nextC, sideSpine] at h
    omega
  · simp [BB6CLine.nextC, sideSpine] at h
    omega
  · simp [BB6CLine.nextC, sideSpine] at h
    omega
  · simp [BB6CLine.nextC, sideSpine] at h
    omega
  · rcases a with _|a
    · by_cases he : k%2=0
      · simp [BB6CLine.nextC, sideSpine, he] at h
        omega
      · simp [BB6CLine.nextC, sideSpine, he] at h
        omega
    · simp [BB6CLine.nextC, sideSpine] at h
      omega

private theorem side_spine_last_unreachable (n : Nat) (hn : 2 ≤ n) :
    ¬ BB6CLine.Reach (sideSpine n (4*n-1)) := by
  intro h
  cases h with
  | init =>
      simp [sideSpine] at *
  | next s t hs hst =>
      exact side_spine_last_no_predecessor n hn s hst

private theorem side_spine_before_last_preimage (n : Nat) (hn : 2 ≤ n)
    (s : Nat × Nat × Nat)
    (hstep : BB6CLine.nextC s = some (sideSpine n (4*n-2))) :
    s = sideSpine n (4*n-1) := by
  rcases s with ⟨a,k,c⟩
  rcases c with _|_|_|_|d
  · simp [BB6CLine.nextC, sideSpine] at hstep
    omega
  · simp [BB6CLine.nextC, sideSpine] at hstep
    omega
  · simp [BB6CLine.nextC, sideSpine] at hstep
    omega
  · simp [BB6CLine.nextC, sideSpine] at hstep
    omega
  · rcases a with _|a
    · by_cases he : k%2=0
      · simp [BB6CLine.nextC, sideSpine, he] at hstep
        omega
      · simp [BB6CLine.nextC, sideSpine, he] at hstep
        omega
    · simp [BB6CLine.nextC, sideSpine] at hstep
      omega

private theorem side_spine_before_last_unreachable (n : Nat) (hn : 2 ≤ n) :
    ¬ BB6CLine.Reach (sideSpine n (4*n-2)) := by
  intro h
  cases h with
  | init =>
      simp [sideSpine] at *
  | next s t hs hst =>
      have hs' : s = sideSpine n (4*n-1) :=
        side_spine_before_last_preimage n hn s hst
      subst s
      exact side_spine_last_unreachable n hn hs

private theorem side_spine_parent_base (n : Nat) (hn : 2 ≤ n) :
    BB6CLine.Reach (sideSpine n (4*n-3)) → BB6CLine.Reach (sideParent n) := by
  intro h
  cases h with
  | init =>
      simp [sideSpine] at *
  | next s t hs hst =>
      have hp := side_spine_preimage n (4*n-3) hn (by omega) s hst
      rcases hp with hdead | ⟨_, hparent⟩
      · subst s
        exact False.elim (side_spine_before_last_unreachable n hn hs)
      · subst s
        exact hs

private theorem side_spine_step (n t : Nat) (hn : 2 ≤ n)
    (ht : t < 4*n-3) :
    BB6CLine.Reach (sideSpine n t) →
    BB6CLine.Reach (sideSpine n (t+1)) := by
  intro h
  cases h with
  | init =>
      simp [sideSpine] at *
  | next s u hs hstep =>
      have hp := side_spine_preimage n t hn (by omega) s hstep
      rcases hp with hsource | ⟨hbad, _⟩
      · rw [hsource]
        exact hs
      · omega

/-- Any reachable side gate with n>=2 must have reached its unique
    non-dead predecessor parent (0,2*n-2,28*n+24). -/
theorem side_reach_parent (n : Nat) (hn : 2 ≤ n) :
    BB6CLine.Reach (0,4*n,24*n+23) →
    BB6CLine.Reach (sideParent n) := by
  intro h
  have hU0 : BB6CLine.Reach (sideSpine n 0) := by
    cases h with
    | init =>
        simp [sideSpine] at *
    | next s t hs hstep =>
        rcases s with ⟨a,k,c⟩
        have hsEq : (a,k,c) = sideSpine n 0 := by
          simp [BB6CLine.nextC, sideSpine] at hstep
          omega
        rw [hsEq] at hs
        exact hs
  have chain : ∀ d t, d = 4*n-3-t →
      t ≤ 4*n-3 →
      BB6CLine.Reach (sideSpine n t) →
      BB6CLine.Reach (sideParent n) := by
    intro d
    induction d using Nat.strong_induction_on with
    | h d ih =>
        intro t hdt ht hreach
        by_cases heq : t = 4*n-3
        · subst t
          exact side_spine_parent_base n hn hreach
        · have htlt : t < 4*n-3 := by omega
          have hnext : BB6CLine.Reach (sideSpine n (t+1)) :=
            side_spine_step n t hn htlt hreach
          have hdec : 4*n-3-(t+1) < d := by omega
          exact ih (4*n-3-(t+1)) hdec (t+1) rfl (by omega) hnext
  exact chain (4*n-3) 0 (by omega) (by omega) hU0

/-- The M32 source certificate excludes the parent when n is a positive
    multiple of 16. -/
theorem side_parent_mod16_unreachable (n : Nat) (hn : 16 ≤ n)
    (hmod : n%16=0) :
    ¬ BB6CLine.Reach (sideParent n) := by
  intro h
  have hs := reachable_seen (source_reachable_embeds32 h)
  have hk : q (2*n-2) = q 30 :=
    q_congr_big _ _ (by omega) (by decide) (by omega)
  have hc : q (28*n+24) = q 472 :=
    q_congr_big _ _ (by omega) (by decide) (by omega)
  rw [hk,hc] at hs
  have hf : seen (q 0) (q 30) (q 472) = false := by decide
  rw [hf] at hs
  cases hs

/-- New all-time exclusion for the original CLine side family:
    no side gate with n=0 (mod 16) is source-reachable. -/
theorem side_gate_mod16_unreachable (n : Nat) (hn : 16 ≤ n)
    (hmod : n%16=0) :
    ¬ BB6CLine.Reach (0,4*n,24*n+23) := by
  intro h
  have hp := side_reach_parent n (by omega) h
  exact side_parent_mod16_unreachable n hn hmod hp

#print axioms side_reach_parent
#print axioms side_parent_mod16_unreachable
#print axioms side_gate_mod16_unreachable

end CCert
