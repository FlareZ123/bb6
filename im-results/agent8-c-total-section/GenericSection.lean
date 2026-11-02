import Std
import Lean.Elab.Tactic.Omega

namespace BB6.Agent8Section

variable {α β : Type}

def run {α : Type} (f : α → Option α) : Nat → Option α → Option α
  | 0, s => s
  | n+1, s => (run f n s).bind f

theorem run_add (f : α → Option α) (n m : Nat) (s : Option α) :
    run f (n+m) s = run f m (run f n s) := by
  induction m with
  | zero => simp [run]
  | succ m ih =>
      rw [Nat.add_succ]
      change (run f (n+m) s).bind f = (run f m (run f n s)).bind f
      rw [ih]

theorem run_none (f : α → Option α) (n : Nat) :
    run f n none = none := by
  induction n with
  | zero => rfl
  | succ n ih => simp [run,ih]

theorem run_step_commute (f : α → Option α) (n : Nat) (s : Option α) :
    run f n (s.bind f) = (run f n s).bind f := by
  induction n with
  | zero => rfl
  | succ n ih =>
      change (run f n (s.bind f)).bind f = ((run f n s).bind f).bind f
      rw [ih]

theorem run_succ_head (f : α → Option α) (n : Nat) (s : Option α) :
    run f (n+1) s = run f n (s.bind f) := by
  change (run f n s).bind f = run f n (s.bind f)
  exact (run_step_commute f n s).symm

variable (f : α → Option α) (embed : β → α)
variable (exits : ∀ x : β, ∃ n : Nat, 1 ≤ n ∧
  ∃ y : Option β, run f n (some (embed x)) = y.map embed)

noncomputable def exitTime (x : β) : Nat := Classical.choose (exits x)
noncomputable def sectionStep (x : β) : Option β :=
  Classical.choose ((Classical.choose_spec (exits x)).2)

theorem exitTime_positive (x : β) : 1 ≤ exitTime f embed exits x :=
  (Classical.choose_spec (exits x)).1

theorem sectionStep_exact (x : β) :
    run f (exitTime f embed exits x) (some (embed x)) =
       (sectionStep f embed exits x).map embed :=
  Classical.choose_spec ((Classical.choose_spec (exits x)).2)

/-- Any deterministic section map whose each edge covers a positive number
    of real transitions is an exact halting reduction. -/
theorem section_halts_iff_of_step
    (time : β → Nat) (g : β → Option β)
    (step_pos : ∀ s : β, 1 ≤ time s)
    (step_spec : ∀ s : β, run f (time s) (some (embed s)) = (g s).map embed)
    (x : β) :
    (∃ n, run f n (some (embed x)) = none) ↔
      (∃ m, run g m (some x) = none) := by
  constructor
  · rintro ⟨n, hn⟩
    have all : ∀ k : Nat, ∀ s : β,
        run f k (some (embed s)) = none → ∃ m, run g m (some s) = none := by
      intro k
      induction k using Nat.strongRecOn with
      | ind k ih =>
          intro s hs
          cases hg : g s with
          | none =>
              refine ⟨1, ?_⟩
              simp [run,hg]
          | some t =>
              have he : run f (time s) (some (embed s)) =
                  some (embed t) := by simpa [hg] using step_spec s
              have hlt : time s < k := by
                by_cases hc : time s < k
                · exact hc
                have hle : k ≤ time s := Nat.le_of_not_gt hc
                have hsum : k+(time s-k) = time s := by omega
                have hnone : run f (time s) (some (embed s)) = none := by
                  rw [←hsum,run_add,hs,run_none]
                rw [he] at hnone
                contradiction
              have hleft : time s + (k-time s) = k := by omega
              have htail : run f (k-time s) (some (embed t)) = none := by
                rw [← hleft,run_add,he] at hs
                exact hs
              obtain ⟨m,hm⟩ := ih (k-time s) (by have hp := step_pos s; omega) t htail
              refine ⟨m+1, ?_⟩
              rw [run_succ_head]
              simpa [hg] using hm
    exact all n x hn
  · rintro ⟨m, hm⟩
    have all : ∀ k : Nat, ∀ s : β,
        run g k (some s) = none → ∃ n, run f n (some (embed s)) = none := by
      intro k
      induction k with
      | zero =>
          intro s hs
          simp [run] at hs
      | succ k ih =>
          intro s hs
          rw [run_succ_head] at hs
          cases hg : g s with
          | none =>
              refine ⟨time s, ?_⟩
              simpa [hg] using step_spec s
          | some t =>
              have htail : run g k (some t) = none := by simpa [hg] using hs
              obtain ⟨n,hn⟩ := ih t htail
              refine ⟨time s+n, ?_⟩
              rw [run_add,step_spec]
              simpa [hg] using hn
    exact all m x hm

/-- A uniformly defined section exists whenever each section input has
    some positive-length exit to another section point or a stop. -/
theorem section_halts_iff (x : β) :
    (∃ n, run f n (some (embed x)) = none) ↔
      (∃ m, run (sectionStep f embed exits) m (some x) = none) :=
  section_halts_iff_of_step f embed (exitTime f embed exits)
    (sectionStep f embed exits)
    (exitTime_positive f embed exits)
    (sectionStep_exact f embed exits) x

#print axioms section_halts_iff_of_step
#print axioms section_halts_iff
end BB6.Agent8Section
