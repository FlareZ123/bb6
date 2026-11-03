import Lean
import Lean.Elab.Tactic.Omega

namespace ForwardMass

universe u
variable {α : Type u}

/-- The finite trajectory, with `none` forever after the first failure. -/
def run (step : α → Option α) (start : α) : Nat → Option α
  | 0 => some start
  | n+1 => (run step start n).bind step

theorem run_add (step : α → Option α) (s : α) (n m : Nat) :
    run step s (n+m) = (run step s n).bind (fun p => run step p m) := by
  induction m with
  | zero =>
      simp [run]
  | succ m ih =>
      rw [Nat.add_succ, run, ih]
      cases h : run step s n with
      | none => simp [h, run]
      | some p => simp [h, run]

theorem run_none_later (step : α → Option α) (s : α) (n m : Nat)
    (h : run step s n = none) : run step s (n+m) = none := by
  rw [run_add, h]
  rfl

theorem run_mass_mono (step : α → Option α) (mass : α → Nat)
    (hmono : ∀ p q, step p = some q → mass p ≤ mass q)
    (s : α) (n : Nat) (q : α) (hq : run step s n = some q) :
    mass s ≤ mass q := by
  induction n generalizing q with
  | zero =>
      simp [run] at hq
      subst q
      exact Nat.le_refl _
  | succ n ih =>
      have hh : (run step s n).bind step = some q := hq
      cases hr : run step s n with
      | none => simp [hr] at hh
      | some p =>
          have hp : step p = some q := by simpa [hr] using hh
          exact Nat.le_trans (ih p hr) (hmono p q hp)

theorem run_stops_after_terminal (step : α → Option α) (s goal : α)
    (hterm : step goal = none) (n k : Nat)
    (hhit : run step s n = some goal) : run step s (n+1+k) = none := by
  have hz : run step s (n+1) = none := by
    simp [run, hhit, hterm]
  exact run_none_later step s (n+1) k hz

/-- Verified alive trajectory overshooting a terminal target's monotone mass
    excludes that target at every time, including earlier times. -/
theorem terminal_overshoot (step : α → Option α) (mass : α → Nat)
    (hmono : ∀ p q, step p = some q → mass p ≤ mass q)
    (start goal live : α) (N : Nat)
    (hterm : step goal = none)
    (htrace : run step start N = some live)
    (hovershoot : mass goal < mass live) :
    ∀ n, run step start n ≠ some goal := by
  intro n hhit
  rcases Nat.le_total n N with hle | hle
  · rcases Nat.eq_or_lt_of_le hle with heq | hlt
    · subst N
      have : live = goal := Option.some.inj (htrace.symm.trans hhit)
      subst live
      omega
    · obtain ⟨k, hk⟩ : ∃ k, n+1+k = N := by
        refine ⟨N-(n+1), ?_⟩
        omega
      have hz := run_stops_after_terminal step start goal hterm n k hhit
      rw [hk] at hz
      rw [htrace] at hz
      contradiction
  · obtain ⟨k, hk⟩ : ∃ k, N+k = n := by
      refine ⟨n-N, ?_⟩
      omega
    rw [← hk, run_add, htrace] at hhit
    have hs : run step live k = some goal := by simpa using hhit
    have := run_mass_mono step mass hmono live k goal hs
    omega

#print axioms terminal_overshoot

end ForwardMass
