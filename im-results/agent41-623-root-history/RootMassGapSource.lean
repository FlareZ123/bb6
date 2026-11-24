import Agent49ParitySource

set_option maxRecDepth 100000
set_option maxHeartbeats 0

/-!
# Root-history exclusion of the #623 synchronization witnesses

This file imports the unmodified pinned Cryptids transition through
Agent49ParitySource. It proves strict mass monotonicity between surviving
iterates, anchors the root at indices 23 and 24, and excludes the two-call
source-authentic synchronization witness by the resulting skipped mass
interval.
-/

namespace BB6.Agent41RootHistory

open BB6.Agent49ParitySource

/-- If both iterates survive, total section mass is monotone along the
    authentic blank-origin run. -/
private theorem run_mass_mono_aux (n k : Nat) :
    ∀ a d aa dd,
      run n = some (.D a d) →
      run (n + k) = some (.D aa dd) →
      a + d ≤ aa + dd := by
  induction k with
  | zero =>
      intro a d aa dd hN hM
      have hM' : run n = some (.D aa dd) := by simpa using hM
      have hstate : (.D a d) = (.D aa dd) :=
        Option.some.inj (hN.symm.trans hM')
      cases hstate
      omega
  | succ k ih =>
      intro a d aa dd hN hM
      have hM' : run (n + k + 1) = some (.D aa dd) := by
        simpa [Nat.add_succ] using hM
      have hM'' := hM'
      simp only [run] at hM''
      cases hm : run (n + k) with
      | none =>
          simp only [hm, Option.bind_none] at hM''
      | some s =>
          rcases s with ⟨x, y⟩
          simp only [hm, Option.bind_some] at hM''
          have hprev : a + d ≤ x + y := ih a d x y hN hm
          have hstepMass : x + y + 7 ≤ aa + dd :=
            next_strict_mass x y aa dd hM''
          omega

/-- Monotonicity between arbitrary surviving root indices. -/
theorem run_mass_mono (n m : Nat) (hnm : n ≤ m)
    (a d aa dd : Nat)
    (hN : run n = some (.D a d))
    (hM : run m = some (.D aa dd)) :
    a + d ≤ aa + dd := by
  have hdecomp : m = n + (m - n) := by omega
  rw [hdecomp] at hM
  exact run_mass_mono_aux n (m - n) a d aa dd hN hM

/-- Exact original-source blank-root anchor at index 23. -/
theorem run_23_exact :
    run 23 = some (.D 1228 4156) := by
  decide +kernel

/-- Exact original-source blank-root anchor at index 24. -/
theorem run_24_exact :
    run 24 = some (.D 2924 3705) := by
  decide +kernel

/-- The authentic root skips every total mass strictly between 5384 and
    6629: the two adjacent root masses are 5384 and 6629, and every
    successful source transition strictly increases mass. -/
theorem run_avoids_mass_interval (n a d : Nat)
    (h : run n = some (.D a d)) :
    a + d ≤ 5384 ∨ 6629 ≤ a + d := by
  by_cases hn : n ≤ 23
  · left
    have hm := run_mass_mono n 23 hn a d 1228 4156 h run_23_exact
    omega
  · right
    have hn' : 24 ≤ n := by omega
    have hm := run_mass_mono 24 n hn' 2924 3705 a d run_24_exact h
    omega

/-- Agent 1's two-call source-authentic witness is not a state on the
    blank-origin orbit. Its mass is 5482, inside the skipped interval. -/
theorem two_call_source_not_root (n : Nat) :
    run n ≠ some (.D 4388 1094) := by
  intro h
  have hm := run_avoids_mass_interval n 4388 1094 h
  omega

/-- The target of the two-call witness is also outside the blank-root orbit.
    Its mass is 6594, still below the next root mass 6629. -/
theorem two_call_target_not_root (n : Nat) :
    run n ≠ some (.D 3284 3310) := by
  intro h
  have hm := run_avoids_mass_interval n 3284 3310 h
  omega

#print axioms run_mass_mono
#print axioms run_23_exact
#print axioms run_24_exact
#print axioms run_avoids_mass_interval
#print axioms two_call_source_not_root
#print axioms two_call_target_not_root

end BB6.Agent41RootHistory
