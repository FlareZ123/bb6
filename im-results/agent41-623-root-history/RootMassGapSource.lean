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
      have hstate :
          BusyBeaver.M_1RB0LE_0RC1RC_0RD1LA_1LD0LA_1LF1LC_HHH0LA.HighLevelState.D a d =
          BusyBeaver.M_1RB0LE_0RC1RC_0RD1LA_1LD0LA_1LF1LC_HHH0LA.HighLevelState.D aa dd :=
        Option.some.inj (hN.symm.trans hM')
      cases hstate
      omega
  | succ k ih =>
      intro a d aa dd hN hM
      have hM' : run (n + k + 1) = some (.D aa dd) := by
        simpa [Nat.add_succ] using hM
      rw [run] at hM'
      cases hm : run (n + k) with
      | none =>
          have hfalse : False := by
            simpa only [hm, Option.bind_none] using hM'
          exact hfalse.elim
      | some s =>
          rcases s with ⟨x, y⟩
          have hprev : a + d ≤ x + y := ih a d x y hN hm
          have hstepMass : x + y + 7 ≤ aa + dd := by
            apply next_strict_mass x y aa dd
            simpa only [hm, Option.bind_some] using hM'
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

/-- Exact original-source blank-root anchor at index 77. -/
theorem run_77_exact :
    run 77 = some (.D 143714866 386322776) := by
  decide +kernel

/-- Exact original-source blank-root anchor at index 78. -/
theorem run_78_exact :
    run 78 = some (.D 242607912 431144625) := by
  decide +kernel

/-- Exact original-source blank-root anchor at index 79. -/
theorem run_79_exact :
    run 79 = some (.D 188536700 727823788) := by
  decide +kernel

/-- Exact original-source blank-root anchor at index 80. -/
theorem run_80_exact :
    run 80 = some (.D 539287086 565610137) := by
  decide +kernel

/-- Exact original-source blank-root anchor at index 81. -/
theorem run_81_exact :
    run 81 = some (.D 26323038 1617861312) := by
  decide +kernel

/-- A second skipped root-mass interval, between indices 77 and 78. -/
theorem run_avoids_mass_interval_77_78 (n a d : Nat)
    (h : run n = some (.D a d)) :
    a + d ≤ 530037642 ∨ 673752537 ≤ a + d := by
  by_cases hn : n ≤ 77
  · left
    have hm := run_mass_mono n 77 hn a d 143714866 386322776 h run_77_exact
    omega
  · right
    have hn' : 78 ≤ n := by omega
    have hm := run_mass_mono 78 n hn' 242607912 431144625 run_78_exact h
    omega

/-- A third skipped root-mass interval, between indices 78 and 79. -/
theorem run_avoids_mass_interval_78_79 (n a d : Nat)
    (h : run n = some (.D a d)) :
    a + d ≤ 673752537 ∨ 916360488 ≤ a + d := by
  by_cases hn : n ≤ 78
  · left
    have hm := run_mass_mono n 78 hn a d 242607912 431144625 h run_78_exact
    omega
  · right
    have hn' : 79 ≤ n := by omega
    have hm := run_mass_mono 79 n hn' 188536700 727823788 run_79_exact h
    omega

/-- A fourth skipped root-mass interval, between indices 80 and 81. -/
theorem run_avoids_mass_interval_80_81 (n a d : Nat)
    (h : run n = some (.D a d)) :
    a + d ≤ 1104897223 ∨ 1644184350 ≤ a + d := by
  by_cases hn : n ≤ 80
  · left
    have hm := run_mass_mono n 80 hn a d 539287086 565610137 h run_80_exact
    omega
  · right
    have hn' : 81 ≤ n := by omega
    have hm := run_mass_mono 81 n hn' 26323038 1617861312 run_81_exact h
    omega

/-- The first ell=20 member of Agent 1's cone-only family is not root-reachable. -/
theorem cone_only_ell20_r1_not_root (n : Nat) :
    run n ≠ some (.D 602667616 150666804) := by
  intro h
  have hm := run_avoids_mass_interval_78_79 n 602667616 150666804 h
  omega

/-- The second ell=20 member of Agent 1's cone-only family is not root-reachable. -/
theorem cone_only_ell20_r2_not_root (n : Nat) :
    run n ≠ some (.D 947041384 236760246) := by
  intro h
  have hm := run_avoids_mass_interval_80_81 n 947041384 236760246 h
  omega

/-- The third ell=20 member of Agent 1's cone-only family is not root-reachable. -/
theorem cone_only_ell20_r3_not_root (n : Nat) :
    run n ≠ some (.D 1291415152 322853688) := by
  intro h
  have hm := run_avoids_mass_interval_80_81 n 1291415152 322853688 h
  omega

/-- The source of the v3 state-locality counterexample is not root-reachable:
    its mass lies strictly between the exact root masses at indices 77 and 78. -/
theorem v3_counterexample_source_not_root (n : Nat) :
    run n ≠ some (.D 464905666 116226414) := by
  intro h
  have hm := run_avoids_mass_interval_77_78 n 464905666 116226414 h
  omega

/-- The target of the v3 state-locality counterexample is not root-reachable:
    its mass lies strictly between the exact root masses at indices 78 and 79. -/
theorem v3_counterexample_target_not_root (n : Nat) :
    run n ≠ some (.D 348679242 348679292) := by
  intro h
  have hm := run_avoids_mass_interval_78_79 n 348679242 348679292 h
  omega

#print axioms run_mass_mono
#print axioms run_23_exact
#print axioms run_24_exact
#print axioms run_avoids_mass_interval
#print axioms two_call_source_not_root
#print axioms two_call_target_not_root
#print axioms run_77_exact
#print axioms run_78_exact
#print axioms run_79_exact
#print axioms run_avoids_mass_interval_77_78
#print axioms run_avoids_mass_interval_78_79
#print axioms v3_counterexample_source_not_root
#print axioms v3_counterexample_target_not_root
#print axioms run_80_exact
#print axioms run_81_exact
#print axioms run_avoids_mass_interval_80_81
#print axioms cone_only_ell20_r1_not_root
#print axioms cone_only_ell20_r2_not_root
#print axioms cone_only_ell20_r3_not_root

end BB6.Agent41RootHistory
