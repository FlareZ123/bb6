import OriginalNextBridge
import RootMinIndex

namespace Agent10Original746
open BusyBeaver.M_1RB0LF_1LC1RA_0RE0RD_HHH1LE_1LF1RC_1LC1LA
open CascadeRootMinIndex

/-- In the unmodified Cryptids high-level machine accelerated from the
    actual initial state, no fatal reset with index at most 100 occurs. -/
theorem upstream_no_fatal_through_100 (n k : Nat) (hn : n ≤ 100) :
    startRun k ≠ some (.C (4*2^n-n-4) 0) := by
  cases k with
  | zero =>
      simp [startRun, highLevelStart]
  | succ k =>
      rw [startRun_successor]
      intro h
      exact no_fatal_through_100 n hn (run_reaches k _ _ h)

/-- Any genuine accelerated high-level run reaching the halting C-state
    has a source-episode fatal witness of index at least 101. -/
theorem upstream_halt_requires_index_ge_101 (k a : Nat)
    (h : startRun k = some (.C a 1)) :
    ∃ n, 101 ≤ n ∧ (n%6=4 ∨ n%6=5) ∧
      CascadeSweep.ReachC (2,0) (4*2^n-n-4,0) := by
  cases k with
  | zero =>
      simp [startRun, highLevelStart] at h
  | succ k =>
      rw [startRun_successor] at h
      exact halt_requires_index_ge_101 a (run_reaches k _ _ h)

#print axioms upstream_no_fatal_through_100
#print axioms upstream_halt_requires_index_ge_101
end Agent10Original746
