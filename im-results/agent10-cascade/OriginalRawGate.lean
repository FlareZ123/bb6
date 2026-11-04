import OriginalMinIndexBridge

namespace Agent10Raw746
open BusyBeaver
open BusyBeaver.M_1RB0LF_1LC1RA_0RE0RD_HHH1LE_1LF1RC_1LC1LA
open Agent10Original746
open CascadeSweep

/-- In any partial transition system, eventual termination has a last
    defined state whose next transition is undefined. -/
private theorem halt_has_terminal {S : Type*} (next : S → Option S) (s : S)
    (h : CollatzHalts next s) :
    ∃ t, CollatzReachesStar next s t ∧ next t = none := by
  obtain ⟨n, hn⟩ := h
  induction n generalizing s with
  | zero =>
      simp at hn
  | succ n ih =>
      rw [Function.iterate_succ_apply] at hn
      cases he : next s with
      | none =>
          exact ⟨s, CollatzReachesStar.refl next s, he⟩
      | some y =>
          have htail : ((Option.bind · next)^[n] (some y)).isNone := by
            simpa [he] using hn
          obtain ⟨t, ht, hnone⟩ := ih y htail
          exact ⟨t, CollatzReachesStar.head he ht, hnone⟩

/-- The original high-level accelerated run agrees exactly with the
    abstract iterate used in the upstream raw-machine reduction. -/
private theorem iterate_eq_startRun (k : Nat) :
    ((Option.bind · highLevelNext)^[k] (some highLevelStart)) =
      startRun k := by
  induction k with
  | zero => rfl
  | succ k ih =>
      rw [show k+1 = 1+k by omega, Function.iterate_add_apply]
      rw [ih]
      rfl

/-- If the physical blank-tape six-state machine halts, an authentic
    accelerated blank-origin fatal reset c_n was reached with n>=101.
    This is a necessary condition, not an assertion of nonhalting. -/
theorem raw_halt_requires_index_ge_101 (h : IsHalt target) :
    ∃ n, 101 ≤ n ∧ (n%6=4 ∨ n%6=5) ∧
      ReachC (2,0) (4*2^n-n-4,0) := by
  have hh : CollatzHalts highLevelNext highLevelStart :=
    isHalt_iff_highLevel_acceleration.mp h
  obtain ⟨s, ⟨k, hk⟩, hs⟩ :=
    halt_has_terminal highLevelNext highLevelStart hh
  rcases s with ⟨a,b⟩
  have hb : b=1 := by
    rcases b with _|_|d
    · simp [highLevelNext] at hs
    · rfl
    · simp only [highLevelNext] at hs
      split_ifs at hs <;> cases hs
  have hrun : startRun k = some (.C a 1) := by
    rw [←iterate_eq_startRun]
    rw [←hb]
    exact hk
  exact upstream_halt_requires_index_ge_101 k a hrun

#print axioms raw_halt_requires_index_ge_101
end Agent10Raw746
