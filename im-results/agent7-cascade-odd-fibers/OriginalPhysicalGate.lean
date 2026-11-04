import OriginalSurvivingBridge

namespace Agent7Physical746

open BusyBeaver
open BusyBeaver.M_1RB0LF_1LC1RA_0RE0RD_HHH1LE_1LF1RC_1LC1LA
open CascadeSource CascadeSweep

/-- The existing source-indexed run is exactly the iterated original
highLevelNext used by the pinned Cryptids IsHalt theorem. -/
theorem original_startRun_eq_iter (k : Nat) :
    Agent10Original746.startRun k =
      ((Option.bind · highLevelNext)^[k]) (some highLevelStart) := by
  induction k with
  | zero => rfl
  | succ k ih =>
      change (Agent10Original746.startRun k).bind highLevelNext =
        ((Option.bind · highLevelNext)^[k+1]) (some highLevelStart)
      rw [Function.iterate_succ_apply']
      rw [ih]

/-- A genuinely undefined original high-level iterate must have an
immediately preceding original high-level C-state with b=1. -/
private theorem before_none (n : Nat)
    (h : Agent10Original746.startRun (n+1) = none) :
    ∃ k a, Agent10Original746.startRun k = some (.C a 1) := by
  induction n with
  | zero =>
      simp [Agent10Original746.startRun, highLevelStart, highLevelNext] at h
  | succ n ih =>
      cases hs : Agent10Original746.startRun (n+1) with
      | none => exact ih hs
      | some s =>
          rcases s with ⟨a,b⟩
          change (Agent10Original746.startRun (n+1)).bind highLevelNext = none at h
          rw [hs] at h
          have hb : b=1 := by
            rcases b with _ | _ | d
            · simp [highLevelNext] at h
            · rfl
            · simp only [highLevelNext] at h
              split_ifs at h <;> cases h
          exact ⟨n+1,a,by simpa only [hb] using hs⟩

/-- The exact original Cryptids halting predicate means that its genuine
high-level trajectory visits the unique undefined C-state layer b=1. -/
theorem original_collatz_halts_iff_visits_1 :
    CollatzHalts highLevelNext highLevelStart ↔
      ∃ k a, Agent10Original746.startRun k = some (.C a 1) := by
  constructor
  · rintro ⟨n,hn⟩
    have hnone : ((Option.bind · highLevelNext)^[n]) (some highLevelStart) = none :=
      Option.isNone_iff_eq_none.mp hn
    rw [←original_startRun_eq_iter] at hnone
    cases n with
    | zero =>
        simp [Agent10Original746.startRun] at hnone
    | succ n => exact before_none n hnone
  · rintro ⟨k,a,hk⟩
    have hnone : Agent10Original746.startRun (k+1)=none := by
      simp [Agent10Original746.startRun,hk,highLevelNext]
    refine ⟨k+1,?_⟩
    rw [←original_startRun_eq_iter]
    exact Option.isNone_iff_eq_none.mpr hnone

/-- Every exact copied-source C-reachable state is visited by a genuine
iterated highLevelNext of the unmodified Cryptids accelerator. -/
theorem exact_root_reach_has_original_run {x : Nat × Nat}
    (h : ReachC (2,0) x) :
    ∃ k, Agent10Original746.run k = some (.C x.1 x.2) := by
  induction h with
  | refl => exact ⟨0,rfl⟩
  | @push y z hprev he ih =>
      rcases y with ⟨a,b⟩
      rcases z with ⟨c,d⟩
      obtain ⟨k,hk⟩ := ih
      have hnext : highLevelNext (.C a b)=some (.C c d) := by
        cases hs : highLevelNext (.C a b) with
        | none =>
            have hh := Agent10Original746.exact_high_level_step a b
            rw [hs, he] at hh
            simp at hh
        | some s =>
            rcases s with ⟨u,v⟩
            have hh := Agent10Original746.exact_high_level_step a b
            rw [hs, he] at hh
            change some (u,v) = some (c,d) at hh
            have huv : u=c ∧ v=d := by simpa using hh
            rcases huv with ⟨rfl,rfl⟩
            rfl
      exact ⟨k+1,by simpa [Agent10Original746.run,hk,hnext]⟩

/-- Genuine *raw six-state Turing-machine* halting is equivalent to
actual accelerated blank-root reachability of a fatal reset in the two
surviving mod-six classes, with exponent at least 52. Original Cryptids
supplies the proved raw TM-to-highLevelNext equivalence. -/
theorem original_machine_halts_iff_surviving_52 :
    IsHalt target ↔
      ∃ n, 52≤n ∧ (n%6=4 ∨ n%6=5) ∧
        ReachC (2,0) (4*2^n-n-4,0) := by
  rw [isHalt_iff_highLevel_acceleration, original_collatz_halts_iff_visits_1]
  constructor
  · rintro ⟨k,a,hk⟩
    cases k with
    | zero =>
        simp [Agent10Original746.startRun,highLevelStart] at hk
    | succ k =>
        rw [Agent10Original746.startRun_successor] at hk
        have hr := Agent10Original746.run_reaches k a 1 hk
        exact CascadeSurvivingGate.halt_iff_surviving_index_ge_52.mp ⟨a,hr⟩
  · rintro ⟨n,hn,hmod,hr⟩
    obtain ⟨a,ha⟩ :=
      CascadeSurvivingGate.halt_iff_surviving_index_ge_52.mpr ⟨n,hn,hmod,hr⟩
    obtain ⟨k,hk⟩ := exact_root_reach_has_original_run ha
    exact ⟨k+1,a,by rw [Agent10Original746.startRun_successor]; exact hk⟩

#print axioms original_collatz_halts_iff_visits_1
#print axioms exact_root_reach_has_original_run
#print axioms original_machine_halts_iff_surviving_52

end Agent7Physical746
