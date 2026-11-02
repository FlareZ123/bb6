import RootTransfer

namespace BB6.Agent19.Physical
open BB6.Portfolio

/-- In partial physical semantics, a halt at exact time t means that its
    t-step state is live while the (t+1)-step state is undefined. -/
theorem exact_halt_iff_first_none (M : Machine) (c : Cfg) (t : Nat) :
    HaltsAtCfg M c t ↔
      run M t (some c) ≠ none ∧ run M (t+1) (some c) = none := by
  constructor
  · rintro ⟨last,hr,hs⟩
    constructor
    · simp [hr]
    · change (run M t (some c)).bind (step M)=none
      simp [hr,hs]
  · rintro ⟨ht,hs⟩
    cases heq : run M t (some c) with
    | none => exact False.elim (ht heq)
    | some last =>
      have hn : step M last=none := by
        change (run M t (some c)).bind (step M)=none at hs
        simpa [heq] using hs
      exact ⟨last,heq,hn⟩

/-- The exact first halting time of ANY physical unary F-section equals
    the original finite-source first transition into frozen state 6. -/
theorem unary_exact_halt_iff_source_first_frozen (n t : Nat) :
    HaltsAtCfg D0 (F0Pure n 0) t ↔
      (CryptidBoundary.run t (sourceUnary n)).st ≠ 6 ∧
        (CryptidBoundary.run (t+1) (sourceUnary n)).st = 6 := by
  rw [exact_halt_iff_first_none]
  exact and_congr (not_congr (unary_run_none_iff_source_frozen n t))
    (unary_run_none_iff_source_frozen n (t+1))

/-- The four genuinely rooted RLE machine strings have exact original
    source halting times after their audited 36/403/92/15 step prefixes. -/
theorem parsed_D0_exact_source_time (t : Nat) :
    haltsAt (parseRLE rleD0) (0:State) (36+t) ↔
      (CryptidBoundary.run t (sourceUnary 9)).st ≠ 6 ∧
      (CryptidBoundary.run (t+1) (sourceUnary 9)).st = 6 := by
  rw [parsed_D0_eq]
  have h : haltsAt D0 (0:State) (36+t) ↔
      HaltsAtCfg D0 (F0Pure 9 0) t := by
    simpa [startTime,startSeed] using
      (all_blank_haltsAt_iff_unary (0 : State) t)
  exact h.trans (unary_exact_halt_iff_source_first_frozen 9 t)

theorem parsed_D1_exact_source_time (t : Nat) :
    haltsAt (parseRLE rleD1) (0:State) (403+t) ↔
      (CryptidBoundary.run t (sourceUnary 39)).st ≠ 6 ∧
      (CryptidBoundary.run (t+1) (sourceUnary 39)).st = 6 := by
  have h := parsed_D1_haltsAt_iff_I39 t
  rw [parsed_D0_eq] at h
  exact h.trans (unary_exact_halt_iff_source_first_frozen 39 t)

theorem parsed_D2_exact_source_time (t : Nat) :
    haltsAt (parseRLE rleD2) (0:State) (92+t) ↔
      (CryptidBoundary.run t (sourceUnary 15)).st ≠ 6 ∧
      (CryptidBoundary.run (t+1) (sourceUnary 15)).st = 6 := by
  have h := parsed_D2_haltsAt_iff_I15 t
  rw [parsed_D0_eq] at h
  exact h.trans (unary_exact_halt_iff_source_first_frozen 15 t)

theorem parsed_D3_exact_source_time (t : Nat) :
    haltsAt (parseRLE rleD3) (0:State) (15+t) ↔
      (CryptidBoundary.run t (sourceUnary 5)).st ≠ 6 ∧
      (CryptidBoundary.run (t+1) (sourceUnary 5)).st = 6 := by
  have h := parsed_D3_haltsAt_iff_I5 t
  rw [parsed_D0_eq] at h
  exact h.trans (unary_exact_halt_iff_source_first_frozen 5 t)

#print axioms exact_halt_iff_first_none
#print axioms unary_exact_halt_iff_source_first_frozen
#print axioms parsed_D0_exact_source_time
#print axioms parsed_D1_exact_source_time
#print axioms parsed_D2_exact_source_time
#print axioms parsed_D3_exact_source_time
end BB6.Agent19.Physical
