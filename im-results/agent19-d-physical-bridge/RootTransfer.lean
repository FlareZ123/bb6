import UnaryBridge
import DSourceCorollaries

namespace BB6.Agent19.Physical
open BB6.Portfolio

/-- All six raw blank-root starts on D0 reduce to their authenticated
    original-source finite unary seed and source halt flag. -/
theorem all_six_blank_starts_source_iff (s : State) :
    haltsFrom D0 s ↔
      ∃ t, (CryptidBoundary.run t (sourceUnary (startSeed s))).st = 6 := by
  exact (every_blank_halts_iff_unary s).trans
    (unary_halts_iff_source_frozen (startSeed s))

/-- Each of the four distinct rooted October holdout strings is now linked
    to the authenticated Cryptid source with its own precise initial seed. -/
theorem parsed_D0_root_source_iff :
    haltsFrom (parseRLE rleD0) (0 : State) ↔
      ∃ t, (CryptidBoundary.run t (sourceUnary 9)).st = 6 := by
  rw [parsed_D0_eq]
  simpa [startSeed] using all_six_blank_starts_source_iff (0 : State)

theorem parsed_D1_root_source_iff :
    haltsFrom (parseRLE rleD1) (0 : State) ↔
      ∃ t, (CryptidBoundary.run t (sourceUnary 39)).st = 6 := by
  have h := parsed_D1_halts_iff_I39
  rw [parsed_D0_eq] at h
  exact h.trans (unary_halts_iff_source_frozen 39)

theorem parsed_D2_root_source_iff :
    haltsFrom (parseRLE rleD2) (0 : State) ↔
      ∃ t, (CryptidBoundary.run t (sourceUnary 15)).st = 6 := by
  have h := parsed_D2_halts_iff_I15
  rw [parsed_D0_eq] at h
  exact h.trans (unary_halts_iff_source_frozen 15)

theorem parsed_D3_root_source_iff :
    haltsFrom (parseRLE rleD3) (0 : State) ↔
      ∃ t, (CryptidBoundary.run t (sourceUnary 5)).st = 6 := by
  have h := parsed_D3_halts_iff_I5
  rw [parsed_D0_eq] at h
  exact h.trans (unary_halts_iff_source_frozen 5)

#print axioms all_six_blank_starts_source_iff
#print axioms parsed_D0_root_source_iff
#print axioms parsed_D1_root_source_iff
#print axioms parsed_D2_root_source_iff
#print axioms parsed_D3_root_source_iff
end BB6.Agent19.Physical
