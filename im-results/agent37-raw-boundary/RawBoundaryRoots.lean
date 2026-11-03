import RawBoundaryHalt
import DAllStarts

namespace BB6.RawBoundaryBridge
open BB6.Portfolio

/-- Each designated blank state of the literal D0 transition table is
    represented by its precise physical unary seed in the original zipper. -/
theorem all_six_blank_states_halt_iff_zipper (s : State) :
    haltsFrom D0 s ↔
      ∃ t : Nat,
        (CryptidBoundary.run t (unary (startSeed s))).st = 6 :=
  (every_blank_halts_iff_unary s).trans (raw_unary_halts_iff (startSeed s))

/-- The four distinct rooted D-family machines in the dated holdout list
    carry their genuine initial-state semantics through both reductions. -/
theorem D0_root_halts_iff_zipper_I9 :
    haltsFrom D0 (0 : State) ↔
      ∃ t : Nat, (CryptidBoundary.run t (unary 9)).st = 6 := by
  simpa [startSeed] using all_six_blank_states_halt_iff_zipper (0 : State)

theorem D1_root_halts_iff_zipper_I39 :
    haltsFrom D1 (0 : State) ↔
      ∃ t : Nat, (CryptidBoundary.run t (unary 39)).st = 6 :=
  D1_root_halts_iff_I39.trans (raw_unary_halts_iff 39)

theorem D2_root_halts_iff_zipper_I15 :
    haltsFrom D2 (0 : State) ↔
      ∃ t : Nat, (CryptidBoundary.run t (unary 15)).st = 6 :=
  D2_root_halts_iff_I15.trans (raw_unary_halts_iff 15)

theorem D3_root_halts_iff_zipper_I5 :
    haltsFrom D3 (0 : State) ↔
      ∃ t : Nat, (CryptidBoundary.run t (unary 5)).st = 6 :=
  D3_root_halts_iff_I5.trans (raw_unary_halts_iff 5)

#print axioms all_six_blank_states_halt_iff_zipper
#print axioms D0_root_halts_iff_zipper_I9
#print axioms D1_root_halts_iff_zipper_I39
#print axioms D2_root_halts_iff_zipper_I15
#print axioms D3_root_halts_iff_zipper_I5

end BB6.RawBoundaryBridge
