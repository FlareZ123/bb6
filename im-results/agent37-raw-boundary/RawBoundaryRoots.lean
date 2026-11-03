import RawBoundaryInit
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

/-- The same four distinct authentic blank roots, now stated directly
    in terms of the preexisting Agent31 init and unmodified transition table. -/
theorem D0_root_halts_iff_init7 :
    haltsFrom D0 (0 : State) ↔
      ∃ t : Nat,
        (CryptidBoundary.run t
          (CryptidBoundary.init (List.replicate 7 true))).st = 6 := by
  simpa only [show unary 9 = CryptidBoundary.init (List.replicate 7 true)
    from unary_eq_init_replicate 7] using D0_root_halts_iff_zipper_I9

theorem D1_root_halts_iff_init37 :
    haltsFrom D1 (0 : State) ↔
      ∃ t : Nat,
        (CryptidBoundary.run t
          (CryptidBoundary.init (List.replicate 37 true))).st = 6 := by
  simpa only [show unary 39 = CryptidBoundary.init (List.replicate 37 true)
    from unary_eq_init_replicate 37] using D1_root_halts_iff_zipper_I39

theorem D2_root_halts_iff_init13 :
    haltsFrom D2 (0 : State) ↔
      ∃ t : Nat,
        (CryptidBoundary.run t
          (CryptidBoundary.init (List.replicate 13 true))).st = 6 := by
  simpa only [show unary 15 = CryptidBoundary.init (List.replicate 13 true)
    from unary_eq_init_replicate 13] using D2_root_halts_iff_zipper_I15

theorem D3_root_halts_iff_init3 :
    haltsFrom D3 (0 : State) ↔
      ∃ t : Nat,
        (CryptidBoundary.run t
          (CryptidBoundary.init (List.replicate 3 true))).st = 6 := by
  simpa only [show unary 5 = CryptidBoundary.init (List.replicate 3 true)
    from unary_eq_init_replicate 3] using D3_root_halts_iff_zipper_I5

#print axioms all_six_blank_states_halt_iff_zipper
#print axioms D0_root_halts_iff_zipper_I9
#print axioms D1_root_halts_iff_zipper_I39
#print axioms D2_root_halts_iff_zipper_I15
#print axioms D3_root_halts_iff_zipper_I5
#print axioms D0_root_halts_iff_init7
#print axioms D1_root_halts_iff_init37
#print axioms D2_root_halts_iff_init13
#print axioms D3_root_halts_iff_init3

end BB6.RawBoundaryBridge
