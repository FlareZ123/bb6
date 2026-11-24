import BoundaryPortfolio
import DAllBlankHalting

namespace BB6.BoundaryPortfolio
open BB6.Portfolio

def I (n : Nat) : B := CryptidBoundary.init (List.replicate (n-2) true)

/-- Live prefix excludes all earlier halts, and shifts the exact remaining
    live-transition count, with no synthetic sink step added. -/
theorem prefix_time_decompose (c d : B) (p T : Nat)
    (hp : CryptidBoundary.run p c = d) (hd : d.st < 6) :
    firstFrozen c T ↔ ∃ t, T=p+t ∧ firstFrozen d t := by
  constructor
  · intro ht
    have hle : p ≤ T := by
      by_cases hle : p ≤ T
      · exact hle
      · exfalso
        have he : p = (T+1) + (p-(T+1)) := by omega
        have hh : (CryptidBoundary.run p c).st = 6 := by
          rw [he, CryptidBoundary.run_add, BB6.Agent36.run_terminal _ _ ht.2]
          exact ht.2
        rw [hp] at hh
        omega
    refine ⟨T-p, by omega, ?_⟩
    apply (firstFrozen_prefix c d p (T-p) hp).mp
    rwa [show p+(T-p) = T by omega]
  · rintro ⟨t,rfl,ht⟩
    exact (firstFrozen_prefix c d p t hp).mpr ht

theorem D0_root_time (T : Nat) :
    haltsAt D0 0 T ↔ ∃ t, T=36+t ∧ firstFrozen (I 9) t := by
  rw [raw_haltsAt_iff]
  exact prefix_time_decompose _ _ 36 T BB6.Agent36.source_blank_A36 (by decide)

theorem D3_root_time (T : Nat) :
    haltsAt D3 0 T ↔ ∃ t, T=15+t ∧ firstFrozen (I 5) t := by
  rw [D3_haltsAt_iff]
  exact prefix_time_decompose _ _ 15 T BB6.Agent36.source_blank_B15 (by decide)

theorem D2_root_time (T : Nat) :
    haltsAt D2 0 T ↔ ∃ t, T=92+t ∧ firstFrozen (I 15) t := by
  rw [D2_haltsAt_iff]
  exact prefix_time_decompose _ _ 92 T BB6.Agent36.source_blank_C92 (by decide)

theorem D1_root_time (T : Nat) :
    haltsAt D1 0 T ↔ ∃ t, T=403+t ∧ firstFrozen (I 39) t := by
  rw [D1_haltsAt_iff]
  exact prefix_time_decompose _ _ 403 T BB6.Agent36.source_blank_F403 (by decide)

theorem D0_root_halts : haltsFrom D0 0 ↔ BB6.Agent36.SourceHalts (I 9) :=
  (raw_halts_iff 0).trans BB6.Agent36.blank_A_halts_iff_I9

theorem D3_root_halts : haltsFrom D3 0 ↔ BB6.Agent36.SourceHalts (I 5) :=
  D3_halts_iff.trans BB6.Agent36.blank_B_halts_iff_I5

theorem D2_root_halts : haltsFrom D2 0 ↔ BB6.Agent36.SourceHalts (I 15) :=
  D2_halts_iff.trans BB6.Agent36.blank_C_halts_iff_I15

theorem D1_root_halts : haltsFrom D1 0 ↔ BB6.Agent36.SourceHalts (I 39) :=
  D1_halts_iff.trans BB6.Agent36.blank_F_halts_iff_I39

#print axioms prefix_time_decompose
#print axioms D0_root_time
#print axioms D3_root_time
#print axioms D2_root_time
#print axioms D1_root_time
#print axioms D0_root_halts
#print axioms D3_root_halts
#print axioms D2_root_halts
#print axioms D1_root_halts
end BB6.BoundaryPortfolio
