import CLine
import CoreCaseLemmas
set_option maxHeartbeats 0
namespace A38Mixed96

theorem source_phase1_A (a k : Nat)
    (h : coreA a (k+1) 0) : coreA a k 1 := by
  have he : lowA0 a (k+1) := by simpa [coreA] using h
  have hp := lowA1_of_lowA0 a k he
  simpa [coreA] using hp

theorem source_phase1_B (a k : Nat)
    (h : coreB a (k+1) 0) : coreB a k 1 := by
  have he : lowB0 a (k+1) := by simpa [coreB] using h
  have hp := lowB1_of_lowB0 a k he
  simpa [coreB] using hp

theorem source_phase3_A (a k : Nat)
    (h : coreA a (k+2) 1) : coreA a k 3 := by
  have he : lowA1 a (k+2) := by simpa [coreA] using h
  exact (coreA_high a k 3 (by omega)).mpr (highA_of_lowA1_c3 a k he)

theorem source_phase3_B (a k : Nat)
    (h : coreB a (k+2) 1) : coreB a k 3 := by
  have he : lowB1 a (k+2) := by simpa [coreB] using h
  exact (coreB_high a k 3 (by omega)).mpr (highB_of_lowB1_c3 a k he)

#print axioms source_phase1_A
#print axioms source_phase3_A
end A38Mixed96
