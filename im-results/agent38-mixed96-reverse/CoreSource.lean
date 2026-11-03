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
theorem no_coreA_czero_a0 (k : Nat) :
    ¬coreA 1 0 (2*k+2) := by
  intro h
  have hp := (coreA_high 1 0 (2*k+2) (by omega)).mp h
  have bad := highA_no_sum_one _ _ hp
  apply bad
  unfold normX normY
  omega

theorem no_coreB_czero_a0 (k : Nat) :
    ¬coreB 1 0 (2*k+2) := by
  intro h
  have hp := (coreB_high 1 0 (2*k+2) (by omega)).mp h
  have bad := highB_no_sum_one _ _ hp
  apply bad
  unfold normX normY
  omega

theorem no_coreA_czero_a1 (k : Nat) :
    ¬coreA 2 2 (2*k+1) := by
  by_cases hk : k = 0
  · subst k
    simp [coreA, lowA1]
  · intro h
    have hp := (coreA_high 2 2 (2*k+1) (by omega)).mp h
    have bad := highA_no_sum_four _ _ hp
    apply bad
    unfold normX normY
    omega

theorem no_coreB_czero_a1 (k : Nat) :
    ¬coreB 2 2 (2*k+1) := by
  by_cases hk : k = 0
  · subst k
    simp [coreB, lowB1]
  · intro h
    have hp := (coreB_high 2 2 (2*k+1) (by omega)).mp h
    have bad := highB_no_sum_four _ _ hp
    apply bad
    unfold normX normY
    omega

theorem no_coreA_lowmiddleone (a : Nat) : ¬coreA a 1 1 := by
  simp [coreA, lowA1]

theorem no_coreB_lowmiddleone (a : Nat) : ¬coreB a 1 1 := by
  simp [coreB, lowB1]

theorem source_czero_reset_A (a k : Nat) (hk : 1 ≤ k)
    (h : coreA a 1 (2*k+1)) : coreA (a+2) k 0 := by
  have he := (coreA_high a 1 (2*k+1) (by omega)).mp h
  have hp := lowA0_of_high_reset a k hk he
  simpa [coreA] using hp

theorem source_czero_reset_B (a k : Nat) (hk : 1 ≤ k)
    (h : coreB a 1 (2*k+1)) : coreB (a+2) k 0 := by
  have he := (coreB_high a 1 (2*k+1) (by omega)).mp h
  have hp := lowB0_of_high_reset a k hk he
  simpa [coreB] using hp

theorem no_coreA_high_even (k d : Nat) (hk : k % 2 = 0) :
    ¬coreA (4*(k/2)+2) 2 (d+1) := by
  by_cases hd : d = 0
  · subst d
    simp [coreA, lowA1]
  · intro h
    have hp := (coreA_high (4*(k/2)+2) 2 (d+1) (by omega)).mp h
    have bad := highA_no_sum_four _ _ hp
    apply bad
    unfold normX normY
    omega

theorem no_coreB_high_even (k d : Nat) (hk : k % 2 = 0) :
    ¬coreB (4*(k/2)+2) 2 (d+1) := by
  by_cases hd : d = 0
  · subst d
    simp [coreB, lowB1]
  · intro h
    have hp := (coreB_high (4*(k/2)+2) 2 (d+1) (by omega)).mp h
    have bad := highB_no_sum_four _ _ hp
    apply bad
    unfold normX normY
    omega

end A38Mixed96
