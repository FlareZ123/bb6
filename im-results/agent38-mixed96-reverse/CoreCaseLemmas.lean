import CoreAnalytic
set_option maxHeartbeats 0
namespace A38Mixed96

theorem lowA1_of_lowA0 (a k : Nat) (h : lowA0 a (k+1)) : lowA1 a k := by
  unfold lowA0 at h
  unfold lowA1
  omega

theorem lowB1_of_lowB0 (a k : Nat) (h : lowB0 a (k+1)) : lowB1 a k := by
  unfold lowB0 at h
  unfold lowB1
  omega

#print axioms lowA1_of_lowA0
#print axioms lowB1_of_lowB0
theorem highA_of_lowA1_c3 (a k : Nat) (h : lowA1 a (k+2)) :
    highA (normX a 3) (normY k 3) := by
  unfold lowA1 at h
  unfold highA normX normY
  omega

theorem highB_of_lowB1_c3 (a k : Nat) (h : lowB1 a (k+2)) :
    highB (normX a 3) (normY k 3) := by
  unfold lowB1 at h
  unfold highB normX normY
  omega

#print axioms highA_of_lowA1_c3
#print axioms highB_of_lowB1_c3

theorem highA_no_sum_four (x y : Nat) (h : highA x y) :
    (x + y) % 4 ≠ 0 := by
  unfold highA at h
  omega

theorem highB_no_sum_four (x y : Nat) (h : highB x y) :
    (x + y) % 4 ≠ 0 := by
  unfold highB at h
  omega

#print axioms highA_no_sum_four
#print axioms highB_no_sum_four

theorem highA_no_sum_one (x y : Nat) (h : highA x y) :
    (x + y) % 24 ≠ 1 := by
  unfold highA at h
  omega

theorem highB_no_sum_one (x y : Nat) (h : highB x y) :
    (x + y) % 24 ≠ 1 := by
  unfold highB at h
  omega

#print axioms highA_no_sum_one
#print axioms highB_no_sum_one

end A38Mixed96
