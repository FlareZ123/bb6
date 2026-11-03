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

end A38Mixed96
