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
end A38Mixed96
