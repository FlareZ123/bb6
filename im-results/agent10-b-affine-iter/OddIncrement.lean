import PeriodMultiply

namespace BB6.Agent10IterBarrier

theorem G_odd_increment (z d : Nat) (hd : d%2=1) :
    2*G (z+d)=2*G z+3*d+7 ∨
    2*G (z+d)+7=2*G z+3*d := by
  have h0:=two_G z
  have h1:=two_G (z+d)
  have hp : z%2=0 ∨ z%2=1 := by omega
  rcases hp with hzero | hone
  · left
    have hc : (z+d)%2=1 := by omega
    rw [hzero] at h0
    rw [hc] at h1
    omega
  · right
    have hc : (z+d)%2=0 := by omega
    rw [hone] at h0
    rw [hc] at h1
    omega

end BB6.Agent10IterBarrier
