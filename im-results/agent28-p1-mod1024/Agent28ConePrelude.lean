import P1Gate
import P1ConeNoOne2
import Agent28PowerGap

namespace BB6.Agent28
open BB6.P1Reduction

theorem forbidden_mod (x y : Nat) (hr:BB6.Agent1.Reach x y)
    (hy:0<y) (hx:x%2=0) (hnot:x≠2) (hmod:x%4=2) : False := by
  rcases BB6.Agent1.reachable_even_mod4 x y hr hy hx with he | he <;> omega

theorem forbidden_power (n x y : Nat) (hr:BB6.Agent1.Reach x y)
    (hx:x%2=0) (hy:0<y) (hye:y%2=0)
    (hlo:7*2^n<x+12) (hhi:x+12<14*2^n) : False := by
  obtain ⟨j,hj⟩ := BB6.Agent1.even_left_power_shape x y hr hx hy hye
  exact no_power_between n (x+12) j hlo hhi hj

end BB6.Agent28
