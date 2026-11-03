import Init.Omega
namespace BB6.Agent9OddWall
theorem positive_depth_wall_cost
    (q P m' b delta : Nat)
    (hq : 1 ≤ q)
    (hP : 256*q ≤ P)
    (hdelta : delta=12 ∨ delta=16)
    (hwall : b=4*m'+64*q+delta)
    (hlarge : 19*P ≤ b) :
    9*P ≤ 2*m' := by
  rcases hdelta with h | h <;> omega

theorem deeper_wall_cost
    (q P m' b delta : Nat)
    (hq : 1 ≤ q)
    (hP : 256*q ≤ P)
    (hdelta : delta=12 ∨ delta=16)
    (hwall : b=4*m'+64*q+delta)
    (hlarge : 29*P ≤ b) :
    7*P ≤ m' := by
  rcases hdelta with h | h <;> omega

#print axioms positive_depth_wall_cost
#print axioms deeper_wall_cost
end BB6.Agent9OddWall
