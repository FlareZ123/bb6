import BDyadic

namespace BB6.OneDim

/-- The scalar branch choice is the entire offset of the affine update. -/
theorem G_balance (z : Nat) : 2 * G z = 3*z+8+7*(z%2) := by
  simp only [G]
  omega

theorem G_order (z w : Nat) (heq : z%2=w%2) (hle : z≤w) :
    G z ≤ G w := by
  have a := G_balance z
  have b := G_balance w
  omega

theorem G_gap (z w : Nat) (heq : z%2=w%2) (hle : z≤w) :
    2*(G w-G z)=3*(w-z) := by
  have a := G_balance z
  have b := G_balance w
  have ord := G_order z w heq hle
  omega

end BB6.OneDim
