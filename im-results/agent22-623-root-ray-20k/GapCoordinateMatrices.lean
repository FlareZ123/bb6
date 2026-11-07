import Lean

def gapR (x y : Int) : Int := y - 4 * x
def gapL (x y : Int) : Int := x - 4 * y

theorem gap_coordinates_inverse (x y : Int) :
    15 * x = -(4 * gapR x y + gapL x y) /\
    15 * y = -(gapR x y + 4 * gapL x y) := by
  constructor <;> simp [gapR, gapL] <;> omega

theorem far_left_gap_matrix (x y : Int) :
    3 * gapR x y - 8 * gapL x y = 5 * (7 * y - 4 * x) /\
    3 * gapR x y + 17 * gapL x y = 5 * (x - 13 * y) := by
  constructor <;> simp [gapR, gapL] <;> omega

theorem near_left_gap_matrix (x y : Int) :
    -8 * gapR x y + 3 * gapL x y = 5 * (7 * x - 4 * y) /\
    17 * gapR x y + 3 * gapL x y = 5 * (y - 13 * x) := by
  constructor <;> simp [gapR, gapL] <;> omega
