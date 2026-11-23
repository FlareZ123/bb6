import Lean

namespace BB6SyncBlockPropagation

def CForm (A B : Int) := 4*A + 5*B
def DForm (A B : Int) := 3*A + 4*B

theorem left_A (A B da db : Int) :
    (A + da) - 3*(B + db) = A - 3*B + da - 3*db := by omega

theorem left_B (B db : Int) :
    3*(B + db) = 3*B + 3*db := by omega

theorem left_C (A B da db : Int) :
    4*(A + da) + 3*(B + db) =
      4*A + 3*B + 4*da + 3*db := by omega

theorem left_D (A B da db : Int) :
    3*((A + da) + (B + db)) =
      3*A + 3*B + 3*da + 3*db := by omega

theorem right_A (A B da db : Int) :
    (-CForm A B + da) - 3*(DForm A B + db) =
      -13*A - 17*B + da - 3*db := by
  simp [CForm, DForm]
  omega

theorem right_B (A B db : Int) :
    3*(DForm A B + db) = 9*A + 12*B + 3*db := by
  simp [DForm]
  omega

theorem right_C (A B da db : Int) :
    4*(-CForm A B + da) + 3*(DForm A B + db) =
      -7*A - 8*B + 4*da + 3*db := by
  simp [CForm, DForm]
  omega

theorem right_D (A B da db : Int) :
    3*((-CForm A B + da) + (DForm A B + db)) =
      -3*A - 3*B + 3*da + 3*db := by
  simp [CForm, DForm]
  omega

end BB6SyncBlockPropagation
