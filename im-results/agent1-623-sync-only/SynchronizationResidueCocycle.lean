import Lean

namespace BB6SyncResidueCocycle

def A (X Y : Int) := X - 3 * Y
def B (Y : Int) := 3 * Y
def CForm (X Y : Int) := 4 * X + 3 * Y
def DForm (X Y : Int) := 3 * (X + Y)

theorem cform_from_AB (X Y : Int) : CForm X Y = 4 * A X Y + 5 * B Y := by
  simp [CForm, A, B]
  omega

theorem dform_from_AB (X Y : Int) : DForm X Y = 3 * A X Y + 4 * B Y := by
  simp [DForm, A, B]
  omega

def leftX (X Y C : Int) := X - 3 * Y + C
def leftY (Y F : Int) := 3 * Y + F
def rightX (X Y C : Int) := -4 * X - 3 * Y + C
def rightY (X Y F : Int) := 3 * X + 3 * Y + F

theorem left_A (X Y C F : Int) :
    A (leftX X Y C) (leftY Y F) = A X Y - 3 * B Y + C - 3 * F := by
  simp [A, B, leftX, leftY]
  omega

theorem left_B (Y F : Int) :
    B (leftY Y F) = 3 * B Y + 3 * F := by
  simp [B, leftY]
  omega

theorem right_A (X Y C F : Int) :
    A (rightX X Y C) (rightY X Y F) =
      -13 * A X Y - 17 * B Y + C - 3 * F := by
  simp [A, B, rightX, rightY]
  omega

theorem right_B (X Y F : Int) :
    B (rightY X Y F) = 9 * A X Y + 12 * B Y + 3 * F := by
  simp [A, B, rightY]
  omega

theorem left_CForm (X Y C F : Int) :
    CForm (leftX X Y C) (leftY Y F) =
      4 * A X Y + 3 * B Y + 4 * C + 3 * F := by
  simp [CForm, A, B, leftX, leftY]
  omega

theorem left_DForm (X Y C F : Int) :
    DForm (leftX X Y C) (leftY Y F) =
      3 * A X Y + 3 * B Y + 3 * C + 3 * F := by
  simp [DForm, A, B, leftX, leftY]
  omega

theorem right_CForm (X Y C F : Int) :
    CForm (rightX X Y C) (rightY X Y F) =
      -7 * A X Y - 8 * B Y + 4 * C + 3 * F := by
  simp [CForm, A, B, rightX, rightY]
  omega

theorem right_DForm (X Y C F : Int) :
    DForm (rightX X Y C) (rightY X Y F) =
      -3 * A X Y - 3 * B Y + 3 * C + 3 * F := by
  simp [DForm, A, B, rightX, rightY]
  omega

theorem canonical_A (g q gamma : Int) :
    A (2*g-gamma) (6*q) = 2*(g-9*q)-gamma := by
  simp [A]
  omega

theorem canonical_B (q : Int) : B (6*q) = 18*q := by
  simp [B]
  omega

theorem canonical_CForm (p q gamma : Int) :
    CForm (2*(p-3*q)-gamma) (6*q) = 2*(4*p-3*q)-4*gamma := by
  simp [CForm]
  omega

theorem canonical_DForm (p q gamma : Int) :
    DForm (2*(p-3*q)-gamma) (6*q) = 6*p-3*gamma := by
  simp [DForm]
  omega

end BB6SyncResidueCocycle
