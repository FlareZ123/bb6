import SignedCoordinateNormalForm

/-- The orientation-independent linear coordinate on the root gap plane. -/
def rayU (h q : Int) : Int := 2*h + 9*q

def leftUOffset : Sector → Int
  | .LO => 4
  | .LE => 4
  | .RO => 0
  | .RE => -9

def leftQOffset : Sector → Int
  | .LO => 14
  | .LE => 8
  | .RO => 0
  | .RE => 3

def rightUOffset : Sector → Int
  | .LO => 30
  | .LE => 15
  | .RO => 1
  | .RE => 7

def rightQOffset : Sector → Int
  | .LO => 4
  | .LE => 3
  | .RO => 5
  | .RE => 3

/-- Exact source cocycle in (u,q), left branch. The D term cancels from u'. -/
theorem left_ray_cocycle
    (s : Sector) (D R h q hp qp : Int)
    (hx : 2*hp = 2*h - 18*q + corrC s .L D R)
    (hy : 6*qp = 18*q + corrF s .L D R) :
    rayU hp qp = rayU h q + 2*R + leftUOffset s ∧
    qp = 3*q + 2*D + 2*R + leftQOffset s := by
  cases s <;> simp [rayU, leftUOffset, leftQOffset, corrC, corrF] at * <;> omega

/-- Exact source cocycle in (u,q), right branch, with denominators cleared. -/
theorem right_ray_cocycle_scaled
    (s : Sector) (D R h q hp qp : Int)
    (hx : 2*hp = -8*h - 18*q + corrC s .R D R)
    (hy : 6*qp = 6*h + 18*q + corrF s .R D R) :
    2 * rayU hp qp = rayU h q + 9*q + 6*D + 8*R + 2*rightUOffset s ∧
    2 * qp = rayU h q - 3*q - 2*D + 2*rightQOffset s := by
  cases s <;> simp [rayU, rightUOffset, rightQOffset, corrC, corrF] at * <;> omega

/-- The terminal ratio-four line is exactly u=9q. -/
theorem terminal_line_iff (h q : Int) : rayU h q = 9*q ↔ h = 0 := by
  dsimp [rayU]
  omega

/-- Both homogeneous branch matrices send the terminal ray h=0 to p'=0. -/
theorem ideal_left_terminal_ray (q : Int) :
    (0 - 9*q) + 3*(3*q) = 0 := by omega

theorem ideal_right_terminal_ray (q : Int) :
    (-4*0 - 9*q) + 3*(0 + 3*q) = 0 := by omega

/-- The homogeneous (u,q) branch matrices have determinant 3 and -3. -/
def rayLeftMatrix : Mat2 := ⟨1, 0, 0, 3⟩
def rayRightMatrixScaled : Mat2 := ⟨1, 9, 1, -3⟩

theorem ray_left_matrix_det : matDet rayLeftMatrix = 3 := by decide
theorem ray_right_matrix_scaled_det : matDet rayRightMatrixScaled = -12 := by decide

/-- A target terminal window pulls back to a narrow left cancellation strip. -/
theorem left_terminal_parent_strip
    (s : Sector) (D R h q hp W B : Int)
    (hx : 2*hp = 2*h - 18*q + corrC s .L D R)
    (hWlo : -W ≤ hp) (hWhi : hp ≤ W)
    (hClo : -B ≤ corrC s .L D R)
    (hChi : corrC s .L D R ≤ B) :
    -(2*W+B) ≤ rayU h q - 27*q ∧
    rayU h q - 27*q ≤ 2*W+B := by
  dsimp [rayU]
  omega

/-- A target terminal window pulls back to a narrow right cancellation strip. -/
theorem right_terminal_parent_strip
    (s : Sector) (D R h q hp W B : Int)
    (hx : 2*hp = -8*h - 18*q + corrC s .R D R)
    (hWlo : -W ≤ hp) (hWhi : hp ≤ W)
    (hClo : -B ≤ corrC s .R D R)
    (hChi : corrC s .R D R ≤ B) :
    -(2*W+B) ≤ 4*rayU h q - 18*q ∧
    4*rayU h q - 18*q ≤ 2*W+B := by
  dsimp [rayU]
  omega

/-- The digit-length source bound turns the terminal window into radius 52*ell+166.
    This version explicitly assumes L ≤ ell. -/
theorem left_terminal_parent_strip_from_digit_length
    (s : Sector) (L E R ell h q hp : Int)
    (hE0 : 0 ≤ E) (hEL : E ≤ L)
    (hR0 : 0 ≤ R) (hRell : R ≤ ell) (hLell : L ≤ ell)
    (hx : 2*hp = 2*h - 18*q + corrC s .L (L-2*E) R)
    (hWlo : -(9*ell+22) ≤ hp) (hWhi : hp ≤ 9*ell+22) :
    -(52*ell+166) ≤ rayU h q - 27*q ∧
    rayU h q - 27*q ≤ 52*ell+166 := by
  have hc := correction_buffer_by_depth s .L L E R ell hE0 hEL hR0 hRell hLell
  have hs := left_terminal_parent_strip s (L-2*E) R h q hp (9*ell+22) (34*ell+122)
    hx hWlo hWhi hc.1 hc.2.1
  rcases hs with ⟨hlo, hhi⟩
  constructor <;> omega

/-- The right-branch source bound gives the same integer radius before scaling.
    This version explicitly assumes L ≤ ell. -/
theorem right_terminal_parent_strip_from_digit_length
    (s : Sector) (L E R ell h q hp : Int)
    (hE0 : 0 ≤ E) (hEL : E ≤ L)
    (hR0 : 0 ≤ R) (hRell : R ≤ ell) (hLell : L ≤ ell)
    (hx : 2*hp = -8*h - 18*q + corrC s .R (L-2*E) R)
    (hWlo : -(9*ell+22) ≤ hp) (hWhi : hp ≤ 9*ell+22) :
    -(52*ell+166) ≤ 4*rayU h q - 18*q ∧
    4*rayU h q - 18*q ≤ 52*ell+166 := by
  have hc := correction_buffer_by_depth s .R L E R ell hE0 hEL hR0 hRell hLell
  have hs := right_terminal_parent_strip s (L-2*E) R h q hp (9*ell+22) (34*ell+122)
    hx hWlo hWhi hc.1 hc.2.1
  rcases hs with ⟨hlo, hhi⟩
  constructor <;> omega

/-- In the homogeneous cocycle, the two exact preimages of the terminal line
    u'=9q' are u=27q (left) and 2u=9q (right). -/
theorem left_ideal_preimage_terminal_iff (u q : Int) :
    u = 9*(3*q) ↔ u = 27*q := by omega

theorem right_ideal_preimage_terminal_iff (u q : Int) :
    u + 9*q = 9*(u - 3*q) ↔ 2*u = 9*q := by omega

/-- Exact zero-gap preimage equations for the two source branches. -/
theorem left_terminal_exact_preimage_iff
    (s : Sector) (D R h q hp : Int)
    (hx : 2*hp = 2*h - 18*q + corrC s .L D R) :
    hp = 0 ↔ rayU h q - 27*q = -corrC s .L D R := by
  dsimp [rayU]
  omega

theorem right_terminal_exact_preimage_iff
    (s : Sector) (D R h q hp : Int)
    (hx : 2*hp = -8*h - 18*q + corrC s .R D R) :
    hp = 0 ↔ 4*rayU h q - 18*q = corrC s .R D R := by
  dsimp [rayU]
  omega

/-- Conservative terminal-parent strips using only the depth bounds
    D in [-ell,ell+1] and R in [0,ell]. -/
theorem left_terminal_parent_strip_from_depth
    (s : Sector) (D R ell h q hp : Int)
    (hDlo : -ell ≤ D) (hDhi : D ≤ ell+1)
    (hRlo : 0 ≤ R) (hRhi : R ≤ ell)
    (hx : 2*hp = 2*h - 18*q + corrC s .L D R)
    (hWlo : -(9*ell+22) ≤ hp) (hWhi : hp ≤ 9*ell+22) :
    -(52*ell+184) ≤ rayU h q - 27*q ∧
    rayU h q - 27*q ≤ 52*ell+184 := by
  have hc := correction_buffer_from_depth s .L D R ell hDlo hDhi hRlo hRhi
  have hs := left_terminal_parent_strip s D R h q hp (9*ell+22) (34*ell+140)
    hx hWlo hWhi hc.1 hc.2.1
  rcases hs with ⟨hlo, hhi⟩
  constructor <;> omega

theorem right_terminal_parent_strip_from_depth
    (s : Sector) (D R ell h q hp : Int)
    (hDlo : -ell ≤ D) (hDhi : D ≤ ell+1)
    (hRlo : 0 ≤ R) (hRhi : R ≤ ell)
    (hx : 2*hp = -8*h - 18*q + corrC s .R D R)
    (hWlo : -(9*ell+22) ≤ hp) (hWhi : hp ≤ 9*ell+22) :
    -(52*ell+184) ≤ 4*rayU h q - 18*q ∧
    4*rayU h q - 18*q ≤ 52*ell+184 := by
  have hc := correction_buffer_from_depth s .R D R ell hDlo hDhi hRlo hRhi
  have hs := right_terminal_parent_strip s D R h q hp (9*ell+22) (34*ell+140)
    hx hWlo hWhi hc.1 hc.2.1
  rcases hs with ⟨hlo, hhi⟩
  constructor <;> omega

#print axioms left_ray_cocycle
#print axioms right_ray_cocycle_scaled
#print axioms terminal_line_iff
#print axioms ray_left_matrix_det
#print axioms ray_right_matrix_scaled_det
#print axioms left_terminal_parent_strip_from_digit_length
#print axioms right_terminal_parent_strip_from_digit_length
#print axioms left_ideal_preimage_terminal_iff
#print axioms right_ideal_preimage_terminal_iff
#print axioms left_terminal_exact_preimage_iff
#print axioms right_terminal_exact_preimage_iff
#print axioms left_terminal_parent_strip_from_depth
#print axioms right_terminal_parent_strip_from_depth
