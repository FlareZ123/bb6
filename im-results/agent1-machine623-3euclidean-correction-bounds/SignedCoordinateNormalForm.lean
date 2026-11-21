import Std.Tactic

structure Mat2 where
  a11 : Int
  a12 : Int
  a21 : Int
  a22 : Int
  deriving DecidableEq, Repr

def matMul (A B : Mat2) : Mat2 :=
  ⟨ A.a11 * B.a11 + A.a12 * B.a21
  , A.a11 * B.a12 + A.a12 * B.a22
  , A.a21 * B.a11 + A.a22 * B.a21
  , A.a21 * B.a12 + A.a22 * B.a22 ⟩

def matScale2 (A : Mat2) : Mat2 :=
  ⟨2*A.a11, 2*A.a12, 2*A.a21, 2*A.a22⟩

def matDet (A : Mat2) : Int := A.a11*A.a22 - A.a12*A.a21

def I2 : Mat2 := ⟨1,0,0,1⟩
def ML : Mat2 := ⟨1,-3,0,3⟩
def MR : Mat2 := ⟨-4,-3,3,3⟩
def U : Mat2 := ⟨-4,-5,3,4⟩
def P : Mat2 := ⟨1,5,-1,-3⟩
def NL : Mat2 := ⟨3,3,1,5⟩
def NR : Mat2 := ⟨3,3,-1,-5⟩

theorem right_factorization : MR = matMul U ML := by decide
theorem involution : matMul U U = I2 := by decide
theorem involution_determinant : matDet U = -1 := by decide
theorem left_determinant : matDet ML = 3 := by decide
theorem right_determinant : matDet MR = -3 := by decide
theorem basis_determinant : matDet P = 2 := by decide

-- These are P^{-1} M_L P = N_L/2 and P^{-1} M_R P = N_R/2,
-- stated without division by clearing the denominator 2.
theorem left_conjugacy_cleared :
    matScale2 (matMul ML P) = matMul P NL := by decide

theorem right_conjugacy_cleared :
    matScale2 (matMul MR P) = matMul P NR := by decide

-- Canonical coordinates have x = 2h and y = 6q.
def wCoord (h q : Int) : Int := -h - 5*q
def vCoord (h q : Int) : Int := h + 3*q

theorem coordinate_sum (h q : Int) :
    wCoord h q + vCoord h q = -2*q := by
  dsimp [wCoord, vCoord]
  omega

theorem x_reconstruction (h q : Int) :
    3*wCoord h q + 5*vCoord h q = 2*h := by
  dsimp [wCoord, vCoord]
  omega

theorem y_reconstruction (h q : Int) :
    -3*(wCoord h q + vCoord h q) = 6*q := by
  dsimp [wCoord, vCoord]
  omega

inductive Sector where
  | LO | LE | RO | RE
  deriving DecidableEq, Repr

inductive Branch where
  | L | R
  deriving DecidableEq, Repr

-- Full-drain convention: in RE, R includes the initial evaluator.
def corrC : Sector → Branch → Int → Int → Int
  | .LO, .L, D, R => -18*D - 16*R - 122
  | .LE, .L, D, R => -18*D - 16*R - 68
  | .RO, .L, D, R => -18*D - 16*R
  | .RE, .L, D, R => -18*D - 16*R - 36
  | .LO, .R, D, R => 12*D + 4*R - 6
  | .LE, .R, D, R => 12*D + 4*R - 12
  | .RO, .R, D, R => 12*D + 4*R - 44
  | .RE, .R, D, R => 12*D + 4*R - 20

def corrF : Sector → Branch → Int → Int → Int
  | .LO, .L, D, R => 12*D + 12*R + 84
  | .LE, .L, D, R => 12*D + 12*R + 48
  | .RO, .L, D, R => 12*D + 12*R
  | .RE, .L, D, R => 12*D + 12*R + 18
  | .LO, .R, D, _R => -6*D + 24
  | .LE, .R, D, _R => -6*D + 18
  | .RO, .R, D, _R => -6*D + 30
  | .RE, .R, D, _R => -6*D + 18

def corrA : Sector → Branch → Int → Int → Int
  | .LO, .L, D, R => -D - 2*R - 9
  | .LE, .L, D, R => -D - 2*R - 6
  | .RO, .L, D, R => -D - 2*R
  | .RE, .L, D, R => -D - 2*R + 3
  | .LO, .R, D, R => -D - 2*R - 17
  | .LE, .R, D, R => -D - 2*R - 9
  | .RO, .R, D, R => -D - 2*R - 3
  | .RE, .R, D, R => -D - 2*R - 5

def corrB : Sector → Branch → Int → Int → Int
  | .LO, .L, D, R => -3*D - 2*R - 19
  | .LE, .L, D, R => -3*D - 2*R - 10
  | .RO, .L, D, R => -3*D - 2*R
  | .RE, .L, D, R => -3*D - 2*R - 9
  | .LO, .R, D, R => 3*D + 2*R + 9
  | .LE, .R, D, R => 3*D + 2*R + 3
  | .RO, .R, D, R => 3*D + 2*R - 7
  | .RE, .R, D, R => 3*D + 2*R - 1

theorem corrA_identity (s : Sector) (b : Branch) (D R : Int) :
    6 * corrA s b D R = -3 * corrC s b D R - 5 * corrF s b D R := by
  cases s <;> cases b <;> simp [corrA, corrC, corrF] <;> omega

theorem corrB_identity (s : Sector) (b : Branch) (D R : Int) :
    2 * corrB s b D R = corrC s b D R + corrF s b D R := by
  cases s <;> cases b <;> simp [corrB, corrC, corrF] <;> omega

-- Exact affine normal form, with h=x/2 and q=y/6.
theorem left_signed_update
    (h q hp qp A B C F : Int)
    (hx : 2*hp = 2*h - 18*q + C)
    (hy : 6*qp = 18*q + F)
    (hA : 6*A = -3*C - 5*F)
    (hB : 2*B = C + F) :
    (-hp - 5*qp = (-h - 5*q) - q + A) ∧
    (hp + 3*qp = h + B) := by
  constructor <;> omega

theorem right_signed_update
    (h q hp qp A B C F : Int)
    (hx : 2*hp = -8*h - 18*q + C)
    (hy : 6*qp = 6*h + 18*q + F)
    (hA : 6*A = -3*C - 5*F)
    (hB : 2*B = C + F) :
    (-hp - 5*qp = (-h - 5*q) - q + A) ∧
    (hp + 3*qp = -h + B) := by
  constructor <;> omega

#print axioms right_factorization
#print axioms left_conjugacy_cleared
#print axioms corrA_identity
#print axioms corrB_identity
#print axioms left_signed_update
#print axioms right_signed_update


-- One extra ternary buffer digit: if the low residue is in [0,3K)
-- and the affine correction has absolute value < K, the carry is in {-1,0,1}.
theorem one_extra_digit_carry_bound
    (K r c q s : Int)
    (hK : 0 < K)
    (hr0 : 0 ≤ r) (hr1 : r < 3*K)
    (hc0 : -K < c) (hc1 : c < K)
    (hdiv : r + c = 3*K*q + s)
    (hs0 : 0 ≤ s) (hs1 : s < 3*K) :
    -1 ≤ q ∧ q ≤ 1 := by
  constructor
  · by_cases hq : q ≤ -2
    · have hmul : 3*K*q ≤ (3*K)*(-2) :=
        Int.mul_le_mul_of_nonneg_left hq (by omega)
      have hmul' : 3*K*q ≤ -6*K := by omega
      have hleft : -K < r+c := by omega
      have hright : 3*K*q+s < -3*K := by omega
      omega
    · omega
  · by_cases hq : 2 ≤ q
    · have hmul : (3*K)*2 ≤ 3*K*q :=
        Int.mul_le_mul_of_nonneg_left hq (by omega)
      have hmul' : 6*K ≤ 3*K*q := by omega
      have hleft : r+c < 4*K := by omega
      have hright : 6*K ≤ 3*K*q+s := by omega
      omega
    · omega

#print axioms one_extra_digit_carry_bound

def J : Mat2 := ⟨1,0,0,-1⟩

theorem involution_diagonalized_by_P : matMul U P = matMul P J := by decide
#print axioms involution_diagonalized_by_P


/-- Tight weighted-digit bounds, using D = L - 2*n₂ and n₂ ≤ R = n₁+n₂ ≤ L. -/
theorem correction_count_bounds (s : Sector) (b : Branch)
    (L E R : Int) (hE0 : 0 ≤ E) (hER : E ≤ R) (hRL : R ≤ L) :
    -(34*L+122) ≤ corrC s b (L-2*E) R ∧
    corrC s b (L-2*E) R ≤ 34*L+122 ∧
    -(24*L+84) ≤ corrF s b (L-2*E) R ∧
    corrF s b (L-2*E) R ≤ 24*L+84 := by
  cases s <;> cases b <;> simp [corrC, corrF] <;> omega

/-- The correction-only buffer 34*L+140 strictly dominates both corrections. -/
theorem correction_buffer_strict (s : Sector) (b : Branch)
    (L E R : Int) (hE0 : 0 ≤ E) (hER : E ≤ R) (hRL : R ≤ L) :
    -(34*L+140) < corrC s b (L-2*E) R ∧
    corrC s b (L-2*E) R < 34*L+140 ∧
    -(34*L+140) < corrF s b (L-2*E) R ∧
    corrF s b (L-2*E) R < 34*L+140 := by
  have h := correction_count_bounds s b L E R hE0 hER hRL
  omega


/-- Closed-bound variant: equality |c| = K is allowed. -/
theorem one_extra_digit_carry_bound_closed
    (K r c q s : Int)
    (hK : 0 < K)
    (hr0 : 0 ≤ r) (hr1 : r < 3*K)
    (hc0 : -K ≤ c) (hc1 : c ≤ K)
    (hdiv : r + c = 3*K*q + s)
    (hs0 : 0 ≤ s) (hs1 : s < 3*K) :
    -1 ≤ q ∧ q ≤ 1 := by
  constructor
  · by_cases hq : q ≤ -2
    · have hmul : 3*K*q ≤ (3*K)*(-2) :=
        Int.mul_le_mul_of_nonneg_left hq (by omega)
      have hmul' : 3*K*q ≤ -6*K := by omega
      have hleft : -K ≤ r+c := by omega
      have hright : 3*K*q+s < -3*K := by omega
      omega
    · omega
  · by_cases hq : 2 ≤ q
    · have hmul : (3*K)*2 ≤ 3*K*q :=
        Int.mul_le_mul_of_nonneg_left hq (by omega)
      have hmul' : 6*K ≤ 3*K*q := by omega
      have hleft : r+c < 4*K := by omega
      have hright : 6*K ≤ 3*K*q+s := by omega
      omega
    · omega


/-- The same K bounds both affine corrections, with equality permitted. -/
theorem correction_buffer_closed (s : Sector) (b : Branch)
    (L E R : Int) (hE0 : 0 ≤ E) (hER : E ≤ R) (hRL : R ≤ L) :
    -(34*L+122) ≤ corrC s b (L-2*E) R ∧
    corrC s b (L-2*E) R ≤ 34*L+122 ∧
    -(34*L+122) ≤ corrF s b (L-2*E) R ∧
    corrF s b (L-2*E) R ≤ 34*L+122 := by
  have h := correction_count_bounds s b L E R hE0 hER hRL
  omega

/-- A depth-only correction bound using the actual full-drain statistics.
    Here D is the signed first-counter drop and R is the full evaluator-call
    count; no digit-count identification is assumed. -/
theorem correction_buffer_from_depth (s : Sector) (b : Branch)
    (D R ell : Int)
    (hDlo : -ell ≤ D) (hDhi : D ≤ ell+1)
    (hRlo : 0 ≤ R) (hRhi : R ≤ ell) :
    -(34*ell+140) ≤ corrC s b D R ∧
    corrC s b D R ≤ 34*ell+140 ∧
    -(24*ell+96) ≤ corrF s b D R ∧
    corrF s b D R ≤ 24*ell+96 := by
  cases s <;> cases b <;> simp [corrC, corrF] <;> omega

/-- Refined correction bound if the source drain is linked to the digit
    normal form D=L-2E. R remains the independent full-drain call count;
    no assumption E≤R or R≤L is needed. -/
theorem correction_buffer_by_depth (s : Sector) (b : Branch)
    (L E R ell : Int)
    (hE0 : 0 ≤ E) (hEL : E ≤ L)
    (hR0 : 0 ≤ R) (hRell : R ≤ ell) (hLell : L ≤ ell) :
    -(34*ell+122) ≤ corrC s b (L-2*E) R ∧
    corrC s b (L-2*E) R ≤ 34*ell+122 ∧
    -(24*ell+84) ≤ corrF s b (L-2*E) R ∧
    corrF s b (L-2*E) R ≤ 24*ell+84 := by
  cases s <;> cases b <;> simp [corrC, corrF] <;> omega

#print axioms correction_buffer_from_depth
#print axioms correction_buffer_by_depth


/-- Joint correction lower bound.  The relation E ≤ R ≤ L is essential:
    it keeps the positive 12E term coupled to the full drain count. -/
theorem correction_sum_lower_bound (s : Sector) (b : Branch)
    (L E R : Int) (hE0 : 0 ≤ E) (hER : E ≤ R) (hRL : R ≤ L) :
    -(10*L+38) ≤
      corrC s b (L-2*E) R + corrF s b (L-2*E) R := by
  cases s <;> cases b <;> simp [corrC, corrF] <;> omega

/-- The joint correction sum is strictly greater than -K under the
    mass-indexed 34*ell+122 buffer. -/
theorem correction_sum_buffer_strict (s : Sector) (b : Branch)
    (L E R ell K : Int)
    (hE0 : 0 ≤ E) (hER : E ≤ R) (hRL : R ≤ L)
    (hLell : L ≤ ell) (hell0 : 0 ≤ ell)
    (hK : 34*ell+122 < K) :
    -K < corrC s b (L-2*E) R + corrF s b (L-2*E) R := by
  have hsum := correction_sum_lower_bound s b L E R hE0 hER hRL
  have hbuf : 10*L+38 < K := by omega
  omega

#print axioms correction_sum_lower_bound
#print axioms correction_sum_buffer_strict
