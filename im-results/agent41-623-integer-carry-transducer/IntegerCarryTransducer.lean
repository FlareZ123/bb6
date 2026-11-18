import Agent41DrainValuationNormalForm

/-!
# Integer carry bounds for the #623 root-gap cocycle

This file formalizes the uniform affine-correction bound and the closed
ternary carry ranges used by the buffered middle-digit transducer.
It does not formalize an all-time root-history invariant.
-/

namespace BB6.Agent41IntegerCarryTransducer

inductive Sector where
  | LO
  | LE
  | RO
  | RE
  deriving DecidableEq, Repr

def correctionLX (s : Sector) (D r : Int) : Int :=
  match s with
  | .LO => -18 * D - 16 * r - 122
  | .LE => -18 * D - 16 * r - 68
  | .RO => -18 * D - 16 * r
  | .RE => -18 * D - 16 * r - 52

def correctionLY (s : Sector) (D r : Int) : Int :=
  match s with
  | .LO => 12 * D + 12 * r + 84
  | .LE => 12 * D + 12 * r + 48
  | .RO => 12 * D + 12 * r
  | .RE => 12 * D + 12 * r + 30

def correctionRX (s : Sector) (D r : Int) : Int :=
  match s with
  | .LO => 12 * D + 4 * r - 6
  | .LE => 12 * D + 4 * r - 12
  | .RO => 12 * D + 4 * r - 44
  | .RE => 12 * D + 4 * r - 16

def correctionRY (s : Sector) (D r : Int) : Int :=
  match s with
  | .LO => 24 - 6 * D
  | .LE => 18 - 6 * D
  | .RO => 30 - 6 * D
  | .RE => 18 - 6 * D

/-- Every affine correction is bounded by the common source-derived buffer. -/
theorem corrections_bounded
    (s : Sector) (ell : Nat) (D r : Int)
    (hDlo : -(ell : Int) - 1 ≤ D)
    (hDhi : D ≤ (ell : Int) + 1)
    (hrlo : 0 ≤ r)
    (hrhi : r ≤ (ell : Int)) :
    let B : Int := 34 * (ell : Int) + 140
    -B ≤ correctionLX s D r ∧ correctionLX s D r ≤ B ∧
    -B ≤ correctionLY s D r ∧ correctionLY s D r ≤ B ∧
    -B ≤ correctionRX s D r ∧ correctionRX s D r ≤ B ∧
    -B ≤ correctionRY s D r ∧ correctionRY s D r ≤ B := by
  cases s <;> simp [correctionLX, correctionLY, correctionRX, correctionRY] <;> omega

/-- L-x carry remains in the deliberately generous buffered range. -/
theorem leftXCarry_closed
    (x y a : Int)
    (hx0 : 0 ≤ x) (hx2 : x ≤ 2)
    (hy0 : 0 ≤ y) (hy2 : y ≤ 2)
    (ha0 : -2 ≤ a) (ha2 : a ≤ 2) :
    -2 ≤ (x - y + a) / 3 ∧ (x - y + a) / 3 ≤ 2 := by
  omega

/-- L-y carry remains in the deliberately generous buffered range. -/
theorem leftYCarry_closed
    (y b : Int)
    (hy0 : 0 ≤ y) (hy2 : y ≤ 2)
    (hb0 : -2 ≤ b) (hb2 : b ≤ 2) :
    -2 ≤ (y + b) / 3 ∧ (y + b) / 3 ≤ 2 := by
  omega

/-- R-x carry remains in the deliberately generous buffered range. -/
theorem rightXCarry_closed
    (x xPrev yPrev a : Int)
    (hx0 : 0 ≤ x) (hx2 : x ≤ 2)
    (hxp0 : 0 ≤ xPrev) (hxp2 : xPrev ≤ 2)
    (hyp0 : 0 ≤ yPrev) (hyp2 : yPrev ≤ 2)
    (ha0 : -4 ≤ a) (ha2 : a ≤ 1) :
    -4 ≤ (-x - xPrev - yPrev + a) / 3 ∧
    (-x - xPrev - yPrev + a) / 3 ≤ 1 := by
  omega

/-- R-y carry remains in the deliberately generous buffered range. -/
theorem rightYCarry_closed
    (xPrev yPrev b : Int)
    (hxp0 : 0 ≤ xPrev) (hxp2 : xPrev ≤ 2)
    (hyp0 : 0 ≤ yPrev) (hyp2 : yPrev ≤ 2)
    (hb0 : -2 ≤ b) (hb2 : b ≤ 2) :
    -2 ≤ (xPrev + yPrev + b) / 3 ∧
    (xPrev + yPrev + b) / 3 ≤ 2 := by
  omega

/-- Euclidean ternary digits are always in the digit alphabet. -/
theorem ternaryDigit_range (n : Int) :
    0 ≤ n % 3 ∧ n % 3 < 3 := by
  omega

/-- Euclidean quotient and remainder give the exact digit decomposition. -/
theorem ternaryDigit_decomposition (n : Int) :
    n = 3 * (n / 3) + n % 3 := by
  omega

end BB6.Agent41IntegerCarryTransducer
