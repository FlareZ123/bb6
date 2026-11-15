import Lean

/-
The leading projective gap maps are represented by the numerator matrices
A₅ = [[3,-8],[3,17]] and B₅ = [[-8,3],[17,3]].
The quadratic form P = [[91,64],[64,56]] is scaled by 91 below,
so gapPotential(r,l) = 91 * (r,l) P (r,l)^T.
-/

def gapPotential (r l : Int) : Int :=
  (91 * r + 64 * l) * (91 * r + 64 * l) + 1000 * l * l

theorem gapPotential_eq_91P (r l : Int) :
    gapPotential r l = 91 * (91*r*r + 128*r*l + 56*l*l) := by
  grind [gapPotential]

theorem int_sq_nonneg (x : Int) : 0 ≤ x * x := by
  by_cases h : 0 ≤ x
  · exact Int.mul_nonneg h h
  · have hx : x ≤ 0 := (Int.le_total x 0).resolve_right h
    have hn : 0 ≤ -x := Int.neg_nonneg.mpr hx
    have hsq := Int.mul_nonneg hn hn
    simpa [Int.neg_mul_neg] using hsq

theorem gapPotential_nonneg (r l : Int) : 0 ≤ gapPotential r l := by
  unfold gapPotential
  have h1 := int_sq_nonneg (91*r + 64*l)
  have h2 := int_sq_nonneg l
  have hc : 0 ≤ (1000 : Int) := by omega
  have h3' := Int.mul_nonneg hc h2
  have h3 : 0 ≤ 1000 * l * l := by simpa [Int.mul_assoc] using h3'
  exact Int.add_nonneg h1 h3

theorem farLeft_scaled_identity (r l : Int) :
    gapPotential (3*r - 8*l) (3*r + 17*l) - 25 * gapPotential r l =
      18200 * (r + 4*l) * (r + 4*l) := by
  grind [gapPotential]

theorem nearLeft_scaled_identity (r l : Int) :
    2 * gapPotential (-8*r + 3*l) (17*r + 3*l) - 75 * gapPotential r l =
      216125 * r * r + 68250 * l * l := by
  grind [gapPotential]

theorem farLeft_scaled_growth (r l : Int) :
    25 * gapPotential r l ≤ gapPotential (3*r - 8*l) (3*r + 17*l) := by
  have hdiff : 0 ≤ gapPotential (3*r - 8*l) (3*r + 17*l) - 25 * gapPotential r l := by
    rw [farLeft_scaled_identity]
    have hs := int_sq_nonneg (r + 4*l)
    have hc : 0 ≤ (18200 : Int) := by omega
    have hmul := Int.mul_nonneg hc hs
    simpa [Int.mul_assoc] using hmul
  omega

theorem nearLeft_scaled_growth (r l : Int) :
    75 * gapPotential r l ≤ 2 * gapPotential (-8*r + 3*l) (17*r + 3*l) := by
  have hdiff : 0 ≤ 2 * gapPotential (-8*r + 3*l) (17*r + 3*l) - 75 * gapPotential r l := by
    rw [nearLeft_scaled_identity]
    have hc1 : 0 ≤ (216125 : Int) := by omega
    have hc2 : 0 ≤ (68250 : Int) := by omega
    have h1' := Int.mul_nonneg hc1 (int_sq_nonneg r)
    have h2' := Int.mul_nonneg hc2 (int_sq_nonneg l)
    have h1 : 0 ≤ 216125 * r * r := by simpa [Int.mul_assoc] using h1'
    have h2 : 0 ≤ 68250 * l * l := by simpa [Int.mul_assoc] using h2'
    exact Int.add_nonneg h1 h2
  omega

/-- The sector-adapted form corresponding exactly to 900 times quadraticGap. -/
def naturalGapPotential (r l : Int) : Int :=
  75 * (r + l) * (r + l) + 9 * (r - l) * (r - l)

theorem naturalGapPotential_nonneg (r l : Int) : 0 ≤ naturalGapPotential r l := by
  have h1 := int_sq_nonneg (r+l)
  have h2 := int_sq_nonneg (r-l)
  have hc1 : 0 ≤ (75 : Int) := by omega
  have hc2 : 0 ≤ (9 : Int) := by omega
  have h1' := Int.mul_nonneg hc1 h1
  have h2' := Int.mul_nonneg hc2 h2
  have h1'' : 0 ≤ 75 * (r+l) * (r+l) := by simpa [Int.mul_assoc] using h1'
  have h2'' : 0 ≤ 9 * (r-l) * (r-l) := by simpa [Int.mul_assoc] using h2'
  exact Int.add_nonneg h1'' h2''

theorem naturalGapPotential_eq_900Q_left (g m : Int) :
    naturalGapPotential (-15*m-4*g) g =
      900 * (g*g + 9*g*m + 21*m*m) := by
  grind [naturalGapPotential]

theorem naturalGapPotential_eq_900Q_right (g m : Int) :
    naturalGapPotential g (-15*m-4*g) =
      900 * (g*g + 9*g*m + 21*m*m) := by
  grind [naturalGapPotential]

theorem farLeft_natural_scaled_identity (r l : Int) :
    naturalGapPotential (3*r - 8*l) (3*r + 17*l) - 25 * naturalGapPotential r l =
      600 * (r + 4*l) * (r + 4*l) := by
  grind [naturalGapPotential]

theorem nearLeft_natural_scaled_identity (r l : Int) :
    naturalGapPotential (-8*r + 3*l) (17*r + 3*l) - 25 * naturalGapPotential r l =
      600 * (4*r + l) * (4*r + l) := by
  grind [naturalGapPotential]

