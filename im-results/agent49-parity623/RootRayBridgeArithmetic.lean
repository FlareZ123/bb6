import Std

namespace BB6.Agent49RootRayBridgeArithmetic

/-- Odd far-left branch: the right-ray gap tracks 7*y-4*x. -/
theorem oddFarRightGap (x y a d n c : Nat)
    (hxy : y + 5 ≤ x)
    (hc : c = 1 ∨ c = 2)
    (hfirstLower : x - y - 5 ≤ a + n + 1)
    (hfirstUpper : a ≤ x - y - 5 + n)
    (hthirdLower : 3*y + 14 ≤ d)
    (hthirdUpper : d ≤ 3*y + 16 + 4*n) :
    -(8*n+39 : Int) ≤
      (d : Int) - 4*(a : Int) - (c : Int) -
        (7*(y : Int) - 4*(x : Int)) ∧
      (d : Int) - 4*(a : Int) - (c : Int) -
        (7*(y : Int) - 4*(x : Int)) ≤ (8*n+39 : Int) := by
  omega

/-- Odd far-left branch: the left-ray gap tracks x-13*y. -/
theorem oddFarLeftGap (x y a d n c : Nat)
    (hxy : y + 5 ≤ x)
    (hc : c = 5 ∨ c = 9)
    (hfirstLower : x - y - 5 ≤ a + n + 1)
    (hfirstUpper : a ≤ x - y - 5 + n)
    (hthirdLower : 3*y + 14 ≤ d)
    (hthirdUpper : d ≤ 3*y + 16 + 4*n) :
    -(17*n+79 : Int) ≤
      (a : Int) - 4*(d : Int) - (c : Int) -
        ((x : Int) - 13*(y : Int)) ∧
      (a : Int) - 4*(d : Int) - (c : Int) -
        ((x : Int) - 13*(y : Int)) ≤ (17*n+79 : Int) := by
  omega

/-- Even far-left branch: the right-ray gap tracks 7*y-4*x. -/
theorem evenFarRightGap (x y a d n c : Nat)
    (hxy : y + 3 ≤ x)
    (hc : c = 1 ∨ c = 2)
    (hfirstLower : x - y - 2 ≤ a + n + 1)
    (hfirstUpper : a ≤ x - y - 2 + n)
    (hthirdLower : 3*y + 8 ≤ d)
    (hthirdUpper : d ≤ 3*y + 10 + 4*n) :
    -(8*n+21 : Int) ≤
      (d : Int) - 4*(a : Int) - (c : Int) -
        (7*(y : Int) - 4*(x : Int)) ∧
      (d : Int) - 4*(a : Int) - (c : Int) -
        (7*(y : Int) - 4*(x : Int)) ≤ (8*n+21 : Int) := by
  omega

/-- Even far-left branch: the left-ray gap tracks x-13*y. -/
theorem evenFarLeftGap (x y a d n c : Nat)
    (hxy : y + 3 ≤ x)
    (hc : c = 5 ∨ c = 9)
    (hfirstLower : x - y - 2 ≤ a + n + 1)
    (hfirstUpper : a ≤ x - y - 2 + n)
    (hthirdLower : 3*y + 8 ≤ d)
    (hthirdUpper : d ≤ 3*y + 10 + 4*n) :
    -(17*n+52 : Int) ≤
      (a : Int) - 4*(d : Int) - (c : Int) -
        ((x : Int) - 13*(y : Int)) ∧
      (a : Int) - 4*(d : Int) - (c : Int) -
        ((x : Int) - 13*(y : Int)) ≤ (17*n+52 : Int) := by
  omega

/-- Odd near-left branch: the right-ray gap tracks 7*x-4*y. -/
theorem oddNearRightGap (x y a d n c : Nat)
    (_hpos : 0 < x)
    (hxy : x ≤ y + 4)
    (hc : c = 1 ∨ c = 2)
    (hfirstLower : y + 4 - x ≤ a + n + 1)
    (hfirstUpper : a ≤ y + 4 - x + n)
    (hthirdLower : 3*x ≤ d)
    (hthirdUpper : d ≤ 3*x + 4*n + 2) :
    -(8*n+18 : Int) ≤
      (d : Int) - 4*(a : Int) - (c : Int) -
        (7*(x : Int) - 4*(y : Int)) ∧
      (d : Int) - 4*(a : Int) - (c : Int) -
        (7*(x : Int) - 4*(y : Int)) ≤ (8*n+18 : Int) := by
  omega

/-- Odd near-left branch: the left-ray gap tracks y-13*x. -/
theorem oddNearLeftGap (x y a d n c : Nat)
    (_hpos : 0 < x)
    (hxy : x ≤ y + 4)
    (hc : c = 5 ∨ c = 9)
    (hfirstLower : y + 4 - x ≤ a + n + 1)
    (hfirstUpper : a ≤ y + 4 - x + n)
    (hthirdLower : 3*x ≤ d)
    (hthirdUpper : d ≤ 3*x + 4*n + 2) :
    -(17*n+14 : Int) ≤
      (a : Int) - 4*(d : Int) - (c : Int) -
        ((y : Int) - 13*(x : Int)) ∧
      (a : Int) - 4*(d : Int) - (c : Int) -
        ((y : Int) - 13*(x : Int)) ≤ (17*n+14 : Int) := by
  omega

/-- Even near-left branch: the right-ray gap tracks 7*x-4*y. -/
theorem evenNearRightGap (x y p q r a d n c : Nat)
    (_hpos : 0 < x)
    (hxy : x ≤ y)
    (hc : c = 1 ∨ c = 2)
    (hevalFirstLower : y + 1 - x ≤ p + n + 1)
    (hevalFirstUpper : p ≤ y + 2 - x)
    (hevalThirdLower : 3*x + 5 ≤ r + 3*q + 2)
    (hevalThirdUpper : r + 3*q ≤ 3*x + 2*n + 7)
    (hdrainFirstLower : p ≤ a + n + 1)
    (hdrainFirstUpper : a ≤ p + n)
    (hdrainThirdLower : r + 3*q ≤ d)
    (hdrainThirdUpper : d ≤ r + 3*q + 4*n + 2) :
    -(14*n+12 : Int) ≤
      (d : Int) - 4*(a : Int) - (c : Int) -
        (7*(x : Int) - 4*(y : Int)) ∧
      (d : Int) - 4*(a : Int) - (c : Int) -
        (7*(x : Int) - 4*(y : Int)) ≤ (14*n+12 : Int) := by
  omega

/-- Even near-left branch: the left-ray gap tracks y-13*x. -/
theorem evenNearLeftGap (x y p q r a d n c : Nat)
    (_hpos : 0 < x)
    (hxy : x ≤ y)
    (hc : c = 5 ∨ c = 9)
    (hevalFirstLower : y + 1 - x ≤ p + n + 1)
    (hevalFirstUpper : p ≤ y + 2 - x)
    (hevalThirdLower : 3*x + 5 ≤ r + 3*q + 2)
    (hevalThirdUpper : r + 3*q ≤ 3*x + 2*n + 7)
    (hdrainFirstLower : p ≤ a + n + 1)
    (hdrainFirstUpper : a ≤ p + n)
    (hdrainThirdLower : r + 3*q ≤ d)
    (hdrainThirdUpper : d ≤ r + 3*q + 4*n + 2) :
    -(26*n+46 : Int) ≤
      (a : Int) - 4*(d : Int) - (c : Int) -
        ((y : Int) - 13*(x : Int)) ∧
      (a : Int) - 4*(d : Int) - (c : Int) -
        ((y : Int) - 13*(x : Int)) ≤ (26*n+46 : Int) := by
  omega

#print axioms oddFarRightGap
#print axioms oddFarLeftGap
#print axioms evenFarRightGap
#print axioms evenFarLeftGap
#print axioms oddNearRightGap
#print axioms oddNearLeftGap
#print axioms evenNearRightGap
#print axioms evenNearLeftGap

end BB6.Agent49RootRayBridgeArithmetic
