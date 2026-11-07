import Std

namespace BB6.Agent49TerminalRatio4Arithmetic

def gapR (a d cR : Nat) : Int :=
  (d : Int) - 4*(a : Int) - (cR : Int)

def gapL (a d cL : Nat) : Int :=
  (a : Int) - 4*(d : Int) - (cL : Int)

/-- Subtracting the two far-left bridge gaps eliminates the output counters. -/
theorem far_ratio4_gap_bound
    (x y aa dd cR cL K eR eL : Nat)
    (hbalR : dd ≤ aa+K+4)
    (hbalL : aa ≤ dd+K+4)
    (hcR : cR=1 ∨ cR=2)
    (hcL : cL=5 ∨ cL=9)
    (hRlo : -(eR : Int) ≤ gapR aa dd cR - (7*(y : Int)-4*(x : Int)))
    (hRhi : gapR aa dd cR - (7*(y : Int)-4*(x : Int)) ≤ eR)
    (hLlo : -(eL : Int) ≤ gapL aa dd cL - ((x : Int)-13*(y : Int)))
    (hLhi : gapL aa dd cL - ((x : Int)-13*(y : Int)) ≤ eL) :
    -(5*K+eR+eL+28 : Int) ≤ 5*(4*(y : Int)-(x : Int)) ∧
      5*(4*(y : Int)-(x : Int)) ≤ 5*K+eR+eL+28 := by
  simp [gapR, gapL] at hRlo hRhi hLlo hLhi
  omega

/-- The near-left analogue, with predecessor form 4*x-y. -/
theorem near_ratio4_gap_bound
    (x y aa dd cR cL K eR eL : Nat)
    (hbalR : dd ≤ aa+K+4)
    (hbalL : aa ≤ dd+K+4)
    (hcR : cR=1 ∨ cR=2)
    (hcL : cL=5 ∨ cL=9)
    (hRlo : -(eR : Int) ≤ gapR aa dd cR - (7*(x : Int)-4*(y : Int)))
    (hRhi : gapR aa dd cR - (7*(x : Int)-4*(y : Int)) ≤ eR)
    (hLlo : -(eL : Int) ≤ gapL aa dd cL - ((y : Int)-13*(x : Int)))
    (hLhi : gapL aa dd cL - ((y : Int)-13*(x : Int)) ≤ eL) :
    -(5*K+eR+eL+28 : Int) ≤ 5*(4*(x : Int)-(y : Int)) ∧
      5*(4*(x : Int)-(y : Int)) ≤ 5*K+eR+eL+28 := by
  simp [gapR, gapL] at hRlo hRhi hLlo hLhi
  omega

#print axioms far_ratio4_gap_bound
#print axioms near_ratio4_gap_bound

end BB6.Agent49TerminalRatio4Arithmetic
