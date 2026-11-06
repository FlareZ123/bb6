import Agent8ExplicitConeSource

/-!
Closed-form geometric cone thresholds for the unchanged source #623.
Every assertion is uniformly quantified over all finite accelerated depths.
The final "finite-horizon corridor" is a necessary condition for a section
to halt within a prescribed finite number of returns. This does not yield
a uniform threshold for any fixed blank-root orbit.
-/
namespace BB6.Agent8ConeClosedFormsSource

open BusyBeaver.M_1RB0LE_0RC1RC_0RD1LA_1LD0LA_1LF1LC_HHH0LA
open BB6.Agent8ExplicitConeSource
open BB6.Agent8RightTailAllDepthSource

/-- The exact slope of the source-certified left safe cone grows
geometrically with factor seven. -/
theorem slope_pow (n : Nat) : 3*coneSlope n+1=7^n := by
  induction n with
  | zero => decide
  | succ n ih =>
      simp only [coneSlope, Nat.pow_succ]
      omega

/-- Closed-form offset, including the linear n correction. -/
theorem offset_pow (n : Nat) :
    9*coneOffset n+6*n+13=13*7^n := by
  induction n with
  | zero => decide
  | succ n ih =>
      have hs := slope_pow n
      simp only [coneOffset, Nat.pow_succ]
      omega

theorem slope_bound (n : Nat) : coneSlope n ≤ 7^n := by
  have h := slope_pow n
  omega

theorem offset_bound (n : Nat) : coneOffset n ≤ 2*7^n := by
  have h := offset_pow n
  omega

theorem leftSimpleCone (n a d : Nat)
    (h : 7^n*(d+2)≤a) :
    coneSlope n*d+coneOffset n≤a := by
  have hs := slope_bound n
  have hb := offset_bound n
  have hmul := Nat.mul_le_mul_right d hs
  have hc : 7^n*d+7^n*2≤a := by simpa only [Nat.mul_add] using h
  omega

theorem rightSlopeBound (n : Nat) :
    7*coneSlope n+2 ≤ 7^(n+1) := by
  have h := slope_pow n
  rw [Nat.pow_succ]
  omega

theorem rightOffsetBound (n : Nat) :
    7*coneSlope n+coneOffset n+2 ≤ 2*7^(n+1) := by
  have h1 := slope_bound n
  have h2 := offset_bound n
  have hpos : 1 ≤ 7^n := by
    have hp : 0 < 7^n := Nat.pow_pos (by decide)
    omega
  rw [Nat.pow_succ]
  omega

theorem rightSimpleCone (n a d : Nat)
    (h : 7^(n+1)*(a+2)≤d) :
    (7*coneSlope n+2)*a+
      (7*coneSlope n+coneOffset n+2)≤d := by
  have hs := rightSlopeBound n
  have hb := rightOffsetBound n
  have hmul := Nat.mul_le_mul_right a hs
  have hc : 7^(n+1)*a+7^(n+1)*2≤d := by
    simpa only [Nat.mul_add] using h
  omega

/-- The simple explicit left safe cone, valid for every finite horizon. -/
theorem simpleLeftAllDepth (n a d : Nat)
    (h : 7^n*(d+2)≤a) :
    Continues n (.D a d) :=
  leftExplicitAllDepth n a d (leftSimpleCone n a d h)

/-- The symmetric simple right cone is safe whenever the first counter is
positive and even. -/
theorem simpleRightAllDepth (n a d : Nat)
    (ha : 0<a) (he : a%2=0)
    (h : 7^(n+1)*(a+2)≤d) :
    Continues (n+1) (.D a d) :=
  rightExplicitAllDepth n a d ha he (rightSimpleCone n a d h)

/-- A finite-horizon failure on an even-first-counter section must lie
inside an explicit depth-dependent diagonal corridor, unless a=0. -/
theorem finiteHorizonNecessaryCorridor (n a d : Nat)
    (he : a%2=0)
    (hshort : ¬Continues (n+1) (.D a d)) :
    a<7^(n+1)*(d+2) ∧
    (a=0 ∨ d<7^(n+1)*(a+2)) := by
  constructor
  · by_contra hnot
    have hs : 7^(n+1)*(d+2)≤a := by omega
    exact hshort (simpleLeftAllDepth (n+1) a d hs)
  · by_cases ha : a=0
    · exact Or.inl ha
    · right
      by_contra hnot
      have hs : 7^(n+1)*(a+2)≤d := by omega
      exact hshort (simpleRightAllDepth n a d (by omega) he hs)

#print axioms slope_pow
#print axioms offset_pow
#print axioms simpleLeftAllDepth
#print axioms simpleRightAllDepth
#print axioms finiteHorizonNecessaryCorridor

end BB6.Agent8ConeClosedFormsSource
