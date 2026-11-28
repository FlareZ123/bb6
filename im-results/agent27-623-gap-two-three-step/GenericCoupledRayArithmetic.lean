import Mathlib.Tactic

/-!
# Generic signed-affine ray transport over the naturals

For *any* weighted two-counter transition with one shared drain-depth r,
this lemma pulls an arbitrary rational successor strip P*x ≈ Q*y
backwards to its unique linearized projective preimage
P*L ≈ (P+3Q)*m, retaining the sharp one-sided width parameters.

This is a purely algebraic theorem: no Turing-machine predicates,
simulator traces, native_decide, or #623-specific premises are needed.
Its hypotheses are precisely those established for each successful
budgeted ordinary #623 drain in FourRayCoupledSource. Once source
accepted, the P,Q lemma can be reused for arbitrary inverse depths.
-/

namespace BB6.Agent27GenericCoupledRayArithmetic

/-- Rational-ray transport with a common weighted recurrence depth. -/
theorem coupled_ray_transport
    (P Q m L x y N r c A B : Nat)
    (hr : r≤N)
    (hcLo : 4≤c) (hcHi : c≤8)
    (hfirstUpper : x+m≤L+r+4)
    (hfirstLower : L≤x+m+N+6)
    (hweighted : 2*x+y=2*L+m+c+2*r)
    (hrayUpper : P*x≤Q*y+A)
    (hrayLower : Q*y≤P*x+B) :
    P*L≤(P+3*Q)*m+A+(P+4*Q)*N+6*P+20*Q ∧
    (P+3*Q)*m≤P*L+B+P*N+4*P+4*Q := by
  have hweightedQ :
      2*(Q*x)+Q*y=2*(Q*L)+Q*m+Q*c+2*(Q*r) := by
    calc
      2*(Q*x)+Q*y=Q*(2*x+y) := by ring
      _ = Q*(2*L+m+c+2*r) :=
        congrArg (fun k : Nat => Q*k) hweighted
      _ = 2*(Q*L)+Q*m+Q*c+2*(Q*r) := by ring
  have hscaledLower :=
    Nat.mul_le_mul_left (P+2*Q) hfirstLower
  have hscaledUpper :=
    Nat.mul_le_mul_left (P+2*Q) hfirstUpper
  have hupperStep :
      P*L+Q*y≤(P+3*Q)*m+P*x+(P+2*Q)*(N+6)+Q*c+2*Q*r := by
    nlinarith only [hweightedQ,hscaledLower]
  have hlowerStep :
      (P+3*Q)*m+P*x+Q*c+2*Q*r≤
      P*L+Q*y+(P+2*Q)*(r+4) := by
    nlinarith only [hweightedQ,hscaledUpper]
  have hrQ := Nat.mul_le_mul_left Q hr
  have hrP := Nat.mul_le_mul_left P hr
  have hcUp := Nat.mul_le_mul_left Q hcHi
  have hcDown := Nat.mul_le_mul_left Q hcLo
  constructor
  · nlinarith only [hupperStep,hrayUpper,hrQ,hcUp]
  · nlinarith only [hlowerStep,hrayLower,hrP,hcDown]

/-- The two inverse slopes, in projective fraction form, are obtained
by applying the preceding theorem with (P,Q) and (Q,P).
The four-ray #623 result specializes to successor slopes 13/1 and 7/4.
-/
theorem pair_of_inverse_rays
    (P Q m L x y N r c A B : Nat)
    (hr : r≤N)
    (hcLo : 4≤c) (hcHi : c≤8)
    (hfirstUpper : x+m≤L+r+4)
    (hfirstLower : L≤x+m+N+6)
    (hweighted : 2*x+y=2*L+m+c+2*r)
    (hpair : (P*x≤Q*y+A ∧ Q*y≤P*x+B) ∨
      (Q*x≤P*y+A ∧ P*y≤Q*x+B)) :
    (P*L≤(P+3*Q)*m+A+(P+4*Q)*N+6*P+20*Q ∧
      (P+3*Q)*m≤P*L+B+P*N+4*P+4*Q) ∨
    (Q*L≤(Q+3*P)*m+A+(Q+4*P)*N+6*Q+20*P ∧
      (Q+3*P)*m≤Q*L+B+Q*N+4*Q+4*P) := by
  rcases hpair with h | h
  · exact Or.inl (coupled_ray_transport P Q m L x y N r c A B
      hr hcLo hcHi hfirstUpper hfirstLower hweighted h.1 h.2)
  · exact Or.inr (coupled_ray_transport Q P m L x y N r c A B
      hr hcLo hcHi hfirstUpper hfirstLower hweighted h.1 h.2)

#print axioms coupled_ray_transport
#print axioms pair_of_inverse_rays

end BB6.Agent27GenericCoupledRayArithmetic
