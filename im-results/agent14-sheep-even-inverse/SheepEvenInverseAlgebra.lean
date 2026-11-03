import Std

namespace SheepEvenInverseAlgebra

/-- The exact generic return from an even input with valuation `a` and odd part `v`.
The equation uses only natural addition and multiplication and so does not lose
the special case at small values of `v`. -/
def GenericEdge (x y : Nat) : Prop :=
  ∃ a h v u : Nat,
    1 ≤ a ∧ 5 ≤ v ∧ v % 2 = 1 ∧ u % 2 = 1 ∧
    x = 2^a * v ∧
    2*(1 + 2^h*u) + 1 = (2^(a+1)+1)*v + 2*a ∧
    y = 1 + 3^h*u

/-- The separate odd-part-three exceptional Sheep return. -/
def SpecialEdge (x y : Nat) : Prop :=
  ∃ a h u : Nat,
    1 ≤ a ∧ u % 2 = 1 ∧
    x = 3*2^a ∧
    3*2^a+a+3 = 1 + 2^h*u ∧
    y = 1 + 3^h*u

/-- The actual even-return equations, expressed as a two-branch relation. -/
def Edge (x y : Nat) : Prop := GenericEdge x y ∨ SpecialEdge x y

/-- Complete universal necessary Diophantine relation for a generic parent
of an arbitrary rational-exponential target `d*y=2^n+b`. -/
theorem generic_inverse_equation
    (x y d n b : Nat) (hedge : GenericEdge x y)
    (hy : d*y = 2^n + b) :
    ∃ a h v u : Nat,
      1 ≤ a ∧ 5 ≤ v ∧ v % 2 = 1 ∧ u % 2 = 1 ∧
      x = 2^a*v ∧ y = 1+3^h*u ∧
      (d*3^h)*(2^(a+1)+1)*v + 2*a*(d*3^h) + 2^(h+1)*d =
        2^(n+h+1) + 2^(h+1)*b + 3*(d*3^h) := by
  obtain ⟨a,h,v,u,ha,hv,hodd,hu,hx,hz,hout⟩ := hedge
  refine ⟨a,h,v,u,ha,hv,hodd,hu,hx,hout,?_⟩
  have hstep : 2^(h+1) = 2*2^h := by
    rw [Nat.pow_succ, Nat.mul_comm]
  have hnstep : 2^(n+h+1) = 2^n*2^(h+1) := by
    rw [show n+h+1=n+(h+1) by omega, Nat.pow_add]
  have hpoly :
    (d*3^h)*(2^(a+1)+1)*v + 2*a*(d*3^h) + 2^(h+1)*d =
    (2*(1+2^h*u)+1)*(d*3^h) + 2^(h+1)*d := by
    rw [hz]
    grind
  have hcombine :
    (2*(1+2^h*u)+1)*(d*3^h) + 2^(h+1)*d =
      (d*(1+3^h*u))*2^(h+1) + 3*(d*3^h) := by
    rw [hstep]
    grind
  calc
    (d*3^h)*(2^(a+1)+1)*v + 2*a*(d*3^h) + 2^(h+1)*d
       = (2*(1+2^h*u)+1)*(d*3^h) + 2^(h+1)*d := hpoly
    _ = (d*(1+3^h*u))*2^(h+1) + 3*(d*3^h) := hcombine
    _ = (2^n+b)*2^(h+1) + 3*(d*3^h) := by rw [← hout, hy]
    _ = 2^(n+h+1) + 2^(h+1)*b + 3*(d*3^h) := by
      rw [hnstep, Nat.add_mul]
      ac_rfl

/-- Complete universal necessary equation for an exceptional odd-part-three
parent of a rational-exponential target. -/
theorem special_inverse_equation
    (x y d n b : Nat) (hedge : SpecialEdge x y)
    (hy : d*y = 2^n + b) :
    ∃ a h u : Nat,
      1 ≤ a ∧ u % 2 = 1 ∧
      x = 3*2^a ∧ y = 1+3^h*u ∧
      (d*3^h)*(3*2^a+a+2) + 2^h*d =
        2^(n+h) + 2^h*b := by
  obtain ⟨a,h,u,ha,hu,hx,hz,hout⟩ := hedge
  refine ⟨a,h,u,ha,hu,hx,hout,?_⟩
  have hspecial : 3*2^a+a+2 = 2^h*u := by omega
  calc
    (d*3^h)*(3*2^a+a+2) + 2^h*d = (d*3^h)*(2^h*u) + 2^h*d := by rw [hspecial]
    _ = (d*(1+3^h*u))*2^h := by
      grind
    _ = (2^n+b)*2^h := by rw [← hout, hy]
    _ = 2^(n+h)+2^h*b := by
      rw [Nat.pow_add, Nat.add_mul]
      ac_rfl


/-- The negative-offset form covers all three nodes of the r=138 inverse cone:
`d*y+c=2^n`, including `(d,c)=(15,2)` and `(81,68)`. -/
theorem generic_inverse_negative
    (x y d c n : Nat) (hedge : GenericEdge x y)
    (hy : d*y+c = 2^n) :
    ∃ a h v u : Nat,
      1 ≤ a ∧ 5 ≤ v ∧ v%2=1 ∧ u%2=1 ∧
      x=2^a*v ∧ y=1+3^h*u ∧
      (d*3^h)*(2^(a+1)+1)*v + 2*a*(d*3^h) + 2^(h+1)*d + 2^(h+1)*c =
        2^(n+h+1) + 3*(d*3^h) := by
  obtain ⟨a,h,v,u,ha,hv,hodd,hu,hx,hz,hout⟩ := hedge
  refine ⟨a,h,v,u,ha,hv,hodd,hu,hx,hout,?_⟩
  have hstep : 2^(h+1) = 2*2^h := by
    rw [Nat.pow_succ, Nat.mul_comm]
  have hnstep : 2^(n+h+1) = 2^n*2^(h+1) := by
    rw [show n+h+1=n+(h+1) by omega, Nat.pow_add]
  have hpoly :
    (d*3^h)*(2^(a+1)+1)*v + 2*a*(d*3^h) + 2^(h+1)*d =
    (2*(1+2^h*u)+1)*(d*3^h) + 2^(h+1)*d := by
    rw [hz]
    grind
  have hcombine :
    (2*(1+2^h*u)+1)*(d*3^h) + 2^(h+1)*d =
      (d*(1+3^h*u))*2^(h+1) + 3*(d*3^h) := by
    rw [hstep]
    grind
  calc
    (d*3^h)*(2^(a+1)+1)*v + 2*a*(d*3^h) + 2^(h+1)*d + 2^(h+1)*c
      = (2*(1+2^h*u)+1)*(d*3^h) + 2^(h+1)*d + 2^(h+1)*c := by rw [hpoly]
    _ = (d*(1+3^h*u))*2^(h+1) + 3*(d*3^h) + 2^(h+1)*c := by rw [hcombine]
    _ = (d*y+c)*2^(h+1) + 3*(d*3^h) := by rw [hout]; grind
    _ = 2^n*2^(h+1) + 3*(d*3^h) := by rw [hy]
    _ = 2^(n+h+1) + 3*(d*3^h) := by rw [hnstep]

/-- Exceptional odd-part-three source in negative-offset form. -/
theorem special_inverse_negative
    (x y d c n : Nat) (hedge : SpecialEdge x y)
    (hy : d*y+c=2^n) :
    ∃ a h u : Nat,
      1 ≤ a ∧ u%2=1 ∧
      x=3*2^a ∧ y=1+3^h*u ∧
      (d*3^h)*(3*2^a+a+2) + 2^h*d + 2^h*c =
        2^(n+h) := by
  obtain ⟨a,h,u,ha,hu,hx,hz,hout⟩ := hedge
  refine ⟨a,h,u,ha,hu,hx,hout,?_⟩
  have hspecial : 3*2^a+a+2=2^h*u := by omega
  calc
    (d*3^h)*(3*2^a+a+2) + 2^h*d + 2^h*c
      = (d*3^h)*(2^h*u) + 2^h*d + 2^h*c := by rw [hspecial]
    _ = (d*(1+3^h*u))*2^h + 2^h*c := by grind
    _ = (d*y+c)*2^h := by rw [hout]; grind
    _ = 2^n*2^h := by rw [hy]
    _ = 2^(n+h) := by rw [Nat.pow_add]

/-- Unconditional two-branch certificate, valid for all natural parameters. -/
theorem edge_inverse_negative_cases
    (x y d c n : Nat) (hedge : Edge x y)
    (hy : d*y+c=2^n) :
    (∃ a h v u : Nat,
      1 ≤ a ∧ 5 ≤ v ∧ v%2=1 ∧ u%2=1 ∧
      x=2^a*v ∧ y=1+3^h*u ∧
      (d*3^h)*(2^(a+1)+1)*v + 2*a*(d*3^h) + 2^(h+1)*d + 2^(h+1)*c =
        2^(n+h+1) + 3*(d*3^h)) ∨
    (∃ a h u : Nat,
      1 ≤ a ∧ u%2=1 ∧
      x=3*2^a ∧ y=1+3^h*u ∧
      (d*3^h)*(3*2^a+a+2) + 2^h*d + 2^h*c = 2^(n+h)) := by
  rcases hedge with hg | hs
  · exact Or.inl (generic_inverse_negative x y d c n hg hy)
  · exact Or.inr (special_inverse_negative x y d c n hs hy)

#print axioms edge_inverse_negative_cases

/-- All incoming even edges are covered, including the exceptional branch. -/
theorem edge_inverse_cases
    (x y d n b : Nat) (hedge : Edge x y)
    (hy : d*y=2^n+b) :
    (∃ a h v u : Nat,
      1 ≤ a ∧ 5 ≤ v ∧ v%2=1 ∧ u%2=1 ∧
      x=2^a*v ∧ y=1+3^h*u ∧
      (d*3^h)*(2^(a+1)+1)*v + 2*a*(d*3^h) + 2^(h+1)*d =
        2^(n+h+1) + 2^(h+1)*b + 3*(d*3^h)) ∨
    (∃ a h u : Nat,
      1 ≤ a ∧ u%2=1 ∧
      x=3*2^a ∧ y=1+3^h*u ∧
      (d*3^h)*(3*2^a+a+2) + 2^h*d =
        2^(n+h) + 2^h*b) := by
  rcases hedge with hg | hs
  · exact Or.inl (generic_inverse_equation x y d n b hg hy)
  · exact Or.inr (special_inverse_equation x y d n b hs hy)

#print axioms edge_inverse_cases

end SheepEvenInverseAlgebra
