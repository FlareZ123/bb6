import Lean

namespace BB6.Agent23GapHeight

-- Clock/carry recurrence. b is signed only at the original seed b=-1.
def Edge (C b : Int) (g : Nat) (b' : Int) : Prop :=
  3 ≤ g ∧ (2 : Int)^g * b' = C + b

def Extendable (C b : Int) : Prop := 8 ∣ C + b

-- Eliminate the intermediate quotient. The congruence checks both
-- integrality of the edge and terminal extendability.
theorem eliminate_quotient (C b d M : Int) :
    (∃ b', M*b' = C+b ∧ 8 ∣ C+d+b') ↔
      8*M ∣ C+b+M*(C+d) := by
  constructor
  · rintro ⟨b', h, k, hk⟩
    refine ⟨k, ?_⟩
    grind
  · rintro ⟨k,hk⟩
    refine ⟨8*k-(C+d), ?_, k, ?_⟩ <;> grind

-- Given a parent cylinder C(h)=C+8Uh, b(h)=b+8Sh, and
-- C+b=8a, choosing a gap with 2^g=8V reduces to a single
-- congruence in the free cylinder parameter h.
theorem cylinder_step (C b a U S V d h : Int) (ha : C+b=8*a) :
    (∃ b', (8*V)*b' = (C+8*U*h)+(b+8*S*h) ∧
      8 ∣ C+8*U*h+d+b') ↔
    8*V ∣ a + V*(C+d) + (U+S)*h := by
  rw [eliminate_quotient]
  have he : (C+8*U*h)+(b+8*S*h)+(8*V)*(C+8*U*h+d) =
      8*(a+V*(C+d)+(U+S)*h+ (8*V)*(U*h)) := by grind
  rw [he, Int.mul_dvd_mul_iff_left (by decide : (8:Int) ≠ 0)]
  have hm : 8*V ∣ (8*V)*(U*h) := Int.dvd_mul_right _ _
  constructor
  · intro hd
    have hh := Int.dvd_sub hd hm
    simpa using hh
  · intro hd
    exact Int.dvd_add hd hm

-- Any untrusted modular inverse is checked by the Bezout identity.
theorem linear_residue (A L M I k h : Int) (hinv : L*I=1+M*k) :
    (M ∣ A+L*h) ↔ M ∣ h+I*A := by
  constructor
  · rintro ⟨t,ht⟩
    refine ⟨I*t-k*h, ?_⟩
    grind
  · rintro ⟨t,ht⟩
    refine ⟨L*t-k*A, ?_⟩
    grind

-- The exact affine carry update after substituting h=h0+M*u.
theorem cylinder_child (C b U S M h0 u b' : Int)
    (hb : M*b'=C+b+8*(U+S)*h0) :
    M*(b'+8*(U+S)*u) =
      (C+8*U*(h0+M*u))+(b+8*S*(h0+M*u)) := by grind

def run : Int → Int → List Nat → Option (Int × Int)
  | C,b,[] => if (C+b)%8=0 then some (C,b) else none
  | C,b,g::gs =>
      if 3≤g ∧ (C+b)%((2:Int)^g)=0 then
        run (C+g) ((C+b)/((2:Int)^g)) gs
      else none

def gaps62 : List Nat := [11,8,6,4,5,3,4,8,7,6]

theorem witness62 : run 241147905 (-1) gaps62 = some (241147967,3797497) := by decide
theorem span62 : gaps62.sum = 62 := by decide

set_option maxRecDepth 10000 in
set_option exponentiation.threshold 10000 in
theorem height_counterexample : (241147905:Nat)^20 < 2^(9*62) := by decide

#print axioms eliminate_quotient
#print axioms cylinder_step
#print axioms linear_residue
#print axioms cylinder_child
#print axioms witness62
#print axioms span62
#print axioms height_counterexample

end BB6.Agent23GapHeight
