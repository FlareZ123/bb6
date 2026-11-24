import Q0DoubleBarrier

namespace BB429Q0Macro.RankBarrier
open BB429Q0Macro
set_option maxHeartbeats 8000000

/-- The low digit contribution to b*D(w)+E(w), with l the remaining
    total cost INCLUDING the current digit. -/
def lowCoeff (b l : Nat) (r : Digit) : Int :=
  (b:Int)*digit r+offset r-(digit r:Int)*l

def poly (b : Nat) (w : List Digit) : Int := b*D w+E w

theorem poly_cons (b : Nat) (r : Digit) (w : List Digit) :
    poly b (r::w) = lowCoeff b (L (r::w)) r + 16*poly b w := by
  simp only [poly,D,E,lowCoeff]
  grind

def coneCarry (a b e : Nat) (l : Nat) (c1 c2 : Int) (w : List Digit) : Prop :=
  l=L w ∧ c1+poly b w<M w*e ∧ c2-3*poly b w<M w*((a:Int)-3*e)

theorem initial_coneCarry (a b e : Nat) (w : List Digit) :
    cone a b e w ↔ coneCarry a b e (L w) 0 ((L w:Int)-b) w := by
  simp only [cone,coneCarry,poly,true_and]
  constructor <;> intro h <;> obtain ⟨h1,h2⟩ := h <;> constructor <;> grind

theorem floor_shift (c x t : Int) : (c+16*x<16*t) ↔ (c/16+x<t) := by
  have h := Int.ediv_lt_iff_lt_mul (a:=c) (b:=t-x) (c:=16) (by decide)
  omega

theorem coneCarry_cons (a b e l : Nat) (c1 c2 : Int) (r : Digit) (w : List Digit) :
    coneCarry a b e l c1 c2 (r::w) ↔
      cost r≤l ∧ coneCarry a b e (l-cost r) ((c1+lowCoeff b l r)/16)
        ((c2-3*lowCoeff b l r)/16) w := by
  have hm : M (r::w)=16*M w := by simp [M,Int.pow_succ,Int.mul_comm]
  constructor
  · rintro ⟨hl,h1,h2⟩
    have hl' : l-cost r=L w := by simp [L] at hl; omega
    refine ⟨by simp [L] at hl; omega,hl',?_,?_⟩
    · rw [poly_cons,←hl,hm] at h1
      apply (floor_shift (c1+lowCoeff b l r) (poly b w) (M w*e)).mp
      grind
    · rw [poly_cons,←hl,hm] at h2
      have h := (floor_shift (c2-3*lowCoeff b l r) (-3*poly b w) (M w*((a:Int)-3*e))).mp (by grind)
      grind
  · rintro ⟨hc,hl,h1,h2⟩
    have hl' : l=L (r::w) := by simp [L]; omega
    refine ⟨hl',?_,?_⟩
    · have h := (floor_shift (c1+lowCoeff b l r) (poly b w) (M w*e)).mpr h1
      rw [poly_cons,←hl',hm]
      grind
    · have h := (floor_shift (c2-3*lowCoeff b l r) (-3*poly b w) (M w*((a:Int)-3*e))).mpr (by omega)
      rw [poly_cons,←hl',hm]
      grind

theorem coneCarry_nil (a b e l : Nat) (c1 c2 : Int) :
    coneCarry a b e l c1 c2 [] ↔ l=0 ∧ c1<e ∧ c2<(a:Int)-3*e := by
  simp [coneCarry,poly,L,D,E,M]

#print axioms initial_coneCarry
#print axioms coneCarry_cons
#print axioms coneCarry_nil
end BB429Q0Macro.RankBarrier
