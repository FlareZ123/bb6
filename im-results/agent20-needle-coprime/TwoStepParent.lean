import Lean
import Lean.Elab.Tactic.Omega

namespace BB6SpaceNeedle

def denominator (v : Nat) : Int := (2 : Int)^(v+1) + 3
def offset (v : Nat) : Int := 3*(2 : Int)^v + (v : Int) + 3
def firstCounter (w q : Nat) : Int := (2 : Int)^w * (2*(q : Int)+3)
def twoStepResidue (w t : Nat) (y : Int) : Int :=
  (2 : Int)^(w+2) * (y+3-(w : Int)-(t : Int)) + 9 - 6*(t : Int)

theorem mulFactors (a b c d : Int) :
    (a*b)*(c*d) = (a*c)*(b*d) := by
  calc
    (a*b)*(c*d) = a*(b*(c*d)) := by rw [Int.mul_assoc]
    _ = a*((b*c)*d) := by rw [← Int.mul_assoc b c d]
    _ = a*((c*b)*d) := by rw [Int.mul_comm b c]
    _ = a*(c*(b*d)) := by rw [Int.mul_assoc c b d]
    _ = (a*c)*(b*d) := by rw [← Int.mul_assoc a c (b*d)]

theorem const_eq (x t : Int) :
  4*x*(3*x+6-t)+9-6*t = (2*x+3)*(6*x-2*t+3) := by
  simp only [Int.mul_sub, Int.mul_add, Int.add_mul]
  have hxxL : 4*x*(3*x) = 12*(x*x) := by
    calc
      4*x*(3*x) = (4*3)*(x*x) := mulFactors 4 x 3 x
      _ = 12*(x*x) := by omega
  have hxxR : 2*x*(6*x) = 12*(x*x) := by
    calc
      2*x*(6*x) = (2*6)*(x*x) := mulFactors 2 x 6 x
      _ = 12*(x*x) := by omega
  have hxtL : 4*x*t = 4*(x*t) := by rw [Int.mul_assoc]
  have hxtR : 2*x*(2*t) = 4*(x*t) := by
    calc
      2*x*(2*t) = (2*2)*(x*t) := mulFactors 2 x 2 t
      _ = 4*(x*t) := by omega
  rw [hxxL, hxxR, hxtL, hxtR]
  omega

theorem hB (t q : Nat) :
    2*(denominator t*(q:Int)+offset t)-2*(t:Int)+3 =
      denominator t*(2*(q:Int)+3) := by
  calc
    2*(denominator t*(q:Int)+offset t)-2*(t:Int)+3
        = 2*denominator t*(q:Int) + (2*offset t-2*(t:Int)+3) := by
            rw [Int.mul_add]
            rw [← Int.mul_assoc]
            omega
    _ = denominator t*(2*(q:Int)) + 3*denominator t := by
          have hmul : 2*denominator t*(q:Int) = denominator t*(2*(q:Int)) := by
            calc
              2*denominator t*(q:Int) = (2*denominator t)*(q:Int) := by rfl
              _ = (denominator t*2)*(q:Int) := by rw [Int.mul_comm 2 (denominator t)]
              _ = denominator t*(2*(q:Int)) := by rw [Int.mul_assoc]
          have hrest : 2*offset t-2*(t:Int)+3 = 3*denominator t := by
            unfold offset denominator
            rw [Int.pow_succ]
            rw [Int.mul_comm ((2:Int)^t) 2]
            omega
          rw [hmul, hrest]
    _ = denominator t*(2*(q:Int)+3) := by
          rw [Int.mul_add]
          rw [Int.mul_comm (denominator t) 3]

theorem hH (w t q : Nat) :
    twoStepResidue w t (denominator w*(q:Int)+offset w) =
      denominator w*(2*firstCounter w q-2*(t:Int)+3) := by
  let x : Int := (2 : Int)^w
  have hxD : denominator w = 2*x+3 := by
    unfold denominator
    dsimp [x]
    rw [Int.pow_succ]
    rw [Int.mul_comm ((2:Int)^w) 2]
  have hxP : (2 : Int)^(w+2) = 4*x := by
    dsimp [x]
    calc
      (2:Int)^(w+2) = (2:Int)^w*(2:Int)^2 := by rw [Int.pow_add]
      _ = (2:Int)^w*4 := by rw [show (2:Int)^2=4 by decide]
      _ = 4*(2:Int)^w := by rw [Int.mul_comm]
  have hq : 4*x*(denominator w*(q:Int)) =
      denominator w*(2*x*(2*(q:Int))) := by
    calc
      4*x*(denominator w*(q:Int)) = (4*x*denominator w)*(q:Int) := by
        rw [← Int.mul_assoc (4*x) (denominator w) (q:Int)]
      _ = (denominator w*(4*x))*(q:Int) := by
        rw [Int.mul_comm (4*x) (denominator w)]
      _ = denominator w*(4*x*(q:Int)) := by rw [Int.mul_assoc]
      _ = denominator w*(2*x*(2*(q:Int))) := by
        congr 1
        calc
          4*x*(q:Int) = (2*2)*(x*(q:Int)) := by ac_rfl
          _ = 2*x*(2*(q:Int)) := by ac_rfl
  have hconst := const_eq x (t:Int)
  unfold twoStepResidue
  rw [hxP]
  have hinner :
      (denominator w*(q:Int)+offset w)+3-(w:Int)-(t:Int) =
      denominator w*(q:Int)+(3*x+6-(t:Int)) := by
    unfold offset
    dsimp [x]
    omega
  rw [hinner]
  rw [Int.mul_add]
  have hright : 2*firstCounter w q = 2*x*(2*(q:Int)+3) := by
    unfold firstCounter
    dsimp [x]
    rw [Int.mul_assoc]
  rw [hright]
  have hrightSplit : 2*x*(2*(q:Int)+3) =
      2*x*(2*(q:Int))+6*x := by
    rw [Int.mul_add]
    have hsix : 2*x*3 = 6*x := by
      calc
        2*x*3 = (2*3)*x := by ac_rfl
        _ = 6*x := by omega
    rw [hsix]
  rw [hrightSplit]
  have hrightGroup : 2*x*(2*(q:Int))+6*x-2*(t:Int)+3 =
      2*x*(2*(q:Int))+(6*x-2*(t:Int)+3) := by omega
  rw [hrightGroup]
  rw [Int.mul_add]
  have hq' : 4*x*(denominator w*(q:Int)) =
      denominator w*(2*x*(2*(q:Int))) := hq
  have hconst' : 4*x*(3*x+6-(t:Int))+9-6*(t:Int) =
      denominator w*(6*x-2*(t:Int)+3) := by
    rw [hxD]
    exact hconst
  rw [hq']
  calc
    denominator w*(2*x*(2*(q:Int))) + 4*x*(3*x+6-(t:Int))+9-6*(t:Int) =
        denominator w*(2*x*(2*(q:Int))) +
          (4*x*(3*x+6-(t:Int))+9-6*(t:Int)) := by omega
    _ = denominator w*(2*x*(2*(q:Int))) +
          denominator w*(6*x-2*(t:Int)+3) := by rw [hconst']

/-- Any two consecutive inverse-parent edges force the quotient-free
congruence modulo the second denominator. -/
theorem two_step_parent_congruence
    (w t y q q' : Nat)
    (hfirst : (y : Int) = denominator w*(q:Int)+offset w)
    (hsecond : firstCounter w q = denominator t*(q':Int)+offset t) :
    denominator t ∣ twoStepResidue w t y := by
  have hB' : (2:Int)*firstCounter w q-2*(t:Int)+3 =
      denominator t*(2*(q':Int)+3) := by
    rw [hsecond]
    exact hB t q'
  have hH' : twoStepResidue w t y =
      denominator w*(2*firstCounter w q-2*(t:Int)+3) := by
    rw [hfirst]
    exact hH w t q
  rw [hH', hB']
  refine ⟨denominator w*(2*(q':Int)+3), ?_⟩
  calc
    denominator w*(denominator t*(2*(q':Int)+3)) =
        (denominator w*denominator t)*(2*(q':Int)+3) := by rw [← Int.mul_assoc]
    _ = (denominator t*denominator w)*(2*(q':Int)+3) := by
        rw [Int.mul_comm (denominator w) (denominator t)]
    _ = denominator t*(denominator w*(2*(q':Int)+3)) := by rw [Int.mul_assoc]

#print axioms two_step_parent_congruence
end BB6SpaceNeedle
