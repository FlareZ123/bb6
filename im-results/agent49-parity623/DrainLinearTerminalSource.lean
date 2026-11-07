import Agent49DrainLinearLogSource
import Agent8TerminalIntervalSource

/-!
DRAFT: sharper terminal-parent interval obtained by combining the
linear-logarithmic B-drain upper bound and the logarithmic first-counter
loss bound with the existing source one-step terminal gate.

The interval arithmetic has compiled locally with Lean 4.36.0-rc2 against the
exact recursion model and abstract one-step gate inequalities. Full pinned
source-import compilation remains pending.
-/

namespace BB6.Agent49DrainLinearTerminalSource
open BusyBeaver.M_1RB0LE_0RC1RC_0RD1LA_1LD0LA_1LF1LC_HHH0LA
open BB6.Agent8DrainFirstSharpSource
open BB6.Agent8DrainSevenSource
open BB6.Agent8BudgetSource
open BB6.Agent49DrainLinearLogSource
open BB6.Agent8DrainQuadraticLogSource

/-- A successful drain that is followed by a halting daughter must have
its input first counter within a logarithmic-width interval around d+3b. -/
theorem drainB_terminal_interval_linear (a b d n aa dd : Nat)
    (hs : drainB a b d = some (.D aa dd))
    (hb : b<3^n)
    (he : aa%2=0)
    (hhalt : highLevelNext (.D aa dd) = none) :
    3^((d+3*b)-(a+n)-5) ≤ 2*(a+d+3*b+5*n+2)+5 ∧
    3^(a-d-3*b-5*n-8) ≤ 2*(a+d+3*b+5*n+2)+5 := by
  have hf := drainB_first_upper_log n a b d aa dd hb hs
  have hl := drainB_first_lower_log n a b d aa dd hb hs
  have hd := drainB_d3 b a d aa dd hs
  have hu := drainB_upper_linear_log n a b d aa dd hb hs
  have hg := BB6.Agent49ParitySource.next_none_requires_pow_gap aa dd he hhalt
  have hm : aa+dd ≤ a+d+3*b+5*n+2 := by omega
  constructor
  · have hr : (d+3*b)-(a+n)-5 ≤ dd-aa-5 := by omega
    have hp := Nat.pow_le_pow_right (by omega : 0<3) hr
    omega
  · have hr : (a-d-3*b-5*n-8) ≤ aa-dd-5 := by omega
    have hp := Nat.pow_le_pow_right (by omega : 0<3) hr
    omega

/-- If K dominates the terminal mass by 3^K, a terminal daughter
forces the final drain input balance into the following sharp interval. -/
theorem drainB_terminal_balance_interval (a b d n K aa dd : Nat)
    (hs : drainB a b d = some (.D aa dd))
    (hb : b<3^n)
    (he : aa%2=0)
    (hhalt : highLevelNext (.D aa dd) = none)
    (hK : 2*(a+d+3*b+5*n+2)+5 < 3^K) :
    d+3*b ≤ a+n+K+4 ∧ a ≤ d+3*b+5*n+K+7 := by
  have hi := drainB_terminal_interval_linear a b d n aa dd hs hb he hhalt
  constructor
  · by_cases h : d+3*b ≤ a+n+K+4
    · exact h
    · have hexp : K ≤ (d+3*b)-(a+n)-5 := by omega
      have hp := Nat.pow_le_pow_right (by omega : 0<3) hexp
      omega
  · by_cases h : a ≤ d+3*b+5*n+K+7
    · exact h
    · have hexp : K ≤ a-d-3*b-5*n-8 := by omega
      have hp := Nat.pow_le_pow_right (by omega : 0<3) hexp
      omega

#print axioms drainB_terminal_interval_linear
/-- Even-right first-evaluator plus final-drain terminality confines
the original right-ray balance d-4*a to a logarithmic interval. -/
theorem evenRight_terminal_balance_interval
    (a d n0 n K x b y aa dd : Nat)
    (hRight : a≤d)
    (ha : a<3^n0)
    (hbpos : 0<b)
    (hEval : evalA (d+1-a) a (2*a+5) = some (x,b,y))
    (hDrain : drainB x b y = some (.D aa dd))
    (hb : b<3^n)
    (he : aa%2=0)
    (hhalt : highLevelNext (.D aa dd) = none)
    (hK : 2*(x+y+3*b+5*n+2)+5 < 3^K) :
    4*a≤d+n+K+3 ∧ d≤4*a+5*n+K+11+3*n0 := by
  obtain ⟨r,s,hrs,hrpos,hbs,hfirst,hpot⟩ :=
    evalA_positive_depth n0 (d+1-a) a (2*a+5) x b y ha hbpos hEval
  have hfirstUpper :=
    evalA_first_upper_one (d+1-a) a (2*a+5) x b y hEval
  have hthirdLower :=
    evalA_third_lower (d+1-a) a (2*a+5) x b y hEval
  have hbal :=
    drainB_terminal_balance_interval x b y n K aa dd hDrain hb he hhalt hK
  omega

#print axioms drainB_terminal_balance_interval
#print axioms evenRight_terminal_balance_interval
/-- A terminal state on the even-right branch with zero residual blocks
is confined by the direct evaluator bounds. -/
theorem terminal_gap_bound (x y K M : Nat)
    (hEven : x%2=0)
    (hhalt : highLevelNext (.D x y) = none)
    (hmass : x+y≤M)
    (hK : 2*M+5<3^K) :
    x≤y+K+4 ∧ y≤x+K+4 := by
  have hg :=
    BB6.Agent49ParitySource.next_none_requires_pow_gap x y hEven hhalt
  rcases hg with ⟨hgap1,hgap2⟩
  constructor
  · by_cases h : x≤y+K+4
    · exact h
    · have hexp : K≤x-y-5 := by omega
      have hp := Nat.pow_le_pow_right (by omega : 0<3) hexp
      omega
  · by_cases h : y≤x+K+4
    · exact h
    · have hexp : K≤y-x-5 := by omega
      have hp := Nat.pow_le_pow_right (by omega : 0<3) hexp
      omega

/-- The even-right b=0 case also confines d-4*a to logarithmic width. -/
theorem evenRight_zero_block_terminal_interval
    (a d n0 K x y : Nat)
    (hRight : a≤d)
    (ha : a<3^n0)
    (hEval : evalA (d+1-a) a (2*a+5) = some (x,0,y))
    (hEven : x%2=0)
    (hhalt : highLevelNext (.D x y) = none)
    (hK : 2*(d+2*a+9+2*n0)+5 < 3^K) :
    4*a≤d+K+3 ∧ d≤4*a+K+11+3*n0 := by
  have hfirstUpper :=
    evalA_first_upper_one (d+1-a) a (2*a+5) x 0 y hEval
  have hfirstLower :=
    evalA_first_lower_log n0 (d+1-a) a (2*a+5) x 0 y ha hEval
  have hthirdLower :=
    evalA_third_lower (d+1-a) a (2*a+5) x 0 y hEval
  have hthirdUpper :=
    evalA_upper_log n0 (d+1-a) a (2*a+5) x 0 y ha hEval
  have hmass : x+y≤d+2*a+9+2*n0 := by omega
  have hgap :=
    terminal_gap_bound x y K (d+2*a+9+2*n0) hEven hhalt hmass hK
  omega

#print axioms terminal_gap_bound
#print axioms evenRight_zero_block_terminal_interval

/-- Odd-left ray: a=2*d+9+t, so its drain balance is t-2*d-10. -/
theorem oddLeft_terminal_ray_interval
    (d t n K aa dd : Nat)
    (hs : drainB (d+t+4) (d+3) 5 = some (.D aa dd))
    (hb : d+3<3^n)
    (he : aa%2=0)
    (hhalt : highLevelNext (.D aa dd) = none)
    (hK : 2*(4*d+t+20+5*n)+5 < 3^K) :
    2*d+6≤t+n+K ∧ t≤2*d+5*n+K+17 := by
  have hK' :
      2*((d+t+4)+5+3*(d+3)+5*n+2)+5 < 3^K := by omega
  have hbal :=
    drainB_terminal_balance_interval (d+t+4) (d+3) 5 n K aa dd
      hs hb he hhalt hK'
  omega

/-- Even-left ray: a=2*d+5+t, so its drain balance is t-2*d-5. -/
theorem evenLeft_terminal_ray_interval
    (d t n K aa dd : Nat)
    (hs : drainB (d+t+3) (d+2) 2 = some (.D aa dd))
    (hb : d+2<3^n)
    (he : aa%2=0)
    (hhalt : highLevelNext (.D aa dd) = none)
    (hK : 2*(4*d+t+13+5*n)+5 < 3^K) :
    2*d+1≤t+n+K ∧ t≤2*d+5*n+K+12 := by
  have hK' :
      2*((d+t+3)+2+3*(d+2)+5*n+2)+5 < 3^K := by omega
  have hbal :=
    drainB_terminal_balance_interval (d+t+3) (d+2) 2 n K aa dd
      hs hb he hhalt hK'
  omega

/-- Odd-right ray: d=2*a+1+2*t, so its drain balance is 2*(t-a)+5. -/
theorem oddRight_terminal_ray_interval
    (a t n K aa dd : Nat)
    (ha : 1≤a)
    (hs : drainB (a+2*t+5) (a-1) 3 = some (.D aa dd))
    (hb : a-1<3^n)
    (he : aa%2=0)
    (hhalt : highLevelNext (.D aa dd) = none)
    (hK : 2*(4*a+2*t+7+5*n)+5 < 3^K) :
    2*a≤2*t+n+K+9 ∧ 2*t≤2*a+5*n+K+2 := by
  have hK' :
      2*((a+2*t+5)+3+3*(a-1)+5*n+2)+5 < 3^K := by omega
  have hbal :=
    drainB_terminal_balance_interval (a+2*t+5) (a-1) 3 n K aa dd
      hs hb he hhalt hK'
  omega


#print axioms oddLeft_terminal_ray_interval
#print axioms evenLeft_terminal_ray_interval
#print axioms oddRight_terminal_ray_interval



/-!
The following four theorems instantiate the arithmetic bridge with the
authentic source evalA/drainB bounds. Both ray directions are retained for
each predecessor branch, yielding all four linear forms on predecessor
coordinates.
-/

/-- Odd far-left predecessor: output deviations track 7*y-4*x and
x-13*y with the source-derived errors. -/
theorem oddFarGap (x y a d n cR cL : Nat)
    (hxy : y + 5 ≤ x)
    (hcR : cR = 1 ∨ cR = 2)
    (hcL : cL = 5 ∨ cL = 9)
    (hDrain : drainB (x-y-5) (y+3) 5 = some (.D a d))
    (hb : y+3 < 3^n) :
    (-(8*n+39 : Int) ≤
        (d : Int) - 4*(a : Int) - (cR : Int) -
          (7*(y : Int) - 4*(x : Int)) ∧
      (d : Int) - 4*(a : Int) - (cR : Int) -
          (7*(y : Int) - 4*(x : Int)) ≤ (8*n+39 : Int)) ∧
    (-(17*n+79 : Int) ≤
        (a : Int) - 4*(d : Int) - (cL : Int) -
          ((x : Int) - 13*(y : Int)) ∧
      (a : Int) - 4*(d : Int) - (cL : Int) -
          ((x : Int) - 13*(y : Int)) ≤ (17*n+79 : Int)) := by
  have hfirstLower := drainB_first_lower_log n (x-y-5) (y+3) 5 a d hb hDrain
  have hfirstUpper := drainB_first_upper_log n (x-y-5) (y+3) 5 a d hb hDrain
  have hthirdLower := drainB_d3 (y+3) (x-y-5) 5 a d hDrain
  have hthirdUpper := drainB_upper_linear_log n (x-y-5) (y+3) 5 a d hb hDrain
  have hthirdLower' : 3*y+14 ≤ d := by omega
  have hthirdUpper' : d ≤ 3*y+16+4*n := by omega
  constructor
  · exact BB6.Agent49RootRayBridgeArithmetic.oddFarRightGap
      x y a d n cR hxy hcR hfirstLower hfirstUpper hthirdLower' hthirdUpper'
  · exact BB6.Agent49RootRayBridgeArithmetic.oddFarLeftGap
      x y a d n cL hxy hcL hfirstLower hfirstUpper hthirdLower' hthirdUpper'

/-- Even far-left predecessor: output deviations track 7*y-4*x and
x-13*y with the source-derived errors. -/
theorem evenFarGap (x y a d n cR cL : Nat)
    (hxy : y + 3 ≤ x)
    (hcR : cR = 1 ∨ cR = 2)
    (hcL : cL = 5 ∨ cL = 9)
    (hDrain : drainB (x-y-2) (y+2) 2 = some (.D a d))
    (hb : y+2 < 3^n) :
    (-(8*n+21 : Int) ≤
        (d : Int) - 4*(a : Int) - (cR : Int) -
          (7*(y : Int) - 4*(x : Int)) ∧
      (d : Int) - 4*(a : Int) - (cR : Int) -
          (7*(y : Int) - 4*(x : Int)) ≤ (8*n+21 : Int)) ∧
    (-(17*n+52 : Int) ≤
        (a : Int) - 4*(d : Int) - (cL : Int) -
          ((x : Int) - 13*(y : Int)) ∧
      (a : Int) - 4*(d : Int) - (cL : Int) -
          ((x : Int) - 13*(y : Int)) ≤ (17*n+52 : Int)) := by
  have hfirstLower := drainB_first_lower_log n (x-y-2) (y+2) 2 a d hb hDrain
  have hfirstUpper := drainB_first_upper_log n (x-y-2) (y+2) 2 a d hb hDrain
  have hthirdLower := drainB_d3 (y+2) (x-y-2) 2 a d hDrain
  have hthirdUpper := drainB_upper_linear_log n (x-y-2) (y+2) 2 a d hb hDrain
  have hthirdLower' : 3*y+8 ≤ d := by omega
  have hthirdUpper' : d ≤ 3*y+10+4*n := by omega
  constructor
  · exact BB6.Agent49RootRayBridgeArithmetic.evenFarRightGap
      x y a d n cR hxy hcR hfirstLower hfirstUpper hthirdLower' hthirdUpper'
  · exact BB6.Agent49RootRayBridgeArithmetic.evenFarLeftGap
      x y a d n cL hxy hcL hfirstLower hfirstUpper hthirdLower' hthirdUpper'

/-- Odd near-left predecessor: output deviations track 7*x-4*y and
y-13*x with the source-derived errors. -/
theorem oddNearGap (x y a d n cR cL : Nat)
    (hpos : 0 < x)
    (hxy : x ≤ y + 4)
    (hcR : cR = 1 ∨ cR = 2)
    (hcL : cL = 5 ∨ cL = 9)
    (hDrain : drainB (y+4-x) (x-1) 3 = some (.D a d))
    (hb : x-1 < 3^n) :
    (-(8*n+18 : Int) ≤
        (d : Int) - 4*(a : Int) - (cR : Int) -
          (7*(x : Int) - 4*(y : Int)) ∧
      (d : Int) - 4*(a : Int) - (cR : Int) -
          (7*(x : Int) - 4*(y : Int)) ≤ (8*n+18 : Int)) ∧
    (-(17*n+14 : Int) ≤
        (a : Int) - 4*(d : Int) - (cL : Int) -
          ((y : Int) - 13*(x : Int)) ∧
      (a : Int) - 4*(d : Int) - (cL : Int) -
          ((y : Int) - 13*(x : Int)) ≤ (17*n+14 : Int)) := by
  have hfirstLower := drainB_first_lower_log n (y+4-x) (x-1) 3 a d hb hDrain
  have hfirstUpper := drainB_first_upper_log n (y+4-x) (x-1) 3 a d hb hDrain
  have hthirdLower := drainB_d3 (x-1) (y+4-x) 3 a d hDrain
  have hthirdUpper := drainB_upper_linear_log n (y+4-x) (x-1) 3 a d hb hDrain
  have hthirdLower' : 3*x ≤ d := by omega
  have hthirdUpper' : d ≤ 3*x+4*n+2 := by omega
  constructor
  · exact BB6.Agent49RootRayBridgeArithmetic.oddNearRightGap
      x y a d n cR hpos hxy hcR hfirstLower hfirstUpper hthirdLower' hthirdUpper'
  · exact BB6.Agent49RootRayBridgeArithmetic.oddNearLeftGap
      x y a d n cL hpos hxy hcL hfirstLower hfirstUpper hthirdLower' hthirdUpper'

/-- Even near-left predecessor: the initial evalA and following B-drain
share one ternary-depth budget. -/
theorem evenNearGap (x y p q r a d n cR cL : Nat)
    (hpos : 0 < x)
    (hxy : x ≤ y)
    (hx : x < 3^n)
    (hcR : cR = 1 ∨ cR = 2)
    (hcL : cL = 5 ∨ cL = 9)
    (hEval : evalA (y+1-x) x (2*x+5) = some (p,q,r))
    (hDrain : drainB p q r = some (.D a d)) :
    (-(14*n+12 : Int) ≤
        (d : Int) - 4*(a : Int) - (cR : Int) -
          (7*(x : Int) - 4*(y : Int)) ∧
      (d : Int) - 4*(a : Int) - (cR : Int) -
          (7*(x : Int) - 4*(y : Int)) ≤ (14*n+12 : Int)) ∧
    (-(26*n+46 : Int) ≤
        (a : Int) - 4*(d : Int) - (cL : Int) -
          ((y : Int) - 13*(x : Int)) ∧
      (a : Int) - 4*(d : Int) - (cL : Int) -
          ((y : Int) - 13*(x : Int)) ≤ (26*n+46 : Int)) := by
  have hq : q < 3^n := by
    by_cases hq0 : q = 0
    · subst q
      exact Nat.pow_pos (by decide : 0 < 3)
    · obtain ⟨r0,s,hrs,hrpos,hqsmall,hfirst,hpot⟩ :=
        evalA_positive_depth n (y+1-x) x (2*x+5) p q r hx (by omega) hEval
      have hsle : s ≤ n := by omega
      have hpow : 3^s ≤ 3^n :=
        Nat.pow_le_pow_right (by decide : 0 < 3) hsle
      exact Nat.lt_of_lt_of_le hqsmall hpow
  have hEvalFirstLower :=
    evalA_first_lower_log n (y+1-x) x (2*x+5) p q r hx hEval
  have hEvalFirstUpper :=
    evalA_first_upper_one (y+1-x) x (2*x+5) p q r hEval
  have hEvalThirdLower :=
    evalA_third_lower (y+1-x) x (2*x+5) p q r hEval
  have hEvalThirdUpper :=
    evalA_upper_log n (y+1-x) x (2*x+5) p q r hx hEval
  have hDrainFirstLower := drainB_first_lower_log n p q r a d hq hDrain
  have hDrainFirstUpper := drainB_first_upper_log n p q r a d hq hDrain
  have hDrainThirdLower := drainB_d3 q p r a d hDrain
  have hDrainThirdUpper := drainB_upper_linear_log n p q r a d hq hDrain
  have hEvalFirstLower' : y+1-x ≤ p+n+1 := by omega
  have hEvalFirstUpper' : p ≤ y+2-x := by omega
  have hEvalThirdLower' : 3*x+5 ≤ r+3*q+2 := by omega
  have hEvalThirdUpper' : r+3*q ≤ 3*x+2*n+7 := by omega
  constructor
  · exact BB6.Agent49RootRayBridgeArithmetic.evenNearRightGap
      x y p q r a d n cR hpos hxy hcR
      hEvalFirstLower' hEvalFirstUpper' hEvalThirdLower' hEvalThirdUpper'
      hDrainFirstLower hDrainFirstUpper hDrainThirdLower hDrainThirdUpper
  · exact BB6.Agent49RootRayBridgeArithmetic.evenNearLeftGap
      x y p q r a d n cL hpos hxy hcL
      hEvalFirstLower' hEvalFirstUpper' hEvalThirdLower' hEvalThirdUpper'
      hDrainFirstLower hDrainFirstUpper hDrainThirdLower hDrainThirdUpper

#print axioms oddFarGap
#print axioms evenFarGap
#print axioms oddNearGap
#print axioms evenNearGap

end BB6.Agent49DrainLinearTerminalSource
