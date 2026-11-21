import Std.Tactic
import SourceDerivedReset

/-!
# Exact affine-to-transducer boundary carry bridge

This file formalizes the quotient identities behind the sourceCarry formulas
in agent48's S-window replay.  It is an arithmetic interface only: the
root-specific hypotheses supplying the affine corrections and the all-time
reset-window induction remain separate obligations.

For K = 3^k, the low residues determine the carry at the k+1 boundary.
The displayed identities show that these are exactly the quotients of the
actual affine output coordinates by 3K, after removing the corresponding
high-coordinate terms.  The source-derived reset wrappers then apply the
already proved 01,00,00 reset to these actual boundary carries.
-/

namespace BB6.Agent48SourceCarryAffineBridge

open BB6.SourceDerivedReset

/-- Euclidean quotient uniqueness for a positive denominator. -/
theorem ediv_eq_of_decomp
    (z d q r : Int) (hd : 0 < d)
    (hr0 : 0 ≤ r) (hrlt : r < d)
    (hdecomp : z = d*q + r) : z / d = q := by
  have hlow : q ≤ z / d := by
    apply (Int.le_ediv_iff_mul_le hd).2
    rw [hdecomp]
    calc
      q*d = d*q := Int.mul_comm q d
      _ ≤ d*q+r := by omega
  have hhigh : z / d < q + 1 := by
    apply Int.ediv_lt_of_lt_mul hd
    rw [hdecomp]
    calc
      d*q + r < d*q + d := by omega
      _ = (q+1)*d := by
        calc
          d*q+d = q*d+d := by rw [Int.mul_comm d q]
          _ = q*d+1*d := by simp
          _ = (q+1)*d := by rw [Int.add_mul]
  omega

/-- Adding an exact multiple of a positive denominator shifts the quotient. -/
theorem ediv_add_mul
    (z d n : Int) (hd : 0 < d) :
    (d*n+z)/d = n + z/d := by
  have hrem0 : 0 ≤ z % d := Int.emod_nonneg z (by omega)
  have hrem1 : z % d < d := Int.emod_lt_of_pos z hd
  have hmul : d*(z/d) + z%d = z := Int.mul_ediv_add_emod z d
  have hdecomp : d*n+z = d*(n+z/d) + z%d := by
    calc
      d*n+z = d*n+(d*(z/d)+z%d) := by rw [hmul]
      _ = (d*n+d*(z/d))+z%d := by omega
      _ = d*(n+z/d)+z%d := by rw [← Int.mul_add]
  exact ediv_eq_of_decomp (d*n+z) d (n+z/d) (z%d) hd hrem0 hrem1 hdecomp

/-- The exact L-branch boundary carry quotients for the affine update
    (x,y) ↦ (x-3y+C, 3y+F). -/
def leftCarryX (K xLow1 yLow C : Int) : Int :=
  (xLow1 - 3*yLow + C) / (3*K)

def leftCarryY (K yLow F : Int) : Int :=
  (3*yLow + F) / (3*K)

/-- The exact R-branch boundary carry quotients for the affine update
    (x,y) ↦ (-4x-3y+C, 3x+3y+F). -/
def rightCarryX (K xLow1 xLow0 yLow C : Int) : Int :=
  (-xLow1 - 3*xLow0 - 3*yLow + C) / (3*K)

def rightCarryY (K xLow0 yLow F : Int) : Int :=
  (3*xLow0 + 3*yLow + F) / (3*K)

/--
The L-branch quotient identity.  The source transducer's initial carries
are precisely the residual quotients after the low x/y digits are removed.
-/
theorem left_affine_boundary_quotients
    (K x y xLow1 xLow0 yLow XHigh1 XHigh0 YHigh0 C F x' y' : Int)
    (hK : 0 < K)
    (hx1 : x = 3*K*XHigh1 + xLow1)
    (_hx0 : x = K*XHigh0 + xLow0)
    (hy0 : y = K*YHigh0 + yLow)
    (hxout : x' = x - 3*y + C)
    (hyout : y' = 3*y + F) :
    x'/(3*K) = XHigh1 - YHigh0 + leftCarryX K xLow1 yLow C ∧
    y'/(3*K) = YHigh0 + leftCarryY K yLow F := by
  have hden : 0 < 3*K := by omega
  constructor
  · rw [hxout, hx1, hy0]
    have hlin :
        3*K*XHigh1 + xLow1 - 3*(K*YHigh0+yLow) + C =
          3*K*(XHigh1-YHigh0) + (xLow1-3*yLow+C) := by
      simp [Int.mul_assoc, Int.mul_add, Int.sub_eq_add_neg,
        Int.add_assoc, Int.add_comm, Int.add_left_comm, Int.neg_add, Int.mul_neg]
    rw [hlin]
    simpa [leftCarryX] using
      ediv_add_mul (xLow1-3*yLow+C) (3*K) (XHigh1-YHigh0) hden
  · rw [hyout, hy0]
    have hlin :
        3*(K*YHigh0+yLow)+F =
          3*K*YHigh0 + (3*yLow+F) := by
      simp [Int.mul_assoc, Int.mul_add, Int.add_assoc, Int.add_comm]
    rw [hlin]
    simpa [leftCarryY] using
      ediv_add_mul (3*yLow+F) (3*K) YHigh0 hden

/--
The R-branch quotient identity.  The two decompositions of x are both
needed because -4x = -x-3x; this is exactly why the sourceCarry formula
contains both x mod 3K and x mod K.
-/
theorem right_affine_boundary_quotients
    (K x y xLow1 xLow0 yLow XHigh1 XHigh0 YHigh0 C F x' y' : Int)
    (hK : 0 < K)
    (hx1 : x = 3*K*XHigh1 + xLow1)
    (hx0 : x = K*XHigh0 + xLow0)
    (hy0 : y = K*YHigh0 + yLow)
    (hxout : x' = -4*x - 3*y + C)
    (hyout : y' = 3*x + 3*y + F) :
    x'/(3*K) =
      -XHigh1-XHigh0-YHigh0 + rightCarryX K xLow1 xLow0 yLow C ∧
    y'/(3*K) =
      XHigh0+YHigh0 + rightCarryY K xLow0 yLow F := by
  have hden : 0 < 3*K := by omega
  constructor
  · rw [hxout]
    have hxsplit : -4*x = -(3*K*XHigh1+xLow1) - 3*(K*XHigh0+xLow0) := by
      have h1 : -x = -(3*K*XHigh1+xLow1) := congrArg (fun t : Int => -t) hx1
      have h2 : -3*x = -3*(K*XHigh0+xLow0) := congrArg (fun t : Int => -3*t) hx0
      omega
    have hysplit : -3*y = -3*(K*YHigh0+yLow) :=
      congrArg (fun t : Int => -3*t) hy0
    have hlin :
        -4*x-3*y+C =
          3*K*(-XHigh1-XHigh0-YHigh0) +
            (-xLow1-3*xLow0-3*yLow+C) := by
      calc
        -4*x-3*y+C = -(3*K*XHigh1+xLow1) -
              3*(K*XHigh0+xLow0) -
              3*(K*YHigh0+yLow)+C := by omega
        _ = 3*K*(-XHigh1-XHigh0-YHigh0) +
              (-xLow1-3*xLow0-3*yLow+C) := by
          simp [Int.mul_assoc, Int.mul_add, Int.sub_eq_add_neg,
            Int.add_assoc, Int.add_comm, Int.add_left_comm, Int.neg_add, Int.mul_neg]
    rw [hlin]
    simpa [rightCarryX] using
      ediv_add_mul (-xLow1-3*xLow0-3*yLow+C) (3*K)
        (-XHigh1-XHigh0-YHigh0) hden
  · rw [hyout, hx0, hy0]
    have hlin :
        3*(K*XHigh0+xLow0)+3*(K*YHigh0+yLow)+F =
          3*K*(XHigh0+YHigh0)+(3*xLow0+3*yLow+F) := by
      simp [Int.mul_assoc, Int.mul_add, Int.add_assoc, Int.add_comm]
    rw [hlin]
    simpa [rightCarryY] using
      ediv_add_mul (3*xLow0+3*yLow+F) (3*K)
        (XHigh0+YHigh0) hden

/-- The actual low residues and a strict correction bound place the L
    boundary carries in the source-derived start rectangle. -/
/-- The L quotient identity specialized to the actual Euclidean low residues. -/
theorem left_actual_affine_boundary_quotients
    (K x y C F x' y' : Int)
    (hK : 0 < K)
    (hxout : x' = x - 3*y + C)
    (hyout : y' = 3*y + F) :
    x'/(3*K) = x/(3*K) - y/K + leftCarryX K (x%(3*K)) (y%K) C ∧
    y'/(3*K) = y/K + leftCarryY K (y%K) F := by
  have hx1 : x = 3*K*(x/(3*K)) + x%(3*K) :=
    (Int.mul_ediv_add_emod x (3*K)).symm
  have hx0 : x = K*(x/K) + x%K :=
    (Int.mul_ediv_add_emod x K).symm
  have hy0 : y = K*(y/K) + y%K :=
    (Int.mul_ediv_add_emod y K).symm
  exact left_affine_boundary_quotients
    K x y (x%(3*K)) (x%K) (y%K) (x/(3*K)) (x/K) (y/K) C F x' y'
    hK hx1 hx0 hy0 hxout hyout

/-- The R quotient identity specialized to the actual Euclidean low residues. -/
theorem right_actual_affine_boundary_quotients
    (K x y C F x' y' : Int)
    (hK : 0 < K)
    (hxout : x' = -4*x - 3*y + C)
    (hyout : y' = 3*x + 3*y + F) :
    x'/(3*K) =
      -(x/(3*K))-x/K-y/K + rightCarryX K (x%(3*K)) (x%K) (y%K) C ∧
    y'/(3*K) = x/K+y/K + rightCarryY K (x%K) (y%K) F := by
  have hx1 : x = 3*K*(x/(3*K)) + x%(3*K) :=
    (Int.mul_ediv_add_emod x (3*K)).symm
  have hx0 : x = K*(x/K) + x%K :=
    (Int.mul_ediv_add_emod x K).symm
  have hy0 : y = K*(y/K) + y%K :=
    (Int.mul_ediv_add_emod y K).symm
  exact right_affine_boundary_quotients
    K x y (x%(3*K)) (x%K) (y%K) (x/(3*K)) (x/K) (y/K) C F x' y'
    hK hx1 hx0 hy0 hxout hyout

/-- The first L transducer output pair is exactly the first ternary digit pair
    of the affine output coordinates. -/
theorem left_actual_affine_first_digit
    (K x y C F x' y' : Int)
    (hK : 0 < K)
    (hxout : x' = x - 3*y + C)
    (hyout : y' = 3*y + F) :
    (x'/(3*K))%3 =
      ((x/(3*K))%3 - (y/K)%3 +
        leftCarryX K (x%(3*K)) (y%K) C)%3 ∧
    (y'/(3*K))%3 =
      ((y/K)%3 + leftCarryY K (y%K) F)%3 := by
  obtain ⟨hx, hy⟩ := left_actual_affine_boundary_quotients
    K x y C F x' y' hK hxout hyout
  have hxdiv : x/(3*K) = 3*((x/(3*K))/3) + (x/(3*K))%3 := by
    have h := Int.mul_ediv_add_emod (x/(3*K)) 3
    omega
  have hydiv : y/K = 3*((y/K)/3) + (y/K)%3 := by
    have h := Int.mul_ediv_add_emod (y/K) 3
    omega
  constructor
  · rw [hx]
    omega
  · rw [hy]
    omega

/-- The first R transducer output pair is exactly the first ternary digit pair
    of the affine output coordinates. -/
theorem right_actual_affine_first_digit
    (K x y C F x' y' : Int)
    (hK : 0 < K)
    (hxout : x' = -4*x - 3*y + C)
    (hyout : y' = 3*x + 3*y + F) :
    (x'/(3*K))%3 =
      (-(x/(3*K))%3 - (x/K)%3 - (y/K)%3 +
        rightCarryX K (x%(3*K)) (x%K) (y%K) C)%3 ∧
    (y'/(3*K))%3 =
      ((x/K)%3 + (y/K)%3 + rightCarryY K (x%K) (y%K) F)%3 := by
  obtain ⟨hx, hy⟩ := right_actual_affine_boundary_quotients
    K x y C F x' y' hK hxout hyout
  have hx1div : x/(3*K) = 3*((x/(3*K))/3) + (x/(3*K))%3 := by
    have h := Int.mul_ediv_add_emod (x/(3*K)) 3
    omega
  have hx0div : x/K = 3*((x/K)/3) + (x/K)%3 := by
    have h := Int.mul_ediv_add_emod (x/K) 3
    omega
  have hy0div : y/K = 3*((y/K)/3) + (y/K)%3 := by
    have h := Int.mul_ediv_add_emod (y/K) 3
    omega
  constructor
  · rw [hx]
    omega
  · rw [hy]
    omega

/-- Nested Euclidean division by K and then 3 agrees with division by 3K. -/
theorem ediv_div_three (x K : Int) (hK : 0 < K) :
    (x/K)/3 = x/(3*K) := by
  let q : Int := x/(3*K)
  have hx : x = 3*K*q + x%(3*K) :=
    (Int.mul_ediv_add_emod x (3*K)).symm
  have hr0 : 0 ≤ x%(3*K) := Int.emod_nonneg x (by omega)
  have hrlt : x%(3*K) < 3*K := Int.emod_lt_of_pos x (by omega)
  have hlow : q ≤ (x/K)/3 := by
    apply (Int.le_ediv_iff_mul_le (by decide : (0:Int)<3)).2
    apply (Int.le_ediv_iff_mul_le hK).2
    have hmul : (q*3)*K = 3*K*q := by
      simp [Int.mul_assoc, Int.mul_comm]
    rw [hmul, hx]
    omega
  have hhigh : (x/K)/3 < q+1 := by
    apply Int.ediv_lt_of_lt_mul (by decide : (0:Int)<3)
    have hxK : x/K < 3*(q+1) := by
      apply Int.ediv_lt_of_lt_mul hK
      rw [hx]
      calc
        3*K*q + x%(3*K) < 3*K*q + 3*K := by omega
        _ = (3*(q+1))*K := by
          simp [Int.mul_assoc, Int.mul_add, Int.mul_comm]
    simpa [Int.mul_comm] using hxK
  change (x/K)/3 = q
  omega

/-- One L transducer step is exactly Euclidean division of the affine
    output tails.  The current input x digit is u and the previous y digit
    is py. -/
theorem left_tail_step
    (X Y u py a b : Int)
    (hu : u = X%3) (hpy : py = Y%3) :
    (X-Y+a)%3 = (u-py+a)%3 ∧
    (Y+b)%3 = (py+b)%3 ∧
    (X-Y+a)/3 = X/3-Y/3+(u-py+a)/3 ∧
    (Y+b)/3 = Y/3+(py+b)/3 := by
  have hX : X = 3*(X/3)+X%3 := (Int.mul_ediv_add_emod X 3).symm
  have hY : Y = 3*(Y/3)+Y%3 := (Int.mul_ediv_add_emod Y 3).symm
  have hlinX : X-Y+a = 3*(X/3-Y/3)+(u-py+a) := by
    rw [hX, hY, ← hu, ← hpy]
    omega
  have hlinY : Y+b = 3*(Y/3)+(py+b) := by
    rw [hY, ← hpy]
    omega
  have hden : (0:Int) < 3 := by decide
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [hX, hY, ← hu, ← hpy]
    omega
  · rw [hY, ← hpy]
    omega
  · rw [hlinX]
    exact ediv_add_mul (u-py+a) 3 (X/3-Y/3) hden
  · rw [hlinY]
    exact ediv_add_mul (py+b) 3 (Y/3) hden

/-- One R transducer step is exactly Euclidean division of the affine
    output tails.  The current x digit is u and (px,py) is the previous pair. -/
theorem right_tail_step
    (X X0 Y0 u px py a b : Int)
    (hu : u = X%3) (hpx : px = X0%3) (hpy : py = Y0%3) :
    (-X-X0-Y0+a)%3 = (-u-px-py+a)%3 ∧
    (X0+Y0+b)%3 = (px+py+b)%3 ∧
    (-X-X0-Y0+a)/3 =
      -(X/3)-(X0/3)-(Y0/3)+(-u-px-py+a)/3 ∧
    (X0+Y0+b)/3 = X0/3+Y0/3+(px+py+b)/3 := by
  have hX : X = 3*(X/3)+X%3 := (Int.mul_ediv_add_emod X 3).symm
  have hX0 : X0 = 3*(X0/3)+X0%3 := (Int.mul_ediv_add_emod X0 3).symm
  have hY0 : Y0 = 3*(Y0/3)+Y0%3 := (Int.mul_ediv_add_emod Y0 3).symm
  have hlinX : -X-X0-Y0+a =
      3*(-(X/3)-(X0/3)-(Y0/3))+(-u-px-py+a) := by omega
  have hlinY : X0+Y0+b =
      3*(X0/3+Y0/3)+(px+py+b) := by omega
  have hden : (0:Int) < 3 := by decide
  refine ⟨?_, ?_, ?_, ?_⟩
  · omega
  · omega
  · rw [hlinX]
    exact ediv_add_mul (-u-px-py+a) 3 (-(X/3)-X0/3-Y0/3) hden
  · rw [hlinY]
    exact ediv_add_mul (px+py+b) 3 (X0/3+Y0/3) hden

theorem left_source_carry_bounds_from_affine_correction
    (K B x y C F : Int)
    (hK : 0 < K) (hBK : B < K)
    (hClo : -B ≤ C) (hChi : C ≤ B)
    (hFlo : -B ≤ F) (hFhi : F ≤ B) :
    -2 ≤ leftCarryX K (x%(3*K)) (y%K) C ∧
      leftCarryX K (x%(3*K)) (y%K) C ≤ 1 ∧
      -1 ≤ leftCarryY K (y%K) F ∧
      leftCarryY K (y%K) F ≤ 1 := by
  unfold leftCarryX leftCarryY
  exact left_source_carry_bounds K B (x%(3*K)) (y%K) C F
    hK hBK hClo hChi hFlo hFhi
    (Int.emod_nonneg x (by omega))
    (Int.emod_lt_of_pos x (by omega))
    (Int.emod_nonneg y (by omega))
    (Int.emod_lt_of_pos y (by omega))

/-- The actual low residues and a strict correction bound place the R
    boundary carries in the source-derived start rectangle. -/
theorem right_source_carry_bounds_from_affine_correction
    (K B x y C F : Int)
    (hK : 0 < K) (hBK : B < K)
    (hClo : -B ≤ C) (hChi : C ≤ B)
    (hFlo : -B ≤ F) (hFhi : F ≤ B) :
    -4 ≤ rightCarryX K (x%(3*K)) (x%K) (y%K) C ∧
      rightCarryX K (x%(3*K)) (x%K) (y%K) C ≤ 0 ∧
      -1 ≤ rightCarryY K (x%K) (y%K) F ∧
      rightCarryY K (x%K) (y%K) F ≤ 2 := by
  unfold rightCarryX rightCarryY
  exact right_source_carry_bounds K B
    (x%(3*K)) (x%K) (y%K) C F
    hK hBK hClo hChi hFlo hFhi
    (Int.emod_nonneg x (by omega))
    (Int.emod_lt_of_pos x (by omega))
    (Int.emod_nonneg x (by omega))
    (Int.emod_lt_of_pos x (by omega))
    (Int.emod_nonneg y (by omega))
    (Int.emod_lt_of_pos y (by omega))

/--
The three-symbol common reset applies to the actual L source boundary carry,
not merely to a free carry variable.  The previous y digit is y/K mod 3.
-/
theorem left_source_reset_from_affine_correction
    (K B x y C F : Int)
    (hK : 0 < K) (hBK : B < K)
    (hClo : -B ≤ C) (hChi : C ≤ B)
    (hFlo : -B ≤ F) (hFhi : F ≤ B) :
    let py := (y/K)%3
    let a := leftCarryX K (x%(3*K)) (y%K) C
    let b := leftCarryY K (y%K) F
    let a1 := (a-py)/3
    let b1 := (py+b)/3
    let a2 := (a1-1)/3
    let b2 := (1+b1)/3
    a2/3 = -1 ∧ b2/3 = 0 ∧
      NonMono ((a-py)%3) ((a1-1)%3) (a2%3) := by
  let py : Int := (y/K)%3
  let a : Int := leftCarryX K (x%(3*K)) (y%K) C
  let b : Int := leftCarryY K (y%K) F
  let a1 : Int := (a-py)/3
  let b1 : Int := (py+b)/3
  let a2 : Int := (a1-1)/3
  let b2 : Int := (1+b1)/3
  have hpy0 : 0 ≤ py := by
    dsimp [py]
    exact Int.emod_nonneg _ (by decide)
  have hpy2 : py ≤ 2 := by
    dsimp [py]
    have h := Int.emod_lt_of_pos (y/K) (by decide : (0:Int) < 3)
    omega
  have hreset :=
    left_source_derived_reset
      K B (x%(3*K)) (y%K) C F py a b a1 b1 a2 b2
      hK hBK hClo hChi hFlo hFhi
      (Int.emod_nonneg x (by omega))
      (Int.emod_lt_of_pos x (by omega))
      (Int.emod_nonneg y (by omega))
      (Int.emod_lt_of_pos y (by omega))
      hpy0 hpy2 rfl rfl rfl rfl rfl rfl
  simpa [py, a, b, a1, b1, a2, b2, leftCarryX, leftCarryY] using hreset

/--
The three-symbol common reset applies to the actual R source boundary carry,
not merely to a free carry variable.  The previous digit pair is
(x/K mod 3, y/K mod 3).
-/
theorem right_source_reset_from_affine_correction
    (K B x y C F : Int)
    (hK : 0 < K) (hBK : B < K)
    (hClo : -B ≤ C) (hChi : C ≤ B)
    (hFlo : -B ≤ F) (hFhi : F ≤ B) :
    let px := (x/K)%3
    let py := (y/K)%3
    let a := rightCarryX K (x%(3*K)) (x%K) (y%K) C
    let b := rightCarryY K (x%K) (y%K) F
    let a1 := (a-px-py)/3
    let b1 := (px+py+b)/3
    let a2 := (a1-1)/3
    let b2 := (1+b1)/3
    a2/3 = -1 ∧ b2/3 = 0 ∧
      NonMono ((a-px-py)%3) ((a1-1)%3) (a2%3) := by
  let px : Int := (x/K)%3
  let py : Int := (y/K)%3
  let a : Int := rightCarryX K (x%(3*K)) (x%K) (y%K) C
  let b : Int := rightCarryY K (x%K) (y%K) F
  let a1 : Int := (a-px-py)/3
  let b1 : Int := (px+py+b)/3
  let a2 : Int := (a1-1)/3
  let b2 : Int := (1+b1)/3
  have hpx0 : 0 ≤ px := by
    dsimp [px]
    exact Int.emod_nonneg _ (by decide)
  have hpx2 : px ≤ 2 := by
    dsimp [px]
    have h := Int.emod_lt_of_pos (x/K) (by decide : (0:Int) < 3)
    omega
  have hpy0 : 0 ≤ py := by
    dsimp [py]
    exact Int.emod_nonneg _ (by decide)
  have hpy2 : py ≤ 2 := by
    dsimp [py]
    have h := Int.emod_lt_of_pos (y/K) (by decide : (0:Int) < 3)
    omega
  have hreset :=
    right_source_derived_reset
      K B (x%(3*K)) (x%K) (y%K) C F px py a b a1 b1 a2 b2
      hK hBK hClo hChi hFlo hFhi
      (Int.emod_nonneg x (by omega))
      (Int.emod_lt_of_pos x (by omega))
      (Int.emod_nonneg x (by omega))
      (Int.emod_lt_of_pos x (by omega))
      (Int.emod_nonneg y (by omega))
      (Int.emod_lt_of_pos y (by omega))
      hpx0 hpx2 hpy0 hpy2 rfl rfl rfl rfl rfl rfl
  simpa [px, py, a, b, a1, b1, a2, b2, rightCarryX, rightCarryY] using hreset

/-- If the authentic L input window begins 01,00,00, the three x digits
    emitted by the source transducer are the actual first three digits of
    the affine output x'.  Thus the source reset's nonmonochromaticity is
    a statement about the genuine next coordinate, not only a free carry. -/
theorem left_reset_word_actual_output_nonmono
    (K B x y C F x' y' : Int)
    (hK : 0 < K) (hBK : B < K)
    (hClo : -B ≤ C) (hChi : C ≤ B)
    (hFlo : -B ≤ F) (hFhi : F ≤ B)
    (hxout : x' = x - 3*y + C)
    (hyout : y' = 3*y + F)
    (hX0 : (x/(3*K))%3 = 0)
    (hY0 : ((y/K)/3)%3 = 1)
    (hX1 : ((x/(3*K)/3)%3) = 0)
    (hY1 : (((y/K)/3)/3)%3 = 0)
    (hX2 : (((x/(3*K)/3)/3)%3) = 0) :
    NonMono ((x'/(3*K))%3)
      (((x'/(3*K))/3)%3)
      ((((x'/(3*K))/3)/3)%3) := by
  let X : Int := x/(3*K)
  let Y : Int := y/K
  let py : Int := Y%3
  let a : Int := leftCarryX K (x%(3*K)) (y%K) C
  let b : Int := leftCarryY K (y%K) F
  let a1 : Int := (a-py)/3
  let b1 : Int := (py+b)/3
  let a2 : Int := (a1-1)/3
  let b2 : Int := (1+b1)/3
  have hU0 : (0:Int) = X%3 := by dsimp [X]; omega
  have hV0 : (1:Int) = (Y/3)%3 := by dsimp [Y]; omega
  have hU1 : (0:Int) = (X/3)%3 := by dsimp [X]; omega
  have hV1 : (0:Int) = ((Y/3)/3)%3 := by dsimp [Y]; omega
  have hU2 : (0:Int) = ((X/3)/3)%3 := by dsimp [X]; omega
  have hquot := left_actual_affine_boundary_quotients K x y C F x' y' hK hxout hyout
  have hq0 : x'/(3*K) = X-Y+a := by
    simpa [X, Y, a, leftCarryX] using hquot.1
  have hstep0 := left_tail_step X Y 0 py a b hU0 rfl
  have hA0 : -py+a = a-py := by omega
  have hA1 : -1+a1 = a1-1 := by omega
  have hq0digit : (x'/(3*K))%3 = (a-py)%3 := by
    rw [hq0]
    simpa [hA0] using hstep0.1
  have hq1 : (x'/(3*K))/3 = X/3-Y/3+a1 := by
    rw [hq0]
    simpa [a1, hA0] using hstep0.2.2.1
  have hstep1 := left_tail_step (X/3) (Y/3) 0 1 a1 b1 hU1 hV0
  have hq1digit : ((x'/(3*K))/3)%3 = (a1-1)%3 := by
    rw [hq1]
    simpa [hA1] using hstep1.1
  have hq2 : ((x'/(3*K))/3)/3 = (X/3)/3-(Y/3)/3+a2 := by
    rw [hq1]
    simpa [a2, hA1] using hstep1.2.2.1
  have hstep2 := left_tail_step (X/3/3) (Y/3/3) 0 0 a2 b2 hU2 hV1
  have hq2digit : (((x'/(3*K))/3)/3)%3 = a2%3 := by
    rw [hq2]
    simpa using hstep2.1
  have hreset : NonMono ((a-py)%3) ((a1-1)%3) (a2%3) := by
    simpa [py, a, b, a1, b1, a2, b2, X, Y, leftCarryX, leftCarryY] using
      (left_source_reset_from_affine_correction K B x y C F
        hK hBK hClo hChi hFlo hFhi).2.2
  rw [hq0digit, hq1digit, hq2digit]
  exact hreset

/-- If the authentic R input window begins 01,00,00, the three x digits
    emitted by the source transducer are the actual first three digits of
    the affine output x'.  The nested-division lemma identifies the shifted
    previous-x digit with the current x tail. -/
theorem right_reset_word_actual_output_nonmono
    (K B x y C F x' y' : Int)
    (hK : 0 < K) (hBK : B < K)
    (hClo : -B ≤ C) (hChi : C ≤ B)
    (hFlo : -B ≤ F) (hFhi : F ≤ B)
    (hxout : x' = -4*x - 3*y + C)
    (hyout : y' = 3*x + 3*y + F)
    (hX0 : (x/(3*K))%3 = 0)
    (hY0 : ((y/K)/3)%3 = 1)
    (hX1 : ((x/(3*K)/3)%3) = 0)
    (hY1 : (((y/K)/3)/3)%3 = 0)
    (hX2 : (((x/(3*K)/3)/3)%3) = 0) :
    NonMono ((x'/(3*K))%3)
      (((x'/(3*K))/3)%3)
      ((((x'/(3*K))/3)/3)%3) := by
  let X : Int := x/(3*K)
  let X0 : Int := x/K
  let Y0 : Int := y/K
  let Y : Int := Y0/3
  let px : Int := X0%3
  let py : Int := Y0%3
  let a : Int := rightCarryX K (x%(3*K)) (x%K) (y%K) C
  let b : Int := rightCarryY K (x%K) (y%K) F
  let a1 : Int := (a-px-py)/3
  let b1 : Int := (px+py+b)/3
  let a2 : Int := (a1-1)/3
  let b2 : Int := (1+b1)/3
  have hcompat : X0/3 = X := by
    dsimp [X0, X]
    exact ediv_div_three x K hK
  have hU0 : (0:Int) = X%3 := by dsimp [X]; omega
  have hV0 : (1:Int) = Y%3 := by dsimp [Y, Y0]; omega
  have hU1 : (0:Int) = (X/3)%3 := by dsimp [X]; omega
  have hV1 : (0:Int) = (Y/3)%3 := by dsimp [Y, Y0]; omega
  have hU2 : (0:Int) = ((X/3)/3)%3 := by dsimp [X]; omega
  have hquot := right_actual_affine_boundary_quotients K x y C F x' y' hK hxout hyout
  have hq0 : x'/(3*K) = -X-X0-Y0+a := by
    simpa [X, X0, Y0, a, rightCarryX] using hquot.1
  have hstep0 := right_tail_step X X0 Y0 0 px py a b hU0 rfl rfl
  have hA0 : -px-py+a = a-px-py := by omega
  have hA1 : -1+a1 = a1-1 := by omega
  have hq0digit : (x'/(3*K))%3 = (a-px-py)%3 := by
    rw [hq0]
    simpa [hA0] using hstep0.1
  have hq1 : (x'/(3*K))/3 = -(X/3)-X-Y+a1 := by
    rw [hq0]
    have h := hstep0.2.2.1
    rw [hcompat] at h
    simpa [a1, hA0, Y, Y0] using h
  have hstep1 := right_tail_step (X/3) X Y 0 0 1 a1 b1 hU1 hU0 hV0
  have hq1digit : ((x'/(3*K))/3)%3 = (a1-1)%3 := by
    rw [hq1]
    simpa [hA1] using hstep1.1
  have hq2 : ((x'/(3*K))/3)/3 = -((X/3)/3)-(X/3)-(Y/3)+a2 := by
    rw [hq1]
    simpa [a2, hA1] using hstep1.2.2.1
  have hstep2 := right_tail_step (X/3/3) (X/3) (Y/3) 0 0 0 a2 b2 hU2 hU1 hV1
  have hq2digit : (((x'/(3*K))/3)/3)%3 = a2%3 := by
    rw [hq2]
    simpa using hstep2.1
  have hreset : NonMono ((a-px-py)%3) ((a1-1)%3) (a2%3) := by
    simpa [px, py, a, b, a1, b1, a2, b2, X, X0, Y0, Y,
      rightCarryX, rightCarryY] using
      (right_source_reset_from_affine_correction K B x y C F
        hK hBK hClo hChi hFlo hFhi).2.2
  rw [hq0digit, hq1digit, hq2digit]
  exact hreset


/-!
## Arbitrary-word affine digit bridge

The earlier reset-output lemmas are specialized to the three-symbol word
01,00,00.  The definitions below expose the full x-digit stream for an
arbitrary source-pair word length.  The y input is offset by one digit in L,
and the previous x/y pair is retained in R, exactly as in the carry
transducers.
-/

/-- First n Euclidean base-three digits of an integer. -/
def intDigitsFrom (z : Int) : Nat → List Int
  | 0 => []
  | n+1 => (z%3) :: intDigitsFrom (z/3) n

/-- Source digit pairs for an L boundary.  The y digit is one place ahead:
    the first L x-output digit uses the preceding y digit Y%3. -/
def leftSourcePairs (X Y : Int) : Nat → List (Int × Int)
  | 0 => []
  | n+1 =>
      (X%3, (Y/3)%3) :: leftSourcePairs (X/3) (Y/3) n

/-- x-output stream of the L carry transducer on an arbitrary pair word. -/
def leftCarryXOutput (prevY carryX : Int) :
    List (Int × Int) → List Int
  | [] => []
  | (u,v)::xs =>
      let t := u - prevY + carryX
      (t%3) :: leftCarryXOutput v (t/3) xs

/-- x-output stream of the R carry transducer on an arbitrary pair word. -/
def rightCarryXOutput (prevX prevY carryX : Int) :
    List (Int × Int) → List Int
  | [] => []
  | (u,v)::xs =>
      let t := -u - prevX - prevY + carryX
      (t%3) :: rightCarryXOutput u v (t/3) xs

/-- The L carry transducer agrees, for every word length, with the
    corresponding affine output x-tail X-Y+a. -/
theorem left_carry_x_output_matches_affine
    (X Y a : Int) (n : Nat) :
    leftCarryXOutput (Y%3) a (leftSourcePairs X Y n) =
      intDigitsFrom (X-Y+a) n := by
  induction n generalizing X Y a with
  | zero => rfl
  | succ n ih =>
      let t : Int := X%3 - Y%3 + a
      have hstep := left_tail_step X Y (X%3) (Y%3) a 0 rfl rfl
      change (t%3) ::
          leftCarryXOutput ((Y/3)%3) (t/3)
            (leftSourcePairs (X/3) (Y/3) n) =
        (X-Y+a)%3 :: intDigitsFrom ((X-Y+a)/3) n
      rw [hstep.1]
      rw [ih (X/3) (Y/3) (t/3)]
      rw [← hstep.2.2.1]

/-- Source digit pairs for an R boundary.  The compatibility X0/3=X is
    supplied by nested Euclidean division at an actual 3K boundary. -/
def rightSourcePairs (X X0 Y0 : Int) : Nat → List (Int × Int)
  | 0 => []
  | n+1 =>
      (X%3, (Y0/3)%3) ::
        rightSourcePairs (X/3) (X0/3) (Y0/3) n

/-- The R carry transducer agrees, for every word length, with the
    corresponding affine output x-tail -X-X0-Y0+a. -/
theorem right_carry_x_output_matches_affine
    (X X0 Y0 a : Int) (n : Nat)
    (hcompat : X0/3 = X) :
    rightCarryXOutput (X0%3) (Y0%3) a
      (rightSourcePairs X X0 Y0 n) =
        intDigitsFrom (-X-X0-Y0+a) n := by
  induction n generalizing X X0 Y0 a with
  | zero => rfl
  | succ n ih =>
      let t : Int := -(X%3) - (X0%3) - (Y0%3) + a
      have hstep :=
        right_tail_step X X0 Y0 (X%3) (X0%3) (Y0%3) a 0 rfl rfl rfl
      have hcompat' : (X0/3)/3 = X/3 := by rw [hcompat]
      have hprev : (X0/3)%3 = X%3 := by rw [hcompat]
      change (t%3) ::
          rightCarryXOutput (X%3) ((Y0/3)%3) (t/3)
            (rightSourcePairs (X/3) (X0/3) (Y0/3) n) =
        (-X-X0-Y0+a)%3 ::
          intDigitsFrom ((-X-X0-Y0+a)/3) n
      rw [hstep.1]
      rw [← hprev]
      rw [ih (X/3) (X0/3) (Y0/3) (t/3) hcompat']
      rw [← hstep.2.2.1]

/-- Actual L successor digits are exactly the arbitrary-length output of
    the L carry transducer, with no restriction on the source word length. -/
theorem left_actual_affine_carry_xdigits
    (K x y C F x' y' : Int) (n : Nat)
    (hK : 0 < K)
    (hxout : x' = x - 3*y + C)
    (hyout : y' = 3*y + F) :
    leftCarryXOutput ((y/K)%3)
      (leftCarryX K (x%(3*K)) (y%K) C)
      (leftSourcePairs (x/(3*K)) (y/K) n) =
        intDigitsFrom (x'/(3*K)) n := by
  have hquot :=
    left_actual_affine_boundary_quotients K x y C F x' y' hK hxout hyout
  calc
    _ = intDigitsFrom
        (x/(3*K) - y/K +
          leftCarryX K (x%(3*K)) (y%K) C) n :=
      left_carry_x_output_matches_affine
        (x/(3*K)) (y/K)
        (leftCarryX K (x%(3*K)) (y%K) C) n
    _ = intDigitsFrom (x'/(3*K)) n := by rw [← hquot.1]

/-- Actual R successor digits are exactly the arbitrary-length output of
    the R carry transducer, with no restriction on the source word length. -/
theorem right_actual_affine_carry_xdigits
    (K x y C F x' y' : Int) (n : Nat)
    (hK : 0 < K)
    (hxout : x' = -4*x - 3*y + C)
    (hyout : y' = 3*x + 3*y + F) :
    rightCarryXOutput ((x/K)%3) ((y/K)%3)
      (rightCarryX K (x%(3*K)) (x%K) (y%K) C)
      (rightSourcePairs (x/(3*K)) (x/K) (y/K) n) =
        intDigitsFrom (x'/(3*K)) n := by
  have hquot :=
    right_actual_affine_boundary_quotients K x y C F x' y' hK hxout hyout
  have hcompat : (x/K)/3 = x/(3*K) := ediv_div_three x K hK
  calc
    _ = intDigitsFrom
        (-(x/(3*K)) - x/K - y/K +
          rightCarryX K (x%(3*K)) (x%K) (y%K) C) n :=
      right_carry_x_output_matches_affine
        (x/(3*K)) (x/K) (y/K)
        (rightCarryX K (x%(3*K)) (x%K) (y%K) C) n hcompat
    _ = intDigitsFrom (x'/(3*K)) n := by rw [← hquot.1]

/-- The shift-aware reset condition: a digit list contains at least one
    digit different from 0 and at least one digit different from 2. -/
def NonMonoDigitList (xs : List Int) : Prop :=
  (∃ z, z ∈ xs ∧ z ≠ 0) ∧ (∃ z, z ∈ xs ∧ z ≠ 2)

/-- If an arbitrary L transducer word has a nonmonochromatic suffix after
    dropping its first output digit, then the same is true of the actual
    successor-coordinate digits. -/
theorem left_actual_affine_drop_first_nonmono
    (K x y C F x' y' : Int) (n : Nat)
    (hK : 0 < K)
    (hxout : x' = x - 3*y + C)
    (hyout : y' = 3*y + F)
    (hnm : NonMonoDigitList
      ((leftCarryXOutput ((y/K)%3)
        (leftCarryX K (x%(3*K)) (y%K) C)
        (leftSourcePairs (x/(3*K)) (y/K) n)).drop 1)) :
    NonMonoDigitList ((intDigitsFrom (x'/(3*K)) n).drop 1) := by
  rw [left_actual_affine_carry_xdigits K x y C F x' y' n hK hxout hyout]
    at hnm
  exact hnm

/-- R version of the arbitrary-word, drop-first actual-output bridge. -/
theorem right_actual_affine_drop_first_nonmono
    (K x y C F x' y' : Int) (n : Nat)
    (hK : 0 < K)
    (hxout : x' = -4*x - 3*y + C)
    (hyout : y' = 3*x + 3*y + F)
    (hnm : NonMonoDigitList
      ((rightCarryXOutput ((x/K)%3) ((y/K)%3)
        (rightCarryX K (x%(3*K)) (x%K) (y%K) C)
        (rightSourcePairs (x/(3*K)) (x/K) (y/K) n)).drop 1)) :
    NonMonoDigitList ((intDigitsFrom (x'/(3*K)) n).drop 1) := by
  rw [right_actual_affine_carry_xdigits K x y C F x' y' n hK hxout hyout]
    at hnm
  exact hnm


/-!
## Full pair-output bridge

The reset automaton consumes digit *pairs*, not only x digits.  The
following stronger interface identifies the complete L/R transducer output
pair stream with the actual affine successor pair digits at every finite
length.
-/

/-- First n Euclidean ternary digit pairs of two integer tails. -/
def intDigitPairsFrom (x y : Int) : Nat → List (Int × Int)
  | 0 => []
  | n+1 => (x%3, y%3) :: intDigitPairsFrom (x/3) (y/3) n

/-- Full L carry-transducer output pair stream on an arbitrary pair word. -/
def leftCarryOutputPairs (prevY carryX carryY : Int) :
    List (Int × Int) → List (Int × Int)
  | [] => []
  | (u,v)::xs =>
      let tx := u - prevY + carryX
      let ty := prevY + carryY
      (tx%3, ty%3) ::
        leftCarryOutputPairs v (tx/3) (ty/3) xs

/-- Full R carry-transducer output pair stream on an arbitrary pair word. -/
def rightCarryOutputPairs
    (prevX prevY carryX carryY : Int) :
    List (Int × Int) → List (Int × Int)
  | [] => []
  | (u,v)::xs =>
      let tx := -u - prevX - prevY + carryX
      let ty := prevX + prevY + carryY
      (tx%3, ty%3) ::
        rightCarryOutputPairs u v (tx/3) (ty/3) xs

/-- Every finite L output pair stream is exactly the affine pair-tail digit
    stream (X-Y+a, Y+b). -/
theorem left_carry_output_pairs_matches_affine
    (X Y a b : Int) (n : Nat) :
    leftCarryOutputPairs (Y%3) a b (leftSourcePairs X Y n) =
      intDigitPairsFrom (X-Y+a) (Y+b) n := by
  induction n generalizing X Y a b with
  | zero => rfl
  | succ n ih =>
      let tx : Int := X%3 - Y%3 + a
      let ty : Int := Y%3 + b
      have hstep := left_tail_step X Y (X%3) (Y%3) a b rfl rfl
      change (tx%3, ty%3) ::
          leftCarryOutputPairs ((Y/3)%3) (tx/3) (ty/3)
            (leftSourcePairs (X/3) (Y/3) n) =
        ((X-Y+a)%3, (Y+b)%3) ::
          intDigitPairsFrom ((X-Y+a)/3) ((Y+b)/3) n
      rw [hstep.1, hstep.2.1]
      rw [ih (X/3) (Y/3) (tx/3) (ty/3)]
      rw [← hstep.2.2.1, ← hstep.2.2.2]

/-- Every finite R output pair stream is exactly the affine pair-tail digit
    stream (-X-X0-Y0+a, X0+Y0+b). -/
theorem right_carry_output_pairs_matches_affine
    (X X0 Y0 a b : Int) (n : Nat)
    (hcompat : X0/3 = X) :
    rightCarryOutputPairs (X0%3) (Y0%3) a b
      (rightSourcePairs X X0 Y0 n) =
        intDigitPairsFrom (-X-X0-Y0+a) (X0+Y0+b) n := by
  induction n generalizing X X0 Y0 a b with
  | zero => rfl
  | succ n ih =>
      let tx : Int := -X%3 - X0%3 - Y0%3 + a
      let ty : Int := X0%3 + Y0%3 + b
      have hstep :=
        right_tail_step X X0 Y0 (X%3) (X0%3) (Y0%3) a b rfl rfl rfl
      have hcompat' : (X0/3)/3 = X/3 := by rw [hcompat]
      have hprev : (X0/3)%3 = X%3 := by rw [hcompat]
      change (tx%3, ty%3) ::
          rightCarryOutputPairs (X%3) ((Y0/3)%3) (tx/3) (ty/3)
            (rightSourcePairs (X/3) (X0/3) (Y0/3) n) =
        ((-X-X0-Y0+a)%3, (X0+Y0+b)%3) ::
          intDigitPairsFrom ((-X-X0-Y0+a)/3) ((X0+Y0+b)/3) n
      rw [hstep.1, hstep.2.1]
      have hrec :=
        ih (X/3) (X0/3) (Y0/3) (tx/3) (ty/3) hcompat'
      rw [hprev] at hrec
      rw [hrec]
      rw [← hstep.2.2.1, ← hstep.2.2.2]

/-- Actual L successor pair digits are the full L transducer output, for
    every finite length. -/
theorem left_actual_affine_carry_pairdigits
    (K x y C F x' y' : Int) (n : Nat)
    (hK : 0 < K)
    (hxout : x' = x - 3*y + C)
    (hyout : y' = 3*y + F) :
    leftCarryOutputPairs ((y/K)%3)
      (leftCarryX K (x%(3*K)) (y%K) C)
      (leftCarryY K (y%K) F)
      (leftSourcePairs (x/(3*K)) (y/K) n) =
        intDigitPairsFrom (x'/(3*K)) (y'/(3*K)) n := by
  have hquot :=
    left_actual_affine_boundary_quotients K x y C F x' y' hK hxout hyout
  calc
    _ = intDigitPairsFrom
        (x/(3*K) - y/K +
          leftCarryX K (x%(3*K)) (y%K) C)
        (y/K + leftCarryY K (y%K) F) n :=
      left_carry_output_pairs_matches_affine
        (x/(3*K)) (y/K)
        (leftCarryX K (x%(3*K)) (y%K) C)
        (leftCarryY K (y%K) F) n
    _ = intDigitPairsFrom (x'/(3*K)) (y'/(3*K)) n := by
      rw [← hquot.1, ← hquot.2]

/-- Actual R successor pair digits are the full R transducer output, for
    every finite length. -/
theorem right_actual_affine_carry_pairdigits
    (K x y C F x' y' : Int) (n : Nat)
    (hK : 0 < K)
    (hxout : x' = -4*x - 3*y + C)
    (hyout : y' = 3*x + 3*y + F) :
    rightCarryOutputPairs ((x/K)%3) ((y/K)%3)
      (rightCarryX K (x%(3*K)) (x%K) (y%K) C)
      (rightCarryY K (x%K) (y%K) F)
      (rightSourcePairs (x/(3*K)) (x/K) (y/K) n) =
        intDigitPairsFrom (x'/(3*K)) (y'/(3*K)) n := by
  have hquot :=
    right_actual_affine_boundary_quotients K x y C F x' y' hK hxout hyout
  have hcompat : (x/K)/3 = x/(3*K) := ediv_div_three x K hK
  calc
    _ = intDigitPairsFrom
        (-(x/(3*K)) - x/K - y/K +
          rightCarryX K (x%(3*K)) (x%K) (y%K) C)
        (x/K + y/K +
          rightCarryY K (x%K) (y%K) F) n :=
      right_carry_output_pairs_matches_affine
        (x/(3*K)) (x/K) (y/K)
        (rightCarryX K (x%(3*K)) (x%K) (y%K) C)
        (rightCarryY K (x%K) (y%K) F) n hcompat
    _ = intDigitPairsFrom (x'/(3*K)) (y'/(3*K)) n := by
      rw [← hquot.1, ← hquot.2]

#print axioms left_affine_boundary_quotients
#print axioms right_affine_boundary_quotients
#print axioms left_source_reset_from_affine_correction
#print axioms right_source_reset_from_affine_correction

end BB6.Agent48SourceCarryAffineBridge
