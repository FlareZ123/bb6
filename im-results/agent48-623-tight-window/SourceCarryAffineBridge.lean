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
    omega
  have hhigh : z / d < q + 1 := by
    apply Int.ediv_lt_of_lt_mul hd
    rw [hdecomp]
    calc
      d*q + r < d*q + d := by omega
      _ = d*(q+1) := by ring
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
      _ = d*(n+z/d)+z%d := by ring
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
    (hx0 : x = K*XHigh0 + xLow0)
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
          3*K*(XHigh1-YHigh0) + (xLow1-3*yLow+C) := by ring
    rw [hlin]
    simpa [leftCarryX] using
      ediv_add_mul (xLow1-3*yLow+C) (3*K) (XHigh1-YHigh0) hden
  · rw [hyout, hy0]
    have hlin :
        3*(K*YHigh0+yLow)+F =
          3*K*YHigh0 + (3*yLow+F) := by ring
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
    have hlin :
        -4*x-3*y+C =
          3*K*(-XHigh1-XHigh0-YHigh0) +
            (-xLow1-3*xLow0-3*yLow+C) := by
      calc
        -4*x-3*y+C = -x-3*x-3*y+C := by ring
        _ = -(3*K*XHigh1+xLow1) -
              3*(K*XHigh0+xLow0) -
              3*(K*YHigh0+yLow)+C := by rw [hx1, hx0, hy0]
        _ = 3*K*(-XHigh1-XHigh0-YHigh0) +
              (-xLow1-3*xLow0-3*yLow+C) := by ring
    rw [hlin]
    simpa [rightCarryX] using
      ediv_add_mul (-xLow1-3*xLow0-3*yLow+C) (3*K)
        (-XHigh1-XHigh0-YHigh0) hden
  · rw [hyout, hx0, hy0]
    have hlin :
        3*(K*XHigh0+xLow0)+3*(K*YHigh0+yLow)+F =
          3*K*(XHigh0+YHigh0)+(3*xLow0+3*yLow+F) := by ring
    rw [hlin]
    simpa [rightCarryY] using
      ediv_add_mul (3*xLow0+3*yLow+F) (3*K)
        (XHigh0+YHigh0) hden

/-- The actual low residues and a strict correction bound place the L
    boundary carries in the source-derived start rectangle. -/
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
  have hBounds :=
    left_source_carry_bounds_from_affine_correction K B x y C F
      hK hBK hClo hChi hFlo hFhi
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
      hpy0 hpy2 rfl rfl rfl rfl
      hBounds.1 hBounds.2.1 hBounds.2.2.1 hBounds.2.2.2
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
  have hBounds :=
    right_source_carry_bounds_from_affine_correction K B x y C F
      hK hBK hClo hChi hFlo hFhi
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
      hpx0 hpx2 hpy0 hpy2 rfl rfl rfl rfl
      hBounds.1 hBounds.2.1 hBounds.2.2.1 hBounds.2.2.2
  simpa [px, py, a, b, a1, b1, a2, b2, rightCarryX, rightCarryY] using hreset

#print axioms left_affine_boundary_quotients
#print axioms right_affine_boundary_quotients
#print axioms left_source_reset_from_affine_correction
#print axioms right_source_reset_from_affine_correction

end BB6.Agent48SourceCarryAffineBridge
