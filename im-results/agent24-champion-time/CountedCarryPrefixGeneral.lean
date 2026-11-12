import CountedCarryPrefix
import CountedCarryBoundaryTraces
import Lean.Elab.Tactic.Omega

namespace BB6Coverage.Agent48Champion

set_option maxHeartbeats 1000000

/-- Away from the two cells changed by the closed-form left sweep, the
post-sweep tape is exactly the source tape. -/
theorem carryLeftSweep_preserves_at (r s : Nat) (T : Int → Bool)
    (hmatch : ∀ x, carryInputArea r x = true → T x = carryInputBit r x)
    (hs : 0 < s) (hbound : 4*s ≤ 3*r) (x : Int)
    (hx1 : x ≠ 1) (hxb : x ≠ 1-4*(s:Int)) :
    sweptLeft (4*s) T 0 x = T x := by
  have hon := carryInput_leftOnes r s T hmatch hbound
  have hzero : T 1 = false := by
    exact carryInput_unmarked r T hmatch 1 (by omega) (by omega) (by
      simp [carryInputBit]; omega)
  rw [carryLeftSweep_closed s T hs hon hzero]
  simp [hx1,hxb]

/-- The left sweep moves its unique zero boundary to head+1. -/
theorem carryLeftSweep_boundary_zero (r s : Nat) (T : Int → Bool)
    (hmatch : ∀ x, carryInputArea r x = true → T x = carryInputBit r x)
    (hs : 0 < s) (hbound : 4*s ≤ 3*r) :
    sweptLeft (4*s) T 0 (1-4*(s:Int)) = false := by
  have hon := carryInput_leftOnes r s T hmatch hbound
  have hzero : T 1 = false := by
    exact carryInput_unmarked r T hmatch 1 (by omega) (by omega) (by
      simp [carryInputBit]; omega)
  rw [carryLeftSweep_closed s T hs hon hzero]
  simp

/-- rho=0: the source's final 4k ones give the nine-cell bridge window. -/
theorem carryBridge0_input_match (k : Nat) (T : Int → Bool)
    (hmatch : ∀ x, carryInputArea (4*k) x = true →
      T x = carryInputBit (4*k) x) (hk : 0 < k) :
    ∀ i : Int, -1 ≤ i → i ≤ 10 →
      sweptLeft (12*k) T 0 (-12*(k:Int)+i) =
        decide (i ∈ ([2,3,4,5,6,7,8,9,10] : List Int)) := by
  have hs : 0 < 3*k := by omega
  have hb : 4*(3*k) ≤ 3*(4*k) := by omega
  intro i hlo hhi
  have hcases : i = -1 ∨ i = 0 ∨ i = 1 ∨ (2 ≤ i ∧ i ≤ 10) := by omega
  rcases hcases with hneg | hzero | hone | hpos
  · subst i
    have hblank := carryInput_unmarked (4*k) T hmatch
      (-12*(k:Int)-1) (by omega) (by omega) (by simp [carryInputBit]; omega)
    have hval := carryLeftSweep_preserves_at (4*k) (3*k) T hmatch hs hb
      (-12*(k:Int)-1) (by omega) (by omega)
    have hmem : (-1:Int) ∉ ([2,3,4,5,6,7,8,9,10] : List Int) := by simp
    simpa [hmem] using hval.trans hblank
  · subst i
    have hblank := carryInput_unmarked (4*k) T hmatch
      (-12*(k:Int)) (by omega) (by omega) (by simp [carryInputBit]; omega)
    have hval := carryLeftSweep_preserves_at (4*k) (3*k) T hmatch hs hb
      (-12*(k:Int)) (by omega) (by omega)
    have hmem : (0:Int) ∉ ([2,3,4,5,6,7,8,9,10] : List Int) := by simp
    simpa [hmem] using hval.trans hblank
  · subst i
    have hval := carryLeftSweep_boundary_zero (4*k) (3*k) T hmatch hs hb
    have hmem : (1:Int) ∉ ([2,3,4,5,6,7,8,9,10] : List Int) := by simp
    simpa [hmem] using hval
  · have hval := carryLeftSweep_marked (4*k) (3*k) T hmatch hs hb
      (-12*(k:Int)+i) (by omega) (by omega)
    have hmem : i ∈ ([2,3,4,5,6,7,8,9,10] : List Int) := by simp; omega
    simpa [hmem] using hval

/-- rho=1: the residual one and the rightward run give the bridge window. -/
theorem carryBridge1_input_match (k : Nat) (T : Int → Bool)
    (hmatch : ∀ x, carryInputArea (4*k+3) x = true →
      T x = carryInputBit (4*k+3) x) :
    ∀ i : Int, -2 ≤ i → i ≤ 6 →
      sweptLeft (12*k+8) T 0 (-12*(k:Int)-8+i) =
        decide (i ∈ ([0,2,3,4,5,6] : List Int)) := by
  have hs : 0 < 3*k+2 := by omega
  have hb : 4*(3*k+2) ≤ 3*(4*k+3) := by omega
  intro i hlo hhi
  have hcases : i = -2 ∨ i = -1 ∨ i = 0 ∨ i = 1 ∨ (2 ≤ i ∧ i ≤ 6) := by omega
  rcases hcases with hneg | hzero | hone | hboundary | hpos
  · subst i
    have hblank := carryInput_unmarked (4*k+3) T hmatch
      (-12*(k:Int)-10) (by omega) (by omega) (by simp [carryInputBit]; omega)
    have hval := carryLeftSweep_preserves_at (4*k+3) (3*k+2) T hmatch hs hb
      (-12*(k:Int)-10) (by omega) (by omega)
    have hmem : (-2:Int) ∉ ([0,2,3,4,5,6] : List Int) := by simp
    simpa [hmem] using hval.trans hblank
  · subst i
    have hblank := carryInput_unmarked (4*k+3) T hmatch
      (-12*(k:Int)-9) (by omega) (by omega) (by simp [carryInputBit]; omega)
    have hval := carryLeftSweep_preserves_at (4*k+3) (3*k+2) T hmatch hs hb
      (-12*(k:Int)-9) (by omega) (by omega)
    have hmem : (-1:Int) ∉ ([0,2,3,4,5,6] : List Int) := by simp
    simpa [hmem] using hval.trans hblank
  · subst i
    have hone' := carryInput_marked (4*k+3) T hmatch
      (-12*(k:Int)-8) (Or.inl (by constructor <;> omega))
    have hval := carryLeftSweep_preserves_at (4*k+3) (3*k+2) T hmatch hs hb
      (-12*(k:Int)-8) (by omega) (by omega)
    have hmem : (0:Int) ∈ ([0,2,3,4,5,6] : List Int) := by simp
    simpa [hmem] using hval.trans hone'
  · subst i
    have hval := carryLeftSweep_boundary_zero (4*k+3) (3*k+2) T hmatch hs hb
    have hmem : (1:Int) ∉ ([0,2,3,4,5,6] : List Int) := by simp
    simpa [hmem] using hval
  · have hval := carryLeftSweep_marked (4*k+3) (3*k+2) T hmatch hs hb
      (-12*(k:Int)-8+i) (by omega) (by omega)
    have hmem : i ∈ ([0,2,3,4,5,6] : List Int) := by simp; omega
    simpa [hmem] using hval

/-- rho=2: two residual ones, a rightward guard, and the zero boundary. -/
theorem carryBridge2_input_match (k : Nat) (T : Int → Bool)
    (hmatch : ∀ x, carryInputArea (4*k+2) x = true →
      T x = carryInputBit (4*k+2) x) :
    ∀ i : Int, -3 ≤ i → i ≤ 2 →
      sweptLeft (12*k+4) T 0 (-12*(k:Int)-4+i) =
        decide (i ∈ ([-1,0,2] : List Int)) := by
  have hs : 0 < 3*k+1 := by omega
  have hb : 4*(3*k+1) ≤ 3*(4*k+2) := by omega
  intro i hlo hhi
  have hcases : i = -3 ∨ i = -2 ∨ i = -1 ∨ i = 0 ∨ i = 1 ∨ i = 2 := by omega
  rcases hcases with hneg | hzero | hone1 | hone0 | hboundary | hpos
  · subst i
    have hblank := carryInput_unmarked (4*k+2) T hmatch
      (-12*(k:Int)-7) (by omega) (by omega) (by simp [carryInputBit]; omega)
    have hval := carryLeftSweep_preserves_at (4*k+2) (3*k+1) T hmatch hs hb
      (-12*(k:Int)-7) (by omega) (by omega)
    have hmem : (-3:Int) ∉ ([-1,0,2] : List Int) := by simp
    simpa [hmem] using hval.trans hblank
  · subst i
    have hblank := carryInput_unmarked (4*k+2) T hmatch
      (-12*(k:Int)-6) (by omega) (by omega) (by simp [carryInputBit]; omega)
    have hval := carryLeftSweep_preserves_at (4*k+2) (3*k+1) T hmatch hs hb
      (-12*(k:Int)-6) (by omega) (by omega)
    have hmem : (-2:Int) ∉ ([-1,0,2] : List Int) := by simp
    simpa [hmem] using hval.trans hblank
  · subst i
    have hone := carryInput_marked (4*k+2) T hmatch
      (-12*(k:Int)-5) (Or.inl (by constructor <;> omega))
    have hval := carryLeftSweep_preserves_at (4*k+2) (3*k+1) T hmatch hs hb
      (-12*(k:Int)-5) (by omega) (by omega)
    have hmem : (-1:Int) ∈ ([-1,0,2] : List Int) := by simp
    simpa [hmem] using hval.trans hone
  · subst i
    have hone := carryInput_marked (4*k+2) T hmatch
      (-12*(k:Int)-4) (Or.inl (by constructor <;> omega))
    have hval := carryLeftSweep_preserves_at (4*k+2) (3*k+1) T hmatch hs hb
      (-12*(k:Int)-4) (by omega) (by omega)
    have hmem : (0:Int) ∈ ([-1,0,2] : List Int) := by simp
    simpa [hmem] using hval.trans hone
  · subst i
    have hval := carryLeftSweep_boundary_zero (4*k+2) (3*k+1) T hmatch hs hb
    have hmem : (1:Int) ∉ ([-1,0,2] : List Int) := by simp
    simpa [hmem] using hval
  · have hval := carryLeftSweep_marked (4*k+2) (3*k+1) T hmatch hs hb
      (-12*(k:Int)-4+i) (by omega) (by omega)
    have hmem : (2:Int) ∈ ([-1,0,2] : List Int) := by simp
    simpa [hmem] using hval

/-- rho=3 for k>0: the three residual ones and the zero boundary. -/
theorem carryBridge3_input_match (k : Nat) (T : Int → Bool)
    (hmatch : ∀ x, carryInputArea (4*k+1) x = true →
      T x = carryInputBit (4*k+1) x) (hk : 0 < k) :
    ∀ i : Int, -4 ≤ i → i ≤ 1 →
      sweptLeft (12*k) T 0 (-12*(k:Int)+i) =
        decide (i ∈ ([-2,-1,0] : List Int)) := by
  have hs : 0 < 3*k := by omega
  have hb : 4*(3*k) ≤ 3*(4*k+1) := by omega
  intro i hlo hhi
  have hcases : i = -4 ∨ i = -3 ∨ i = -2 ∨ i = -1 ∨ i = 0 ∨ i = 1 := by omega
  rcases hcases with hneg | hzero | hone2 | hone1 | hone0 | hboundary
  · subst i
    have hblank := carryInput_unmarked (4*k+1) T hmatch
      (-12*(k:Int)-4) (by omega) (by omega) (by simp [carryInputBit]; omega)
    have hval := carryLeftSweep_preserves_at (4*k+1) (3*k) T hmatch hs hb
      (-12*(k:Int)-4) (by omega) (by omega)
    have hmem : (-4:Int) ∉ ([-2,-1,0] : List Int) := by simp
    simpa [hmem] using hval.trans hblank
  · subst i
    have hblank := carryInput_unmarked (4*k+1) T hmatch
      (-12*(k:Int)-3) (by omega) (by omega) (by simp [carryInputBit]; omega)
    have hval := carryLeftSweep_preserves_at (4*k+1) (3*k) T hmatch hs hb
      (-12*(k:Int)-3) (by omega) (by omega)
    have hmem : (-3:Int) ∉ ([-2,-1,0] : List Int) := by simp
    simpa [hmem] using hval.trans hblank
  · subst i
    have hone := carryInput_marked (4*k+1) T hmatch
      (-12*(k:Int)-2) (Or.inl (by constructor <;> omega))
    have hval := carryLeftSweep_preserves_at (4*k+1) (3*k) T hmatch hs hb
      (-12*(k:Int)-2) (by omega) (by omega)
    have hmem : (-2:Int) ∈ ([-2,-1,0] : List Int) := by simp
    simpa [hmem] using hval.trans hone
  · subst i
    have hone := carryInput_marked (4*k+1) T hmatch
      (-12*(k:Int)-1) (Or.inl (by constructor <;> omega))
    have hval := carryLeftSweep_preserves_at (4*k+1) (3*k) T hmatch hs hb
      (-12*(k:Int)-1) (by omega) (by omega)
    have hmem : (-1:Int) ∈ ([-2,-1,0] : List Int) := by simp
    simpa [hmem] using hval.trans hone
  · subst i
    have hone := carryInput_marked (4*k+1) T hmatch
      (-12*(k:Int)) (Or.inl (by constructor <;> omega))
    have hval := carryLeftSweep_preserves_at (4*k+1) (3*k) T hmatch hs hb
      (-12*(k:Int)) (by omega) (by omega)
    have hmem : (0:Int) ∈ ([-2,-1,0] : List Int) := by simp
    simpa [hmem] using hval.trans hone
  · subst i
    have hval := carryLeftSweep_boundary_zero (4*k+1) (3*k) T hmatch hs hb
    have hmem : (1:Int) ∉ ([-2,-1,0] : List Int) := by simp
    simpa [hmem] using hval

/-- The r=1 short branch enters the rho=3 bridge without a left sweep. -/
theorem carryBridge3_input_match_r1 (T : Int → Bool)
    (hmatch : ∀ x, carryInputArea 1 x = true → T x = carryInputBit 1 x) :
    ∀ i : Int, -4 ≤ i → i ≤ 1 →
      T i = decide (i ∈ ([-2,-1,0] : List Int)) := by
  intro i hlo hhi
  have hcases : i = -4 ∨ i = -3 ∨ i = -2 ∨ i = -1 ∨ i = 0 ∨ i = 1 := by omega
  rcases hcases with hneg | hzero | hone2 | hone1 | hone0 | hboundary
  · subst i
    have hblank := carryInput_unmarked 1 T hmatch (-4) (by omega) (by omega)
      (by simp [carryInputBit]; omega)
    have hmem : (-4:Int) ∉ ([-2,-1,0] : List Int) := by simp
    simpa [hmem] using hblank
  · subst i
    have hblank := carryInput_unmarked 1 T hmatch (-3) (by omega) (by omega)
      (by simp [carryInputBit]; omega)
    have hmem : (-3:Int) ∉ ([-2,-1,0] : List Int) := by simp
    simpa [hmem] using hblank
  · subst i
    have hone := carryInput_marked 1 T hmatch (-2) (Or.inl (by constructor <;> omega))
    have hmem : (-2:Int) ∈ ([-2,-1,0] : List Int) := by simp
    simpa [hmem] using hone
  · subst i
    have hone := carryInput_marked 1 T hmatch (-1) (Or.inl (by constructor <;> omega))
    have hmem : (-1:Int) ∈ ([-2,-1,0] : List Int) := by simp
    simpa [hmem] using hone
  · subst i
    have hone := carryInput_marked 1 T hmatch 0 (Or.inl (by constructor <;> omega))
    have hmem : (0:Int) ∈ ([-2,-1,0] : List Int) := by simp
    simpa [hmem] using hone
  · subst i
    have hblank := carryInput_unmarked 1 T hmatch 1 (by omega) (by omega)
      (by simp [carryInputBit]; omega)
    have hmem : (1:Int) ∉ ([-2,-1,0] : List Int) := by simp
    simpa [hmem] using hblank

end BB6Coverage.Agent48Champion
