import ModularConeHighStop
import Lean.Elab.Tactic.Omega
namespace BB6.Agent34H5Precision
open BB6.Agent42ModularCone
set_option maxRecDepth 8192
set_option maxHeartbeats 2000000

def highStopBitsCap (cap j m : Nat) : Nat :=
  if 2 ≤ j then min cap (2*m+2) else min cap (2*m+1)
def highStopExcludedCap (cap j m : Nat) : Bool :=
  excluded (highStopBitsCap cap j m) (stopResidue j m)
theorem cap32_eq (j m : Nat) :
    highStopExcludedCap 32 j m = highStopExcluded j m := rfl
theorem high_stop_excluded_cap (cap j m k : Nat)
    (hstop : k+j+3*m+4 = 2^(2*m+2)*(j+2))
    (hc : highStopExcludedCap cap j m = true) :
    ¬ BB6.Agent3.CReach (2*j+1) k := by
  let b := highStopBitsCap cap j m
  have hb : b≤2*m+1 ∨ (2≤j ∧ b≤2*m+2) := by
    by_cases h : 2≤j
    · right
      exact ⟨h, by simpa [b, highStopBitsCap, h] using
        (Nat.min_le_right cap (2*m+2))⟩
    · left
      simpa [b, highStopBitsCap, h] using
        (Nat.min_le_right cap (2*m+1))
  exact source_stop_cylinder_excluded b j m j m k hb
    (cong_refl b (j:Int)) (cong_refl b (m:Int)) hstop hc

def J (r : Nat) : Nat := 2098496 + 4194304*r
def M (r w : Nat) : Nat := 4876330 + 4194304*r + 8388608*w
theorem base37 : excluded 37 (stopResidue (J 0) (M 0 0)) = true := by decide
theorem base36 : excluded 36 (stopResidue (J 0) (M 0 0)) = false := by decide
theorem base32 : excluded 32 (stopResidue (J 0) (M 0 0)) = false := by decide
theorem lifted_residue37 (r w : Nat) :
    residue 37 (stopResidue (J (16384*r)) (M (16384*r) (16384*w))) =
      residue 37 (stopResidue (J 0) (M 0 0)) := by
  simp only [residue, stopResidue, J, M, Int.natCast_add, Int.natCast_mul, Int.cast_ofNat_Int]
  rw [Pair.mk.injEq]
  constructor
  · apply Int.emod_eq_emod_iff_emod_sub_eq_zero.mpr
    apply Int.emod_eq_zero_of_dvd
    refine ⟨(r:Int), ?_⟩
    change _ = (137438953472:Int) * _
    omega
  · apply Int.emod_eq_emod_iff_emod_sub_eq_zero.mpr
    apply Int.emod_eq_zero_of_dvd
    refine ⟨-2*(r:Int)-3*(w:Int), ?_⟩
    change _ = (137438953472:Int) * _
    omega
theorem lifted_residue32 (r w : Nat) :
    residue 32 (stopResidue (J (16384*r)) (M (16384*r) (16384*w))) =
      residue 32 (stopResidue (J 0) (M 0 0)) := by
  simp only [residue, stopResidue, J, M, Int.natCast_add, Int.natCast_mul, Int.cast_ofNat_Int]
  rw [Pair.mk.injEq]
  constructor
  · apply Int.emod_eq_emod_iff_emod_sub_eq_zero.mpr
    apply Int.emod_eq_zero_of_dvd
    refine ⟨32*(r:Int), ?_⟩
    change _ = (4294967296:Int) * _
    omega
  · apply Int.emod_eq_emod_iff_emod_sub_eq_zero.mpr
    apply Int.emod_eq_zero_of_dvd
    refine ⟨-64*(r:Int)-96*(w:Int), ?_⟩
    change _ = (4294967296:Int) * _
    omega
theorem lifted37 (r w : Nat) :
    excluded 37 (stopResidue (J (16384*r)) (M (16384*r) (16384*w))) = true := by
  unfold excluded
  rw [lifted_residue37]
  exact base37
theorem lifted32miss (r w : Nat) :
    highStopExcluded (J (16384*r)) (M (16384*r) (16384*w)) = false := by
  have hJ : 2 ≤ J (16384*r) := by unfold J; omega
  have hM : 32 ≤ 2*M (16384*r) (16384*w)+2 := by unfold M; omega
  simp only [highStopExcluded, highStopBits, hJ, ite_true, Nat.min_eq_left hM, excluded]
  rw [lifted_residue32]
  exact base32
theorem lifted_quarter_miss (r w : Nat) :
    ¬ ((5*(16384*r)+3*(16384*w)+4)%8=0 ∨
      (5*(16384*r)+3*(16384*w)+17)%16=0 ∨
      ∃ t, t∈[26,48,51,56] ∧ (37*(16384*r)+3*(16384*w)+t)%64=0) := by
  rintro (h | h | ⟨t,ht,h⟩)
  · omega
  · omega
  · simp at ht
    rcases ht with h26 | h48 | h51 | h56 <;> subst t <;> omega
theorem lifted_source (r w k : Nat)
    (hstop : k+J (16384*r)+3*M (16384*r) (16384*w)+4 =
      2^(2*M (16384*r) (16384*w)+2)*(J (16384*r)+2)) :
    ¬ BB6.Agent3.CReach (2*J (16384*r)+1) k := by
  have hb : 37≤2*M (16384*r) (16384*w)+1 := by unfold M; omega
  exact source_stop_cylinder_excluded 37
    (J (16384*r)) (M (16384*r) (16384*w))
    (J (16384*r)) (M (16384*r) (16384*w)) k (Or.inl hb)
    (cong_refl 37 _) (cong_refl 37 _) hstop (lifted37 r w)

/-- A substantially wider 33-bit H5 certificate in a phase-guard-free coset.
    The affine stop residue has differences 2^33*r and -2^33*(2*r+3*w). -/
theorem base33_w15 :
    excluded 33 (stopResidue (J 0) (M 0 15)) = true := by decide
theorem base32_w15 :
    excluded 32 (stopResidue (J 0) (M 0 15)) = false := by decide

theorem lifted_w15_residue33 (r w : Nat) :
    residue 33 (stopResidue (J (1024*r)) (M (1024*r) (15+1024*w))) =
      residue 33 (stopResidue (J 0) (M 0 15)) := by
  simp only [residue, stopResidue, J, M, Int.natCast_add, Int.natCast_mul, Int.cast_ofNat_Int]
  rw [Pair.mk.injEq]
  constructor
  · apply Int.emod_eq_emod_iff_emod_sub_eq_zero.mpr
    apply Int.emod_eq_zero_of_dvd
    refine ⟨(r:Int), ?_⟩
    change _ = (8589934592:Int) * _
    omega
  · apply Int.emod_eq_emod_iff_emod_sub_eq_zero.mpr
    apply Int.emod_eq_zero_of_dvd
    refine ⟨-2*(r:Int)-3*(w:Int), ?_⟩
    change _ = (8589934592:Int) * _
    omega

theorem lifted_w15_residue32 (r w : Nat) :
    residue 32 (stopResidue (J (1024*r)) (M (1024*r) (15+1024*w))) =
      residue 32 (stopResidue (J 0) (M 0 15)) := by
  simp only [residue, stopResidue, J, M, Int.natCast_add, Int.natCast_mul, Int.cast_ofNat_Int]
  rw [Pair.mk.injEq]
  constructor
  · apply Int.emod_eq_emod_iff_emod_sub_eq_zero.mpr
    apply Int.emod_eq_zero_of_dvd
    refine ⟨2*(r:Int), ?_⟩
    change _ = (4294967296:Int) * _
    omega
  · apply Int.emod_eq_emod_iff_emod_sub_eq_zero.mpr
    apply Int.emod_eq_zero_of_dvd
    refine ⟨-4*(r:Int)-6*(w:Int), ?_⟩
    change _ = (4294967296:Int) * _
    omega

theorem lifted_w15_33 (r w : Nat) :
    excluded 33 (stopResidue (J (1024*r)) (M (1024*r) (15+1024*w))) = true := by
  unfold excluded
  rw [lifted_w15_residue33]
  exact base33_w15

theorem lifted_w15_32_miss (r w : Nat) :
    highStopExcluded (J (1024*r)) (M (1024*r) (15+1024*w)) = false := by
  have hJ : 2 ≤ J (1024*r) := by unfold J; omega
  have hM : 32 ≤ 2*M (1024*r) (15+1024*w)+2 := by unfold M; omega
  simp only [highStopExcluded, highStopBits, hJ, ite_true, Nat.min_eq_left hM, excluded]
  rw [lifted_w15_residue32]
  exact base32_w15

theorem lifted_w15_quarter_miss (r w : Nat) :
    ¬ ((5*(1024*r)+3*(15+1024*w)+4)%8=0 ∨
      (5*(1024*r)+3*(15+1024*w)+17)%16=0 ∨
      ∃ t, t∈[26,48,51,56] ∧
        (37*(1024*r)+3*(15+1024*w)+t)%64=0) := by
  rintro (h | h | ⟨t,ht,h⟩)
  · omega
  · omega
  · simp at ht
    rcases ht with h26 | h48 | h51 | h56 <;> subst t <;> omega

/-- Genuine original-section all-time exclusion for the new 33-bit
    coset, conditional only on the exact high-stop equation. -/
theorem lifted_w15_source (r w k : Nat)
    (hstop : k+J (1024*r)+3*M (1024*r) (15+1024*w)+4 =
      2^(2*M (1024*r) (15+1024*w)+2)*(J (1024*r)+2)) :
    ¬ BB6.Agent3.CReach (2*J (1024*r)+1) k := by
  have hb : 33 ≤ 2*M (1024*r) (15+1024*w)+1 := by unfold M; omega
  exact source_stop_cylinder_excluded 33
    (J (1024*r)) (M (1024*r) (15+1024*w))
    (J (1024*r)) (M (1024*r) (15+1024*w)) k (Or.inl hb)
    (cong_refl 33 _) (cong_refl 33 _) hstop (lifted_w15_33 r w)

#print axioms base33_w15
#print axioms lifted_w15_33
#print axioms lifted_w15_32_miss
#print axioms lifted_w15_quarter_miss
#print axioms lifted_w15_source


/-- The signed stop residue is affine at any base parameter. Every
    simultaneous shift by 1024 preserves its first 33 bits. -/
theorem arbitrary_base_residue33 (r0 w0 r w : Nat) :
    residue 33 (stopResidue (J (r0+1024*r)) (M (r0+1024*r) (w0+1024*w))) =
      residue 33 (stopResidue (J r0) (M r0 w0)) := by
  simp only [residue, stopResidue, J, M, Int.natCast_add, Int.natCast_mul, Int.cast_ofNat_Int]
  rw [Pair.mk.injEq]
  constructor
  · apply Int.emod_eq_emod_iff_emod_sub_eq_zero.mpr
    apply Int.emod_eq_zero_of_dvd
    refine ⟨(r:Int), ?_⟩
    change _ = (8589934592:Int) * _
    omega
  · apply Int.emod_eq_emod_iff_emod_sub_eq_zero.mpr
    apply Int.emod_eq_zero_of_dvd
    refine ⟨-2*(r:Int)-3*(w:Int), ?_⟩
    change _ = (8589934592:Int) * _
    omega

theorem arbitrary_base33_source (r0 w0 r w k : Nat)
    (hcert : excluded 33 (stopResidue (J r0) (M r0 w0)) = true)
    (hstop :
       k+J (r0+1024*r)+3*M (r0+1024*r) (w0+1024*w)+4 =
       2^(2*M (r0+1024*r) (w0+1024*w)+2)*(J (r0+1024*r)+2)) :
    ¬ BB6.Agent3.CReach (2*J (r0+1024*r)+1) k := by
  have hb : 33 ≤ 2*M (r0+1024*r) (w0+1024*w)+1 := by unfold M; omega
  apply source_stop_cylinder_excluded 33
    (J (r0+1024*r)) (M (r0+1024*r) (w0+1024*w))
    (J (r0+1024*r)) (M (r0+1024*r) (w0+1024*w)) k (Or.inl hb)
    (cong_refl 33 _) (cong_refl 33 _) hstop
  unfold excluded
  rw [arbitrary_base_residue33]
  exact hcert

/-- Second 33-bit base in the correlated diagonal family. -/
theorem base33_r512_w527 :
    excluded 33 (stopResidue (J 512) (M 512 527)) = true := by decide
theorem base32_r512_w527 :
    excluded 32 (stopResidue (J 512) (M 512 527)) = false := by decide

theorem diagonal33_source (n w k : Nat)
    (hstop :
      k+J (512*n)+3*M (512*n) (15+512*n+1024*w)+4 =
      2^(2*M (512*n) (15+512*n+1024*w)+2)*(J (512*n)+2)) :
    ¬ BB6.Agent3.CReach (2*J (512*n)+1) k := by
  by_cases heven : n%2=0
  · let t := n/2
    have hn : n=2*t := by dsimp [t]; omega
    have hj : J (512*n) = J (0+1024*t) := by unfold J; omega
    have hm : M (512*n) (15+512*n+1024*w) =
        M (0+1024*t) (15+1024*(t+w)) := by unfold M; omega
    have hs : k+J (0+1024*t)+3*M (0+1024*t) (15+1024*(t+w))+4 =
       2^(2*M (0+1024*t) (15+1024*(t+w))+2)*(J (0+1024*t)+2) := by
      simpa only [hj, hm] using hstop
    have hr := arbitrary_base33_source 0 15 t (t+w) k base33_w15 hs
    simpa only [hj] using hr
  · let t := n/2
    have hn : n=2*t+1 := by dsimp [t]; omega
    have hj : J (512*n) = J (512+1024*t) := by unfold J; omega
    have hm : M (512*n) (15+512*n+1024*w) =
        M (512+1024*t) (527+1024*(t+w)) := by unfold M; omega
    have hs : k+J (512+1024*t)+3*M (512+1024*t) (527+1024*(t+w))+4 =
       2^(2*M (512+1024*t) (527+1024*(t+w))+2)*(J (512+1024*t)+2) := by
      simpa only [hj, hm] using hstop
    have hr := arbitrary_base33_source 512 527 t (t+w) k base33_r512_w527 hs
    simpa only [hj] using hr

#print axioms arbitrary_base_residue33
#print axioms arbitrary_base33_source
#print axioms base33_r512_w527
#print axioms diagonal33_source

#print axioms high_stop_excluded_cap
#print axioms base37
#print axioms lifted37
#print axioms lifted32miss
#print axioms lifted_quarter_miss
#print axioms lifted_source
end BB6.Agent34H5Precision
