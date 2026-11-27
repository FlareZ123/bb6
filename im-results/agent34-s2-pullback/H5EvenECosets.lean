import H5EvenEParentCriterion
import Lean.Elab.Tactic.Omega

namespace BB6.Agent34EvenECosets
open BB6.Agent42ModularCone
open BB6.Agent34EvenECriterion
set_option maxRecDepth 8192
set_option maxHeartbeats 4000000

/-- The congruence lift is exact: shifting the shared mass coordinate
    q by 2^16 leaves the direct-parent signed residue unchanged. -/
theorem direct_period16 (q z : Nat) :
    residue 16 (directQ (q+65536*z)) = residue 16 (directQ q) := by
  simp only [residue, directQ, Int.natCast_add, Int.natCast_mul, Int.cast_ofNat_Int]
  rw [Pair.mk.injEq]
  constructor
  · apply Int.emod_eq_emod_iff_emod_sub_eq_zero.mpr
    apply Int.emod_eq_zero_of_dvd
    refine ⟨8*(z:Int), ?_⟩
    change _ = (65536:Int) * _
    omega
  · apply Int.emod_eq_emod_iff_emod_sub_eq_zero.mpr
    apply Int.emod_eq_zero_of_dvd
    refine ⟨-4*(z:Int), ?_⟩
    change _ = (65536:Int) * _
    omega

/-- The odd-depth high parent has the same 2^16 mass periodicity. -/
theorem high_period16 (q z : Nat) :
    residue 16 (highQ (q+65536*z)) = residue 16 (highQ q) := by
  simp only [residue, highQ, Int.natCast_add, Int.natCast_mul, Int.cast_ofNat_Int]
  rw [Pair.mk.injEq]
  constructor
  · apply Int.emod_eq_emod_iff_emod_sub_eq_zero.mpr
    apply Int.emod_eq_zero_of_dvd
    refine ⟨2*(z:Int), ?_⟩
    change _ = (65536:Int) * _
    omega
  · apply Int.emod_eq_emod_iff_emod_sub_eq_zero.mpr
    apply Int.emod_eq_zero_of_dvd
    refine ⟨-(z:Int), ?_⟩
    change _ = (65536:Int) * _
    omega

/-- One finite 16-bit certificate proves both parent exclusions for an
    unbounded progression of mass values, with no brute-force bound. -/
theorem q10083_parent_cert (q : Nat) (hq : q%65536=10083) :
    excluded 16 (directQ q)=true ∧
    excluded 16 (highQ q)=true := by
  have hd : q=10083+65536*(q/65536) := by
    have h := Nat.mod_add_div q 65536
    omega
  have hb := example_Q10083
  constructor
  · unfold excluded
    rw [hd, direct_period16]
    exact hb.1
  · unfold excluded
    rw [hd, high_period16]
    exact hb.2

/-- Novel source-level two-parameter infinite E-family with a single
    congruence hypothesis on the mass parameter q (not a point test). -/
theorem E_q10083_source (r B : Nat)
    (hQ : (Q r B)%65536=10083) :
    ¬ BB6.Agent3.CReach (Eax r B) (Eay r B) := by
  have ho : Q r B % 2 = 1 := by
    have h := Nat.mod_add_div (Q r B) 65536
    omega
  have hc := q10083_parent_cert (Q r B) hQ
  exact evenE_source_excluded r B ho hc.1 hc.2

/-- Explicit source-unreachable infinite 2D affine progression:
    its parameter-lattice density is 2^-16 among unrestricted (r,B). -/
theorem E_affine_coset_source (r z : Nat) :
    ¬ BB6.Agent3.CReach
      (Eax r (65444+4131*r+65536*z))
      (Eay r (65444+4131*r+65536*z)) := by
  have hq : Q r (65444+4131*r+65536*z)%65536=10083 := by
    dsimp [Q]
    omega
  exact E_q10083_source r _ hq

#print axioms direct_period16
#print axioms high_period16
#print axioms q10083_parent_cert
#print axioms E_q10083_source
#print axioms E_affine_coset_source
end BB6.Agent34EvenECosets
