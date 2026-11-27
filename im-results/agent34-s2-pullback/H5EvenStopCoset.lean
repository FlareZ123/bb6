import H5ExactSpine
import H5EvenECosets
import Lean.Elab.Tactic.Omega

namespace BB6.Agent34H5EvenStopCoset
open BB6.Agent42ModularCone
open BB6.Agent34H5Precision
open BB6.Agent34H5Exact
open BB6.Agent34EvenECriterion
open BB6.Agent34EvenECosets
set_option maxRecDepth 8192
set_option maxHeartbeats 4000000

def D (r w : Nat) : Nat := 2+2*r+3*w
def C (r w : Nat) : Nat := 2567283+2208205*r+4416411*w

/-- The massive exact high-stop power forces the offset B modulo 2^16,
    without evaluating the power and for arbitrarily large parameters. -/
theorem highstop_mass_mod (r w B : Nat)
    (hstop : (49726+8388608*B)+J r+3*M r w+4 =
      2^(2*M r w+2)*(J r+2)) :
    (Q r B + C r w)%65536=0 := by
  have hm : 21≤2*M r w := by unfold M; omega
  have he : 2*M r w+2=23+(2*M r w-21) := by omega
  have hp : 2^(2*M r w+2)=8388608*2^(2*M r w-21) := by
    rw [he, Nat.pow_add]
    rfl
  have hlin : 49726+J r+3*M r w+4=8388608*D r w := by
    dsimp [J,M,D]
    omega
  have hB :
      B+D r w=2^(2*M r w-21)*(J r+2) := by
    have hfactor : 8388608*(B+D r w)=
        8388608*(2^(2*M r w-21)*(J r+2)) := by
      calc
        _ = (49726+8388608*B)+J r+3*M r w+4 := by
          omega
        _ = 2^(2*M r w+2)*(J r+2) := hstop
        _ = 8388608*(2^(2*M r w-21)*(J r+2)) := by
          rw [hp]
          simp only [Nat.mul_assoc]
    omega
  have hdivPow : 65536 ∣ 2^(2*M r w-21) := by
    change 2^16 ∣ 2^(2*M r w-21)
    exact Nat.pow_dvd_pow 2 (by omega)
  obtain ⟨z,hz⟩ := hdivPow
  have hdivB : 65536 ∣ B+D r w := by
    refine ⟨z*(J r+2), ?_⟩
    rw [hB, hz]
    simp only [Nat.mul_assoc]
  have hQC : Q r B+C r w=1472137*(B+D r w) := by
    dsimp [Q,C,D]
    omega
  obtain ⟨z2,hz2⟩ := hdivB
  have hdivQ : 65536 ∣ Q r B+C r w := by
    refine ⟨1472137*z2, ?_⟩
    rw [hQC, hz2]
    omega
  exact Nat.mod_eq_zero_of_dvd hdivQ

/-- A concrete two-parameter H5 congruence class, with no huge powers
    in the finite test: all its C(r,w) residues equal 55453 modulo 2^16. -/
theorem C_coset_55453 (s t : Nat) :
    C (1024*s) (30+9216*s+65536*t)%65536=55453 := by
  dsimp [C]
  omega

/-- New *full original-source* H5 high-stop exclusion via ten forced
    inverse steps and a 16-bit double-parent E certificate. The stopping
    equation is the actual exact source transition equation. -/
theorem H5_even_source_coset (s t B : Nat)
    (hstop : (49726+8388608*B)+J (1024*s)+
      3*M (1024*s) (30+9216*s+65536*t)+4 =
      2^(2*M (1024*s) (30+9216*s+65536*t)+2)*(J (1024*s)+2)) :
    ¬ BB6.Agent3.CReach
      (2*J (1024*s)+1) (49726+8388608*B) := by
  let r := 1024*s
  let w := 30+9216*s+65536*t
  have hqPlus := highstop_mass_mod r w B hstop
  have hc := C_coset_55453 s t
  have hq : Q r B%65536=10083 := by
    rw [Nat.add_mod] at hqPlus
    omega
  intro hr
  have hE : BB6.Agent3.CReach (Eax r B) (Eay r B) := by
    simpa [Eax,Eay] using h5_stop_forces_E r w B hstop hr
  exact (E_q10083_source r B hq) hE

/-- The original 32-bit root filter entirely misses this entire
    two-parameter family; so does the accepted quarter-phase guard. -/
theorem root32_base30 :
    excluded 32 (stopResidue (J 0) (M 0 30))=false := by decide

theorem root32_lift (s t : Nat) :
    residue 32
      (stopResidue (J (1024*s)) (M (1024*s) (30+9216*s+65536*t))) =
    residue 32 (stopResidue (J 0) (M 0 30)) := by
  simp only [residue, stopResidue, J, M, Int.natCast_add, Int.natCast_mul,
    Int.cast_ofNat_Int]
  rw [Pair.mk.injEq]
  constructor
  · apply Int.emod_eq_emod_iff_emod_sub_eq_zero.mpr
    apply Int.emod_eq_zero_of_dvd
    refine ⟨(s:Int), ?_⟩
    change _=(4294967296:Int)*_
    omega
  · apply Int.emod_eq_emod_iff_emod_sub_eq_zero.mpr
    apply Int.emod_eq_zero_of_dvd
    refine ⟨-58*(s:Int)-384*(t:Int), ?_⟩
    change _=(4294967296:Int)*_
    omega

theorem root32_miss (s t : Nat) :
    excluded 32
      (stopResidue (J (1024*s)) (M (1024*s) (30+9216*s+65536*t)))=false := by
  unfold excluded
  rw [root32_lift]
  exact root32_base30

theorem quarter_miss (s t : Nat) :
    ¬ ((5*(1024*s)+3*(30+9216*s+65536*t)+4)%8=0 ∨
       (5*(1024*s)+3*(30+9216*s+65536*t)+17)%16=0 ∨
       ∃ z, z∈[26,48,51,56] ∧
         (37*(1024*s)+3*(30+9216*s+65536*t)+z)%64=0) := by
  rintro (h | h | ⟨z,hz,h⟩)
  · omega
  · omega
  · simp at hz
    rcases hz with h26 | h48 | h51 | h56 <;> subst z <;> omega

#print axioms highstop_mass_mod
#print axioms H5_even_source_coset
#print axioms root32_miss
#print axioms quarter_miss
end BB6.Agent34H5EvenStopCoset
