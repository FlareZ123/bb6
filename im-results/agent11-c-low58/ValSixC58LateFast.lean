import ValSixC58Late
import HighThreeLateGateFast
import Lean.Elab.Tactic.Omega

namespace BB6.Agent11LateFastWrapper

/-- The previous C58/ValSix criterion, strengthened by the exact
    arbitrary-depth three-cone filter. The filter is executable through
    the unique valuation candidate in HighThreeLateGateFast.lean. -/
def highAllowed (j m : Nat) : Prop :=
  BB6.Agent11C58Boolean.highAllowed j m ∧
  BB6.Agent11LateDepthGate.allowedBool j m = true

private theorem high_bound (j m : Nat) :
    j+3*m+5 ≤ 2^(2*m+2)*(j+3) := by
  have hm : 4*m+4 ≤ 2^(2*m+2) :=
    BB6.Agent29New.power_linear_bound m
  have hp : 1 ≤ 2^(2*m+2) := Nat.pow_pos (by decide)
  have hj : j ≤ 2^(2*m+2)*j := by
    simpa only [Nat.one_mul] using Nat.mul_le_mul_right j hp
  rw [Nat.mul_add]
  omega

/-- Lossless original-source Machine C halting iff with every
    arbitrary-depth late three-cone target removed. The remaining
    low/high parameter existentials are still unbounded. -/
theorem blank_halts_iff_c58_all_depth_late_fast :
    BB6.CReachBridge.RunHalts ↔
      (∃ m, BB6.Agent11C58ValSix.lowAllowed m ∧
        BB6.Agent3ValSix.valSixMixedRootDecision 1
          (2^(2*m+3)-(3*m+4))=true) ∨
      (∃ j m, highAllowed j m ∧
        BB6.Agent3ValSix.valSixMixedRootDecision (2*j+3)
          (2^(2*m+2)*(j+3)-(j+3*m+5))=true) := by
  rw [BB6.Agent11C58Boolean.blank_halts_iff_c58_all_depth_boolean]
  constructor
  · rintro (hlow | ⟨j,m,hprior,hroot⟩)
    · exact Or.inl hlow
    · let k := 2^(2*m+2)*(j+3)-(j+3*m+5)
      have hreach : BB6.Agent3.CReach (2*j+3) k :=
        (BB6.Agent3ValSix.valSixMixedRootDecision_iff (2*j+3) k).mp hroot
      have hstop : k+j+3*m+5=2^(2*m+2)*(j+3) := by
        dsimp [k]
        have hc := Nat.sub_add_cancel (high_bound j m)
        omega
      have hgate : BB6.Agent11LateDepthGate.allowedBool j m = true := by
        apply (BB6.Agent11LateDepthGate.allowedBool_iff j m).mpr
        intro r hr
        rcases hr with ⟨hrmin,hm3,hm4,hmod,hsize⟩
        exact (BB6.Agent11HighThreeLate.late_high_no_blank
          r j m k hrmin hm3 hm4 hstop hmod hsize) hreach
      exact Or.inr ⟨j,m,⟨hprior,hgate⟩,hroot⟩
  · rintro (hlow | ⟨j,m,⟨hprior,hgate⟩,hroot⟩)
    · exact Or.inl hlow
    · exact Or.inr ⟨j,m,hprior,hroot⟩

/-- The known m=3, j=372 (mod 512) family is admitted by the old
    C58/ValSix sieve and rejected by this general late-depth filter. -/
theorem late_gate_strict_family (t : Nat) :
    BB6.Agent11C58Boolean.highAllowed (372+512*t) 3 ∧
      ¬highAllowed (372+512*t) 3 := by
  have hprior :=
    (BB6.Agent11C58Late.late_high_new_strict_family t).1
  have hk : BB6.Agent11LateDepthGate.stopK (372+512*t) 3 + 2 =
      95616+130560*t := by
    dsimp [BB6.Agent11LateDepthGate.stopK]
    omega
  have hmod :
      (BB6.Agent11LateDepthGate.stopK (372+512*t) 3+2)%2^(7+2)=3*2^7 := by
    rw [hk]
    have hcoeff : 130560=512*255 := by decide
    rw [hcoeff]
    omega
  have hsize :
      7*2^7≤BB6.Agent11LateDepthGate.stopK (372+512*t) 3+2 := by
    rw [hk]
    omega
  have hgate : BB6.Agent11LateDepthGate.candidateAllowedBool
      (372+512*t) 3 = true := by
    apply (BB6.Agent11LateDepthGate.candidateAllowedBool_iff _ _).mpr
    refine ⟨7,by decide,by decide,by decide,hmod,hsize⟩
  refine ⟨hprior,?_⟩
  unfold highAllowed BB6.Agent11LateDepthGate.allowedBool
  simp [hgate]

#print axioms blank_halts_iff_c58_all_depth_late_fast
#print axioms late_gate_strict_family
end BB6.Agent11LateFastWrapper
