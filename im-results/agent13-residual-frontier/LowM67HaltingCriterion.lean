import CThreeSixAllCriterion
import U16AllSource
import Lean.Elab.Tactic.Omega

namespace BB6.Agent13Low16Joint

/-- The five new source-certified low-stop parameter cylinders, in m
    coordinates rather than in z where m=512*z+67. These are pairwise
    disjoint m-residue classes and lie entirely beyond the earlier
    direct six-sector exclusions. -/
def low16Forbidden (m : Nat) : Prop :=
  m%8192=6723 ∨ m%32768=2627 ∨ m%16384=12867 ∨
  m%65536=4675 ∨ m%65536=10819

def lowAllowedSource16 (m : Nat) : Prop :=
  BB6.Agent11SixAll.lowAllowed m ∧ ¬low16Forbidden m

private theorem low_power_bound (m : Nat) :
    3*m+4 ≤ 2^(2*m+3) := by
  induction m with
  | zero => decide
  | succ m ih =>
      have he : 2*(m+1)+3=(2*m+3)+2 := by omega
      rw [he,Nat.pow_add]
      simp only [show (2:Nat)^2=4 by decide]
      omega

private theorem forbidden_of_z (m : Nat)
    (hf : low16Forbidden m) :
    ∃ z, m=512*z+67 ∧
      (z%16=13 ∨ z%64=5 ∨ z%32=25 ∨
        z%128=9 ∨ z%128=21) := by
  let z := m/512
  have hm512 : m%512=67 := by
    rcases hf with h|h|h|h|h <;> simp only [low16Forbidden] at * <;> omega
  have hm : m=512*z+67 := by
    have h := Nat.mod_add_div m 512
    dsimp [z]
    omega
  refine ⟨z,hm,?_⟩
  rcases hf with h13|h5|h25|h9|h21
  · left
    rw [hm] at h13
    omega
  · right; left
    rw [hm] at h5
    omega
  · right; right; left
    rw [hm] at h25
    omega
  · right; right; right; left
    rw [hm] at h9
    omega
  · right; right; right; right
    rw [hm] at h21
    omega

/-- Lossless, truly original-source halting criterion after removing all
    five newly source-forbidden low parameter cylinders. The residual
    low and high existentials remain unbounded; Machine C is not decided. -/
theorem blank_halts_iff_six_low16 :
    BB6.CReachBridge.RunHalts ↔
      (∃ m, lowAllowedSource16 m ∧
        BB6.Agent11SixForced.sixForcedRootDecision 1
          (2^(2*m+3)-(3*m+4))=true) ∨
      (∃ j m, BB6.Agent11SixAll.highAllowed j m ∧
        BB6.Agent11SixForced.sixForcedRootDecision (2*j+3)
          (2^(2*m+2)*(j+3)-(j+3*m+5))=true) := by
  rw [BB6.Agent11SixAll.blank_halts_iff_six_both]
  constructor
  · rintro (⟨m,hprior,hroot⟩ | ⟨j,m,hprior,hroot⟩)
    · let k := 2^(2*m+3)-(3*m+4)
      have hr : BB6.Agent3.CReach 1 k :=
        (BB6.Agent11SixForced.sixForcedRootDecision_iff 1 k).mp hroot
      have hstop : k+3*m+4=2^(2*m+3) := by
        dsimp [k]
        have hb := Nat.sub_add_cancel (low_power_bound m)
        omega
      have hnon : ¬low16Forbidden m := by
        intro hf
        obtain ⟨z,hm,hz⟩ := forbidden_of_z m hf
        exact (BB6.Agent13LowM67Sixteen.low_stop_sixteen_mod128_unreachable
          z m k hm hz hstop) hr
      exact Or.inl ⟨m,⟨hprior,hnon⟩,hroot⟩
    · exact Or.inr ⟨j,m,hprior,hroot⟩
  · rintro (⟨m,⟨hprior,_⟩,hroot⟩ | ⟨j,m,hprior,hroot⟩)
    · exact Or.inl ⟨m,hprior,hroot⟩
    · exact Or.inr ⟨j,m,hprior,hroot⟩

#print axioms forbidden_of_z
#print axioms blank_halts_iff_six_low16
end BB6.Agent13Low16Joint
