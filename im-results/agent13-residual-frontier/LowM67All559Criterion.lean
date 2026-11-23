import LowM67All523Criterion
import LowM67All559Source
import Lean.Elab.Tactic.Omega

namespace BB6.Agent13Low559Joint

/-- Complete source-certified low exclusions, including eight new all-time
    source cylinders beyond the earlier 65/512 criterion. -/
def lowAllowedSource559 (m : Nat) : Prop :=
  BB6.Agent13Low523Joint.lowAllowedSource523 m ∧
  m%131072≠84547 ∧
  m%262144≠53827 ∧
  m%524288≠240195 ∧
  m%524288≠444995 ∧
  m%524288≠299587

private theorem low_power_bound (m : Nat) :
    3*m+4 ≤ 2^(2*m+3) := by
  induction m with
  | zero => decide
  | succ m ih =>
      have he : 2*(m+1)+3=(2*m+3)+2 := by omega
      rw [he,Nat.pow_add]
      simp only [show (2:Nat)^2=4 by decide]
      omega

/-- Lossless original-machine blank-halt criterion narrowing the exact
    low-stop parameter family m=512*z+67 by 559/4096 excluded z residue
    classes. The high-stop original-source existential remains unchanged,
    and neither Machine C nor BB(6) is decided by this theorem. -/
theorem blank_halts_iff_six_low559 :
    BB6.CReachBridge.RunHalts ↔
      (∃ m, lowAllowedSource559 m ∧
        BB6.Agent11SixForced.sixForcedRootDecision 1
          (2^(2*m+3)-(3*m+4))=true) ∨
      (∃ j m, BB6.Agent11SixAll.highAllowed j m ∧
        BB6.Agent11SixForced.sixForcedRootDecision (2*j+3)
          (2^(2*m+2)*(j+3)-(j+3*m+5))=true) := by
  rw [BB6.Agent13Low523Joint.blank_halts_iff_six_low523]
  constructor
  · rintro (⟨m,hprior,hroot⟩ | ⟨j,m,hprior,hroot⟩)
    · let k := 2^(2*m+3)-(3*m+4)
      have hr : BB6.Agent3.CReach 1 k :=
        (BB6.Agent11SixForced.sixForcedRootDecision_iff 1 k).mp hroot
      have hstop : k+3*m+4=2^(2*m+3) := by
        dsimp [k]
        have hb := Nat.sub_add_cancel (low_power_bound m)
        omega
      have hnon165 : m%131072≠84547 := by
        intro hm0
        let z := m/512
        have hm : m=512*z+67 := by
          have hh := Nat.mod_add_div m 512
          dsimp [z]
          omega
        have hz : z%256=165 := by
          rw [hm] at hm0
          omega
        exact (BB6.Agent13FiveD23.low_stop_m67_z165_mod256_unreachable
          z m k hm hz hstop) hr
      have hnon105 : m%262144≠53827 := by
        intro hm0
        let z := m/512
        have hm : m=512*z+67 := by
          have hh := Nat.mod_add_div m 512
          dsimp [z]
          omega
        have hz : z%512=105 := by
          rw [hm] at hm0
          omega
        exact (BB6.Agent13FiveD23.low_stop_m67_z105_mod512_unreachable
          z m k hm hz hstop) hr
      have hnon469 : m%524288≠240195 := by
        intro hm0
        let z := m/512
        have hm : m=512*z+67 := by
          have hh := Nat.mod_add_div m 512
          dsimp [z]
          omega
        have hz : z%1024=469 := by
          rw [hm] at hm0
          omega
        exact (BB6.Agent13FiveD23.low_stop_m67_z469_mod1024_unreachable
          z m k hm hz hstop) hr
      have hnon869 : m%524288≠444995 := by
        intro hm0
        let z := m/512
        have hm : m=512*z+67 := by
          have hh := Nat.mod_add_div m 512
          dsimp [z]
          omega
        have hz : z%1024=869 := by
          rw [hm] at hm0
          omega
        exact (BB6.Agent13FiveD23.low_stop_m67_z869_mod1024_unreachable
          z m k hm hz hstop) hr
      have hnon585 : m%524288≠299587 := by
        intro hm0
        let z := m/512
        have hm : m=512*z+67 := by
          have hh := Nat.mod_add_div m 512
          dsimp [z]
          omega
        have hz : z%1024=585 := by
          rw [hm] at hm0
          omega
        exact (BB6.Agent13FiveD23.low_stop_m67_z585_mod1024_unreachable
          z m k hm hz hstop) hr
      exact Or.inl ⟨m,⟨hprior,hnon165,hnon105,hnon469,hnon869,hnon585⟩,hroot⟩
    · exact Or.inr ⟨j,m,hprior,hroot⟩
  · rintro (⟨m,⟨hprior,_,_,_,_,_⟩,hroot⟩ | ⟨j,m,hprior,hroot⟩)
    · exact Or.inl ⟨m,hprior,hroot⟩
    · exact Or.inr ⟨j,m,hprior,hroot⟩

#print axioms blank_halts_iff_six_low559
end BB6.Agent13Low559Joint
