import LowM67All559Criterion
import LowM67Z7Source
import Lean.Elab.Tactic.Omega

/-!
# Lossless Machine C blank-halting equivalence excluding 1327 / 4096
residues on the m = 512 z + 67 necessary low-stop family.

The original source CReach rooted at (5,1), source target arithmetic,
and high-stop branch are unchanged. This only strengthens necessary
conditions for one unbounded low branch; it is NOT a halt/nonhalt verdict.
-/

namespace BB6.Agent8CLow1327

/-- The source-only 559/4096 predicate, with two additional mutually
disjoint source-certified prohibitions: z=2 (mod 8), z=7 (mod 16).
These remove respectively 512/4096 and 256/4096 new residue classes. -/
def lowAllowedSource1327 (m : Nat) : Prop :=
  BB6.Agent13Low559Joint.lowAllowedSource559 m ∧
  m%4096≠1091 ∧ m%8192≠3651

private theorem low_power_bound (m : Nat) :
    3*m+4 ≤ 2^(2*m+3) := by
  induction m with
  | zero => decide
  | succ m ih =>
      have he : 2*(m+1)+3=(2*m+3)+2 := by omega
      rw [he,Nat.pow_add]
      simp only [show (2:Nat)^2=4 by decide]
      omega

/-- Exact original blank-halt iff, preserving all remaining low and high
existential witnesses; the new excluded parameters cannot be genuine
reachable low stopping targets for any section time. -/
theorem blank_halts_iff_six_low1327 :
    BB6.CReachBridge.RunHalts ↔
      (∃ m, lowAllowedSource1327 m ∧
        BB6.Agent11SixForced.sixForcedRootDecision 1
          (2^(2*m+3)-(3*m+4))=true) ∨
      (∃ j m, BB6.Agent11SixAll.highAllowed j m ∧
        BB6.Agent11SixForced.sixForcedRootDecision (2*j+3)
          (2^(2*m+2)*(j+3)-(j+3*m+5))=true) := by
  rw [BB6.Agent13Low559Joint.blank_halts_iff_six_low559]
  constructor
  · rintro (⟨m,hprior,hroot⟩ | ⟨j,m,hprior,hroot⟩)
    · let k := 2^(2*m+3)-(3*m+4)
      have hr : BB6.Agent3.CReach 1 k :=
        (BB6.Agent11SixForced.sixForcedRootDecision_iff 1 k).mp hroot
      have hstop : k+3*m+4=2^(2*m+3) := by
        dsimp [k]
        have hb := Nat.sub_add_cancel (low_power_bound m)
        omega
      have hnon2 : m%4096≠1091 := by
        intro hm0
        let z := m/512
        have hm : m=512*z+67 := by
          have hh := Nat.mod_add_div m 512
          dsimp [z]
          omega
        have hz : z%8=2 := by
          rw [hm] at hm0
          omega
        exact (BB6.Agent8CLowZ2.low_stop_m67_z2_mod8_unreachable
          z m k hm hz hstop) hr
      have hnon7 : m%8192≠3651 := by
        intro hm0
        let z := m/512
        have hm : m=512*z+67 := by
          have hh := Nat.mod_add_div m 512
          dsimp [z]
          omega
        have hz : z%16=7 := by
          rw [hm] at hm0
          omega
        exact (BB6.Agent8CLowZ7.low_stop_m67_z7_mod16_unreachable
          z m k hm hz hstop) hr
      exact Or.inl ⟨m,⟨hprior,hnon2,hnon7⟩,hroot⟩
    · exact Or.inr ⟨j,m,hprior,hroot⟩
  · rintro (⟨m,⟨hprior,_,_⟩,hroot⟩ | ⟨j,m,hprior,hroot⟩)
    · exact Or.inl ⟨m,hprior,hroot⟩
    · exact Or.inr ⟨j,m,hprior,hroot⟩

#print axioms blank_halts_iff_six_low1327
end BB6.Agent8CLow1327
