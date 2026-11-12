import ValSixC58AllDepth
import CSixSeventhDiagonal
import Lean.Elab.Tactic.Omega

namespace BB6.Agent4SevenC58

/-- The four-class diagonal forces these exact low residues. -/
private theorem diagonal_residues (j m : Nat)
    (hj : j%512=319)
    (hpair : (3*m)%4096=(j+2879)%4096) :
    j%256=63 ∧ j%128=63 ∧ j%64=63 ∧ j%32=31 ∧
    j%16=15 ∧ j%8=7 ∧ j%4=3 ∧
    m%512=42 ∧ m%256=42 ∧ m%128=42 ∧ m%64=42 ∧
    m%32=10 ∧ m%16=10 ∧ m%8=2 ∧ m%4=2 := by
  have hdiv : 512 ∣ 4096 := by decide
  have h3m : (3*m)%512=126 := by
    calc
      (3*m)%512 = ((3*m)%4096)%512 := by
        symm
        exact Nat.mod_mod_of_dvd (3*m) hdiv
      _ = ((j+2879)%4096)%512 := by rw [hpair]
      _ = (j+2879)%512 := Nat.mod_mod_of_dvd (j+2879) hdiv
      _ = 126 := by omega
  have hm512 : m%512=42 := by omega
  omega

private theorem high_score_nonnegative (j m : Nat) :
    j+3*m+5 ≤ (2:Nat)^(2*m+2)*(j+3) := by
  have hP : 4*m+4 ≤ (2:Nat)^(2*m+2) :=
    BB6.Agent29New.power_linear_bound m
  have hp : 1 ≤ (2:Nat)^(2*m+2) :=
    Nat.pow_pos (by decide)
  have hj : j ≤ (2:Nat)^(2*m+2)*j := by
    simpa only [Nat.one_mul] using Nat.mul_le_mul_right j hp
  have hm : 3*m+5 ≤ 3*(2:Nat)^(2*m+2) := by omega
  rw [Nat.mul_add]
  omega

private theorem high_stop_identity (j m : Nat) :
    (2:Nat)^(2*m+2)*(j+3) - (j+3*m+5) + j+3*m+5 =
      (2:Nat)^(2*m+2)*(j+3) := by
  have h := Nat.sub_add_cancel (high_score_nonnegative j m)
  omega

/-- The Agent 4 six/seven diagonal is admitted by the complete
    source-certified ValSixFull+C58 high sieve, including its affine
    right-four exclusion. -/
theorem prior_c58_admits_six_seven_diagonal (j m : Nat)
    (hm : 7≤m) (hj : j%512=319)
    (hpair : (3*m)%4096=(j+2879)%4096) :
    BB6.Agent11C58AllDepth.highAllowed j m := by
  obtain ⟨hj256,hj128,hj64,hj32,hj16,hj8,hj4,
      hm512,hm256,hm128,hm64,hm32,hm16,hm8,hm4⟩ :=
    diagonal_residues j m hj hpair

  have hbase : BB6.Agent3.jointHighAllowed j m := by
    unfold BB6.Agent3.jointHighAllowed
    refine ⟨?_,?_,?_,?_,?_⟩ <;> omega
  have hrect : BB6.Agent3.jointHighRectAllowed j m := by
    unfold BB6.Agent3.jointHighRectAllowed
    exact ⟨hbase,by omega⟩

  have hdyadic : ∀ n, ¬(n+4≤2*m+2 ∧
      (j+3*m+3)%2^(n+4)=2^(n+2) ∧
      (2*j+3)%8=(if n%2=0 then 7 else 3)) := by
    intro n
    rintro ⟨_,_,hpar,hx⟩
    have hx1 : (2*j+3)%8=1 := by omega
    by_cases hn : n%2=0
    · simp [hn] at hx
      omega
    · simp [hn] at hx
      omega

  have h19 : BB6.Agent19Joint.highAllowed j m := by
    unfold BB6.Agent19Joint.highAllowed
    exact ⟨hrect,hdyadic,by omega,by omega,by omega,by omega⟩
  have hplus : BB6.Agent29Joint.highAllowedPlus j m := by
    unfold BB6.Agent29Joint.highAllowedPlus
    exact ⟨h19,by omega,by omega,by omega,by omega⟩
  have hvalThree : BB6.Agent3ValSix.highAllowedValSixThree j m := by
    unfold BB6.Agent3ValSix.highAllowedValSixThree
    unfold BB6.Agent3ValSix.highAllowedValSix
    exact ⟨⟨hplus,by omega,by omega⟩,by omega⟩
  have h11 : BB6.Agent11Joint.highAllowed j m := by
    unfold BB6.Agent11Joint.highAllowed
    exact ⟨h19,by omega,by omega⟩
  have hfive : BB6.Agent19Five.highAllowed j m := by
    unfold BB6.Agent19Five.highAllowed
    exact ⟨h11,by omega⟩

  let k := (2:Nat)^(2*m+2)*(j+3)-(j+3*m+5)
  have hstop : k+j+3*m+5=(2:Nat)^(2*m+2)*(j+3) := by
    simpa [k] using high_stop_identity j m
  have hpow4 : 4 ∣ (2:Nat)^(2*m+2) := by
    have hpow : (2:Nat)^2 ∣ (2:Nat)^(2*m+2) :=
      Nat.pow_dvd_pow 2 (by omega)
    simpa only [show (2:Nat)^2=4 by decide] using hpow
  have hprod4 : 4 ∣ (2:Nat)^(2*m+2)*(j+3) := by
    rcases hpow4 with ⟨q,hq⟩
    refine ⟨q*(j+3),?_⟩
    rw [hq]
    ac_rfl
  have hmod0 : (k+j+3*m+5)%4=0 := by
    rw [hstop]
    exact Nat.mod_eq_zero_of_dvd hprod4
  have hk4 : k%4=2 := by omega
  have hguard : ¬(4≤k ∧ k%2=0 ∧ ((2*j+3)+k)%4=1) := by omega
  have hnorm :
      BB6.Agent15.affineNormalize (2*j+3) k=(2*j+3,k) := by
    simp [BB6.Agent15.affineNormalize,hguard]
  have hright4 :
      (BB6.Agent15.affineNormalize (2*j+3) k).2≠4 := by
    rw [hnorm]
    omega

  have hfull : BB6.Agent3ValSix.highAllowedValSixFull j m := by
    unfold BB6.Agent3ValSix.highAllowedValSixFull
    exact ⟨hvalThree,hfive,by omega,by omega,by omega,hright4⟩
  have hc58 : BB6.Agent11C58ValSix.highAllowed j m := by
    unfold BB6.Agent11C58ValSix.highAllowed
    exact ⟨hfull,by omega⟩
  unfold BB6.Agent11C58AllDepth.highAllowed
  refine ⟨hc58,?_⟩
  intro r
  rintro ⟨_,_,_,hmr,hres⟩
  have hodd : (2*r+3)%4=1 ∨ (2*r+3)%4=3 := by omega
  omega

/-- A concrete infinite progression survives every preceding
    ValSixFull+C58 all-depth restriction. -/
theorem prior_c58_admits_concrete_infinite_family (t : Nat) :
    BB6.Agent11C58AllDepth.highAllowed (1343+4096*t) 42 := by
  apply prior_c58_admits_six_seven_diagonal
  · omega
  · omega
  · omega

/-- The stronger exact high predicate removes the whole six/seven
    source-certified diagonal, without changing the low branch. -/
def highAllowed (j m : Nat) : Prop :=
  BB6.Agent11C58AllDepth.highAllowed j m ∧
  ¬(7≤m ∧ j%512=319 ∧
    (3*m)%4096=(j+2879)%4096)

/-- Exact original-source Machine C blank-halting iff after adding
    Agent 4's independent infinite six/seven high-stop exclusion.
    The remaining parameter existentials are still unbounded. -/
theorem blank_halts_iff_c58_all_depth_six_seven :
    BB6.CReachBridge.RunHalts ↔
      (∃ m, BB6.Agent11C58ValSix.lowAllowed m ∧
        BB6.Agent3ValSix.valSixMixedRootDecision
          1 (2^(2*m+3)-(3*m+4))=true) ∨
      (∃ j m, highAllowed j m ∧
        BB6.Agent3ValSix.valSixMixedRootDecision (2*j+3)
          (2^(2*m+2)*(j+3)-(j+3*m+5))=true) := by
  rw [BB6.Agent11C58AllDepth.blank_halts_iff_joint_c58_all_depth]
  constructor
  · rintro (hlow | ⟨j,m,hprior,hroot⟩)
    · exact Or.inl hlow
    · let k := (2:Nat)^(2*m+2)*(j+3)-(j+3*m+5)
      have hreach : BB6.Agent3.CReach (2*j+3) k :=
        (BB6.Agent3ValSix.valSixMixedRootDecision_iff (2*j+3) k).mp hroot
      have hnot : ¬(7≤m ∧ j%512=319 ∧
          (3*m)%4096=(j+2879)%4096) := by
        rintro ⟨hm,hj,hpair⟩
        obtain ⟨time,hrun⟩ := hreach
        have hstop : k+j+3*m+5=(2:Nat)^(2*m+2)*(j+3) := by
          simpa [k] using high_stop_identity j m
        exact (BB6.Agent4Seven.high_stop_six_seven_diagonal
          j m k time hm hj hpair hstop) hrun
      exact Or.inr ⟨j,m,⟨hprior,hnot⟩,hroot⟩
  · rintro (hlow | ⟨j,m,⟨hprior,_⟩,hroot⟩)
    · exact Or.inl hlow
    · exact Or.inr ⟨j,m,hprior,hroot⟩

/-- The explicit infinite progression is excluded by the new exact
    high predicate, despite being admitted by the prior one. -/
theorem concrete_family_removed (t : Nat) :
    ¬highAllowed (1343+4096*t) 42 := by
  intro h
  exact h.2 ⟨by omega,by omega,by omega⟩

#print axioms prior_c58_admits_six_seven_diagonal
#print axioms prior_c58_admits_concrete_infinite_family
#print axioms blank_halts_iff_c58_all_depth_six_seven
#print axioms concrete_family_removed

end BB6.Agent4SevenC58
