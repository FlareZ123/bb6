import JointC26
import Low14Source
import Low58Source
import Lean.Elab.Tactic.Omega

namespace BB6.Agent11C58

def lowAllowed (m : Nat) : Prop :=
  BB6.Agent23C26.lowAllowed m ∧ m%64≠58 ∧ m%256≠150

def highAllowed (j m : Nat) : Prop :=
  BB6.Agent23C26.highAllowed j m

private theorem low_bound (m : Nat) :
    3*m+4 ≤ 2^(2*m+3) := by
  induction m with
  | zero => decide
  | succ m ih =>
    have he : 2*(m+1)+3=(2*m+3)+2 := by omega
    rw [he,Nat.pow_add]
    simp only [show (2:Nat)^2=4 by decide]
    omega

/-- Machine C's exact blank-halting criterion with two new disjoint
    low-index infinite sectors removed. Both remaining parameter
    existentials are still unbounded and undecided. -/
theorem blank_halts_iff_c58_five_root : BB6.CReachBridge.RunHalts ↔
    (∃ m, lowAllowed m ∧
      BB6.Agent19Five.mixedFiveFastRootDecision 1
        (2^(2*m+3)-(3*m+4))=true) ∨
    (∃ j m, highAllowed j m ∧
      BB6.Agent19Five.mixedFiveFastRootDecision (2*j+3)
        (2^(2*m+2)*(j+3)-(j+3*m+5))=true) := by
  rw [BB6.Agent23C26.blank_halts_iff_c26_five_root]
  constructor
  · rintro (⟨m,hm,hroot⟩ | ⟨j,m,hm,hroot⟩)
    · let k := 2^(2*m+3)-(3*m+4)
      have hr : BB6.Agent3.CReach 1 k :=
        (BB6.Agent19Five.mixedFiveFastRootDecision_iff 1 k).mp hroot
      have hstop : k+3*m+4=2^(2*m+3) := by
        dsimp [k]
        have hc := Nat.sub_add_cancel (low_bound m)
        omega
      have hnot58 : m%64≠58 := by
        intro hm58
        exact BB6.Agent11C14.blank_no_low_m_58 m k hm58 hstop hr
      have hnot150 : m%256≠150 := by
        intro hm150
        exact BB6.Agent11C58.blank_no_low_m_150 m k hm150 hstop hr
      exact Or.inl ⟨m,⟨hm,hnot58,hnot150⟩,hroot⟩
    · exact Or.inr ⟨j,m,hm,hroot⟩
  · rintro (⟨m,⟨hm,_,_⟩,hroot⟩ | ⟨j,m,hm,hroot⟩)
    · exact Or.inl ⟨m,hm,hroot⟩
    · exact Or.inr ⟨j,m,hm,hroot⟩

/-- Every parameter of the new 150-mod-256 sector satisfies the
    earlier joint low filters (including C26), making this exclusion
    independent of their residue restrictions. -/
theorem old_low_admits_150 (r : Nat) :
    BB6.Agent23C26.lowAllowed (256*r+150) := by
  unfold BB6.Agent23C26.lowAllowed
    BB6.Agent11Joint.lowAllowed BB6.Agent3.jointLowAllowed
  omega

/-- Earlier ValSix low 128-divisibility pruning does not remove this family. -/
theorem old_128_filter_admits_150 (r : Nat) :
    ¬(128≤256*r+150 ∧ (256*r+150)%128=0) := by
  omega

#print axioms blank_halts_iff_c58_five_root
#print axioms old_low_admits_150
end BB6.Agent11C58
