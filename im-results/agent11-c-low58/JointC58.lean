import JointC26
import Low14Source
import Low58Source
import Rect58Source
import Lean.Elab.Tactic.Omega

namespace BB6.Agent11C58

def lowAllowed (m : Nat) : Prop :=
  BB6.Agent23C26.lowAllowed m ∧ m%64≠58 ∧ m%256≠150

def highAllowed (j m : Nat) : Prop :=
  BB6.Agent23C26.highAllowed j m ∧
    ¬(3≤m ∧ j%32=31 ∧ (j+3*m+5)%256=198)

private theorem low_bound (m : Nat) :
    3*m+4 ≤ 2^(2*m+3) := by
  induction m with
  | zero => decide
  | succ m ih =>
    have he : 2*(m+1)+3=(2*m+3)+2 := by omega
    rw [he,Nat.pow_add]
    simp only [show (2:Nat)^2=4 by decide]
    omega

private theorem high_margin_any (m : Nat) :
    3*m+5 ≤ 3*2^(2*m+2) := by
  induction m with
  | zero => decide
  | succ m ih =>
    have he : 2*(m+1)+2=(2*m+2)+2 := by omega
    rw [he,Nat.pow_add]
    simp only [show (2:Nat)^2=4 by decide]
    omega

private theorem high_bound (j m : Nat) :
    j+3*m+5 ≤ 2^(2*m+2)*(j+3) := by
  have hp : 1≤2^(2*m+2) := Nat.pow_pos (by decide)
  have hj : j≤2^(2*m+2)*j := by
    simpa only [Nat.one_mul] using Nat.mul_le_mul_right j hp
  have hm := high_margin_any m
  rw [Nat.mul_add]
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
    · let k := 2^(2*m+2)*(j+3)-(j+3*m+5)
      have hr : BB6.Agent3.CReach (2*j+3) k :=
        (BB6.Agent19Five.mixedFiveFastRootDecision_iff (2*j+3) k).mp hroot
      have hstop : k+j+3*m+5=2^(2*m+2)*(j+3) := by
        dsimp [k]
        have hc := Nat.sub_add_cancel (high_bound j m)
        omega
      have hnot : ¬(3≤m ∧ j%32=31 ∧ (j+3*m+5)%256=198) := by
        rintro ⟨hm3,hj31,hpair⟩
        exact BB6.Agent11C58Rect.blank_no_high_rect_58 j m k
          hm3 hj31 hpair hstop hr
      exact Or.inr ⟨j,m,⟨hm,hnot⟩,hroot⟩
  · rintro (⟨m,⟨hm,_,_⟩,hroot⟩ | ⟨j,m,⟨hm,_⟩,hroot⟩)
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

/-- Every member of an infinite genuine high stopping family passes all
    earlier Agent23/19/11/3 high parameter filters. Its removal by the
    new C58 rectangle is therefore genuinely additional to C26. -/
theorem old_high_admits_31_54 (r : Nat) :
    BB6.Agent23C26.highAllowed 31 (54+256*r) := by
  have hbase : BB6.Agent3.jointHighAllowed 31 (54+256*r) := by
    unfold BB6.Agent3.jointHighAllowed
    refine ⟨?_,?_,?_,?_,?_⟩ <;> omega
  have hrect : BB6.Agent3.jointHighRectAllowed 31 (54+256*r) := by
    unfold BB6.Agent3.jointHighRectAllowed
    exact ⟨hbase, by omega⟩
  have hdy : ∀ n, ¬(n+4≤2*(54+256*r)+2 ∧
      (31+3*(54+256*r)+3)%2^(n+4)=2^(n+2) ∧
      (2*31+3)%8=(if n%2=0 then 7 else 3)) := by
    intro n
    rintro ⟨_,_,hx⟩
    by_cases heven : n%2=0
    · simp [heven] at hx
    · simp [heven] at hx
  have h19 : BB6.Agent19Joint.highAllowed 31 (54+256*r) := by
    unfold BB6.Agent19Joint.highAllowed
    exact ⟨hrect,hdy,by omega,by omega,by omega,by omega⟩
  have h11 : BB6.Agent11Joint.highAllowed 31 (54+256*r) := by
    unfold BB6.Agent11Joint.highAllowed
    exact ⟨h19,by omega,by omega⟩
  have hfive : BB6.Agent19Five.highAllowed 31 (54+256*r) := by
    unfold BB6.Agent19Five.highAllowed
    exact ⟨h11,by omega⟩
  unfold BB6.Agent23C26.highAllowed
  refine ⟨hfive,?_⟩
  unfold BB6.Agent23C26.highForbidden
  omega

/-- All members of that previously allowed infinite high family are
    rejected by the new original-source rectangle condition. -/
theorem new_high_excludes_31_54 (r : Nat) :
    ¬ highAllowed 31 (54+256*r) := by
  intro h
  have hn := h.2
  apply hn
  omega

#print axioms blank_halts_iff_c58_five_root
#print axioms old_high_admits_31_54
#print axioms new_high_excludes_31_54
#print axioms old_low_admits_150
end BB6.Agent11C58
