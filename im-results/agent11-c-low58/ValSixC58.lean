import ValSixJointFull
import Low14Source
import Low58Source
import Rect58Source
import Lean.Elab.Tactic.Omega

namespace BB6.Agent11C58ValSix

def lowAllowed (m : Nat) : Prop :=
  BB6.Agent3ValSix.lowAllowedValSixFull m ∧
    m%64≠58 ∧ m%256≠150

def highAllowed (j m : Nat) : Prop :=
  BB6.Agent3ValSix.highAllowedValSixFull j m ∧
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

private theorem high_bound (j m : Nat) :
    j+3*m+5 ≤ 2^(2*m+2)*(j+3) := by
  have hm : 4*m+4 ≤ 2^(2*m+2) := BB6.Agent29New.power_linear_bound m
  have hp : 1 ≤ 2^(2*m+2) := Nat.pow_pos (by decide)
  have hj : j ≤ 2^(2*m+2)*j := by
    simpa only [Nat.one_mul] using Nat.mul_le_mul_right j hp
  rw [Nat.mul_add]
  omega

/-- Source-certified new sector exclusions combined with the full
    independent ValSix high sieve and exact root evaluator. -/
theorem blank_halts_iff_joint_val_six_c58 :
    BB6.CReachBridge.RunHalts ↔
      (∃ m, lowAllowed m ∧
        BB6.Agent3ValSix.valSixMixedRootDecision 1
          (2^(2*m+3)-(3*m+4))=true) ∨
      (∃ j m, highAllowed j m ∧
        BB6.Agent3ValSix.valSixMixedRootDecision (2*j+3)
          (2^(2*m+2)*(j+3)-(j+3*m+5))=true) := by
  rw [BB6.Agent3ValSix.blank_halts_iff_joint_val_six_full]
  constructor
  · rintro (⟨m,hm,hroot⟩ | ⟨j,m,hm,hroot⟩)
    · let k := 2^(2*m+3)-(3*m+4)
      have hr : BB6.Agent3.CReach 1 k :=
        (BB6.Agent3ValSix.valSixMixedRootDecision_iff 1 k).mp hroot
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
        (BB6.Agent3ValSix.valSixMixedRootDecision_iff (2*j+3) k).mp hroot
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

/-- An explicit infinite high family omitted by the pre-existing
    ValSixFull sieve: no finite sample or truncation is involved. -/
theorem prior_val_six_full_admits_high_31_54 (r : Nat) :
    BB6.Agent3ValSix.highAllowedValSixFull 31 (54+256*r) := by
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
  have h29 : BB6.Agent29Joint.highAllowedPlus 31 (54+256*r) := by
    unfold BB6.Agent29Joint.highAllowedPlus
    exact ⟨h19,by omega,by omega,by omega,by omega⟩
  have hval : BB6.Agent3ValSix.highAllowedValSixThree 31 (54+256*r) := by
    unfold BB6.Agent3ValSix.highAllowedValSixThree
      BB6.Agent3ValSix.highAllowedValSix
    exact ⟨⟨h29,by omega,by omega⟩,by omega⟩
  have h11 : BB6.Agent11Joint.highAllowed 31 (54+256*r) := by
    unfold BB6.Agent11Joint.highAllowed
    exact ⟨h19,by omega,by omega⟩
  have hfive : BB6.Agent19Five.highAllowed 31 (54+256*r) := by
    unfold BB6.Agent19Five.highAllowed
    exact ⟨h11,by omega⟩
  let m := 54+256*r
  let k := 2^(2*m+2)*(31+3)-(31+3*m+5)
  have hstop : k+31+3*m+5=2^(2*m+2)*(31+3) := by
    dsimp [k]
    have hc := Nat.sub_add_cancel (high_bound 31 m)
    omega
  have hkmod : k%4=2 := by
    have hpow4 : 4 ∣ (2:Nat)^(2*m+2) := by
      have hd : (2:Nat)^2 ∣ (2:Nat)^(2*m+2) :=
        Nat.pow_dvd_pow 2 (by omega)
      simpa only [show (2:Nat)^2=4 by decide] using hd
    rcases hpow4 with ⟨z,hz⟩
    rw [hz] at hstop
    dsimp [m] at hstop
    omega
  have hkbig : 7≤k := BB6.Agent15.second_halt_k_ge_seven 31 m k hstop
  have hguard : ¬(4≤k ∧ k%2=0 ∧ ((2*31+3)+k)%4=1) := by
    omega
  have hnorm : BB6.Agent15.affineNormalize (2*31+3) k =
      (2*31+3,k) := by
    simp [BB6.Agent15.affineNormalize,hguard]
  have hright : (BB6.Agent15.affineNormalize
        (2*31+3)
        (2^(2*m+2)*(31+3)-(31+3*m+5))).2≠4 := by
    rw [hnorm]
    exact ne_of_gt (by omega : 4<k)
  unfold BB6.Agent3ValSix.highAllowedValSixFull
  refine ⟨hval,hfive,by omega,by omega,by omega,?_⟩
  simpa [m,k] using hright

theorem new_val_six_c58_rejects_high_31_54 (r : Nat) :
    ¬ highAllowed 31 (54+256*r) := by
  intro hh
  apply hh.2
  omega

#print axioms blank_halts_iff_joint_val_six_c58
#print axioms prior_val_six_full_admits_high_31_54
end BB6.Agent11C58ValSix
