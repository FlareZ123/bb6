import CapPositiveGate
import CapNegativeExitCore

namespace CapSieve

/-- The entire band domain in Q coordinates. -/
def ValidQ (k q : Nat) : Prop := k+6≤q ∧ q≤2*P k+k+2 ∧ q%2=k%2

/-- Positive W sector, in Q coordinates. -/
def PosQ (k q : Nat) : Prop := k+6≤q ∧ q≤2*P k-2 ∧ q%2=k%2

theorem pos_valid {k q : Nat} (h : PosQ k q) : ValidQ k q := by
  unfold PosQ ValidQ at *
  omega

def negQ (k w : Nat) : Nat := (4*P k+w-3)/2

def negWeight (k q : Nat) : Nat := 2*q+3-4*P k

theorem negQ_eq {k w : Nat} (hv : CapNegative.Valid k w) :
    2*negQ k w+3=4*P k+w := by
  have hp := p_ge k
  unfold negQ CapNegative.Valid at *
  omega

theorem negQ_valid {k w : Nat} (hv : CapNegative.Valid k w) :
    ValidQ k (negQ k w) ∧ 2*P k-1≤negQ k w := by
  have he := negQ_eq hv
  have hp := p_ge k
  unfold ValidQ CapNegative.Valid at *
  omega

theorem weight_valid {k q : Nat} (hv : ValidQ k q) (hneg : 2*P k-1≤q) :
    CapNegative.Valid k (negWeight k q) := by
  have hp := p_ge k
  unfold ValidQ CapNegative.Valid negWeight at *
  omega

theorem negQ_of_weight {k q : Nat} (hv : ValidQ k q) (hneg : 2*P k-1≤q) :
    negQ k (negWeight k q)=q := by
  have h := negQ_eq (weight_valid hv hneg)
  unfold negWeight at h ⊢
  have hp := p_ge k
  omega

/-- No same-band multiplication can follow a negative entry. -/
theorem band_last_negative {k w : Nat} (hv : CapNegative.Valid k w) :
    bandLastQ k (negQ k w)=negQ k w := by
  obtain ⟨hq,hneg⟩ := negQ_valid hv
  have hp := p_ge k
  have hqpos : 0<negQ k w := by unfold ValidQ at hq; omega
  have hqhi : negQ k w≤2*P k+k+2 := hq.2.1
  have hc : bandCount k (negQ k w)=0 := by
    unfold bandCount
    apply CapMacro.triple_window_unique hqpos
    · exact CapMacro.tripleCount_spec hqpos hqhi
    · simp; omega
  simp [bandLastQ,hc]

/-- All four forward events on the negative sector in one coordinate. -/
theorem band_macro_negative {k w : Nat} (hv : CapNegative.Valid k w) :
    bandMacro k (negQ k w)=
      if w=2*k+3 then none
      else if w=2*k+7 then some (k+1,3*k+15)
      else if 3*w≤2*k+9 then some (k+1,negQ (k+1) (3*w))
      else some (k+2,(3*w+3)/2) := by
  have he := negQ_eq hv
  have hp := p_ge k
  unfold bandMacro
  dsimp
  rw [band_last_negative hv]
  by_cases ht : w=2*k+3
  · rw [if_pos ht,if_pos (by omega : negQ k w=2*P k+k)]
  · rw [if_neg ht,if_neg (by omega : negQ k w≠2*P k+k)]
    by_cases hs : w=2*k+7
    · rw [if_pos hs,if_pos (by omega : negQ k w=2*P k+k+2)]
    · rw [if_neg hs,if_neg (by omega : negQ k w≠2*P k+k+2)]
      by_cases hd : 3*w≤2*k+9
      · rw [if_pos hd,if_pos (by omega : 3*negQ k w≤6*P k+k)]
        have hnext := negQ_eq (CapNegative.step_valid hv hd)
        rw [p_succ] at hnext
        have h : 3*negQ k w+3-2*P k=negQ (k+1) (3*w) := by omega
        rw [h]
      · rw [if_neg hd,if_neg (by omega : ¬3*negQ k w≤6*P k+k)]
        have h : 3*negQ k w+6-6*P k=(3*w+3)/2 := by omega
        rw [h]

theorem special_return_positive (k : Nat) : PosQ (k+1) (3*k+15) := by
  have hp := p_ge k
  unfold PosQ
  rw [p_succ]
  omega

theorem skip_return_positive {k w : Nat} (hv : CapNegative.Valid k w)
    (ht : w≠2*k+3) (hs : w≠2*k+7) (hd : 2*k+9<3*w) :
    PosQ (k+2) ((3*w+3)/2) := by
  have hp := p_ge k
  have hp2 : P (k+2)=4*P k := by
    rw [show k+2=(k+1)+1 by omega,p_succ,p_succ]; omega
  unfold PosQ CapNegative.Valid at *
  rw [hp2]
  omega

theorem negative_event_band (k w : Nat) : k≤(CapNegative.event k w).1 := by
  unfold CapNegative.event
  dsimp
  omega

/-- Both nonhalting negative exits return to the positive sector, with a
    strictly higher band. -/
theorem negative_event_return {k w j q : Nat} (hv : CapNegative.Valid k w)
    (he : (CapNegative.event k w).2=some (j,q)) :
    (CapNegative.event k w).1<j ∧ PosQ j q := by
  have h := CapNegative.stop_spec hv
  unfold CapNegative.event at he ⊢
  dsimp at h he ⊢
  generalize CapNegative.stopCount k w = n at *
  generalize k+n = b at *
  generalize 3^n*w = v at *
  by_cases ht : v=2*b+3
  · simp [ht] at he
  · rw [if_neg ht] at he
    by_cases hs : v=2*b+7
    · rw [if_pos hs] at he
      obtain ⟨rfl,rfl⟩ := Prod.mk.inj (Option.some.inj he)
      exact ⟨by omega,special_return_positive b⟩
    · rw [if_neg hs] at he
      obtain ⟨rfl,rfl⟩ := Prod.mk.inj (Option.some.inj he)
      exact ⟨by omega,skip_return_positive h.1 ht hs (by rcases h.2 with h|h|h <;> omega)⟩

/-- An exceptional positive exit enters a valid negative state, with
    the exact 3-adic unit phase imposed by its source band. -/
theorem entry_weight {k q : Nat} (hv : PosQ k q)
    (hf : positiveNext k q<k+7) :
    CapNegative.Valid k (2*positiveNext k q-3) ∧
      (2*positiveNext k q-3)%3=2^k%3 := by
  have hq : 0<q := by unfold PosQ at hv; omega
  have hb := positive_next_bounds hq hv.2.1
  have he := positive_next_equation hq hv.2.1
  have hpar := positive_next_parity hq hv.2.1 hv.2.2
  have hdiv : positiveProduct k q%3=0 := by
    unfold positiveProduct
    rw [Nat.pow_succ,show 3^(positiveCount k q)*3*q=3*(3^(positiveCount k q)*q) by ac_rfl]
    omega
  unfold P at he
  unfold CapNegative.Valid
  omega

/-- The first failed relaxed gate ends the same-band run at the actual
    negative state; the original macro therefore has the same event. -/
theorem positive_fail_macro {k q : Nat} (hv : PosQ k q)
    (hf : positiveNext k q<k+7) :
    bandMacro k q=bandMacro k (negQ k (2*positiveNext k q-3)) := by
  have hq : 0<q := by unfold PosQ at hv; omega
  obtain ⟨hlo,hhi,hUlo,hUhi,hU⟩ := positive_product_spec hq hv.2.1
  have he := positive_next_equation hq hv.2.1
  have hb := positive_next_bounds hq hv.2.1
  have hpar := positive_next_parity hq hv.2.1 hv.2.2
  have hp := p_ge k
  have hn := (entry_weight hv hf).1
  have hneg := negQ_eq hn
  have hUeq : negQ k (2*positiveNext k q-3)=positiveProduct k q := by omega
  have hc : bandCount k q=positiveCount k q+1 := by
    unfold bandCount
    apply CapMacro.triple_window_unique hq
    · exact CapMacro.tripleCount_spec hq (by have := hv.2.1; omega)
    · change positiveProduct k q≤2*P k+k+2 ∧ 2*P k+k+2<3^(positiveCount k q+1+1)*q
      rw [Nat.pow_succ,show 3^(positiveCount k q+1)*3*q=3*positiveProduct k q by unfold positiveProduct; ac_rfl]
      omega
  have hz : bandLastQ k q=positiveProduct k q := by
    unfold bandLastQ positiveProduct
    rw [hc]
  unfold bandMacro
  dsimp
  rw [hz,band_last_negative hn,hUeq]

#print axioms band_macro_negative
#print axioms negative_event_return
#print axioms entry_weight
#print axioms positive_fail_macro
end CapSieve
