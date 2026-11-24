import CapAnchorTerminal

namespace CapSieve

theorem signed_halt_true_limit {limit k q : Nat}
    (h : signedHaltBy limit k q=true) : k≤limit := by
  rw [signedHaltBy] at h
  by_cases hh : (signedEvent k q).1>limit
  · rw [if_pos hh] at h
    contradiction
  · have hb := signed_event_band k q
    omega

theorem signed_halt_step {k q j v : Nat} (hv : ValidQ k q)
    (he : (signedEvent k q).2=some (j,v)) :
    (∃ limit, signedHaltBy limit k q=true) ↔
      ∃ limit, signedHaltBy limit j v=true := by
  have hs := signed_event_return hv he
  have hb := signed_event_band k q
  have hj : k<j := by omega
  constructor
  · rintro ⟨limit,h⟩
    rw [signedHaltBy] at h
    by_cases hl : (signedEvent k q).1>limit
    · rw [if_pos hl] at h
      contradiction
    · rw [if_neg hl,he] at h
      change (if k<j then signedHaltBy limit j v else false)=true at h
      rw [if_pos hj] at h
      exact ⟨limit,h⟩
  · rintro ⟨limit,h⟩
    have hl := signed_halt_true_limit h
    refine ⟨limit,?_⟩
    rw [signedHaltBy,if_neg (by omega : ¬(signedEvent k q).1>limit),he]
    change (if k<j then signedHaltBy limit j v else false)=true
    rw [if_pos hj]
    exact h

theorem anchor_421 : (∃ limit, signedHaltBy limit 0 6=true) ↔
    ∃ limit, signedHaltBy limit 5 41=true := by
  calc
    _ ↔ (∃ limit, signedHaltBy limit 1 11=true) :=
      signed_halt_step (by unfold ValidQ P; decide) (by simp [signedEvent,positiveNext,positiveProduct,positiveCount,P,CapMacro.tripleCount,negWeight,CapNegative.event,CapNegative.stopCount])
    _ ↔ (∃ limit, signedHaltBy limit 2 16=true) :=
      signed_halt_step (by unfold ValidQ P; decide) (by simp [signedEvent,positiveNext,positiveProduct,positiveCount,P,CapMacro.tripleCount,negWeight,CapNegative.event,CapNegative.stopCount])
    _ ↔ (∃ limit, signedHaltBy limit 3 11=true) :=
      signed_halt_step (by unfold ValidQ P; decide) (by simp [signedEvent,positiveNext,positiveProduct,positiveCount,P,CapMacro.tripleCount,negWeight,CapNegative.event,CapNegative.stopCount])
    _ ↔ (∃ limit, signedHaltBy limit 4 22=true) :=
      signed_halt_step (by unfold ValidQ P; decide) (by simp [signedEvent,positiveNext,positiveProduct,positiveCount,P,CapMacro.tripleCount,negWeight,CapNegative.event,CapNegative.stopCount])
    _ ↔ _ := signed_halt_step (by unfold ValidQ P; decide) (by simp [signedEvent,positiveNext,positiveProduct,positiveCount,P,CapMacro.tripleCount,negWeight,CapNegative.event,CapNegative.stopCount])

theorem anchor_754 : (∃ limit, signedHaltBy limit 0 8=true) ↔
    ∃ limit, signedHaltBy limit 5 197=true := by
  calc
    _ ↔ (∃ limit, signedHaltBy limit 1 17=true) :=
      signed_halt_step (by unfold ValidQ P; decide) (by simp [signedEvent,positiveNext,positiveProduct,positiveCount,P,CapMacro.tripleCount,negWeight,CapNegative.event,CapNegative.stopCount])
    _ ↔ (∃ limit, signedHaltBy limit 2 34=true) :=
      signed_halt_step (by unfold ValidQ P; decide) (by simp [signedEvent,positiveNext,positiveProduct,positiveCount,P,CapMacro.tripleCount,negWeight,CapNegative.event,CapNegative.stopCount])
    _ ↔ (∃ limit, signedHaltBy limit 3 65=true) :=
      signed_halt_step (by unfold ValidQ P; decide) (by simp [signedEvent,positiveNext,positiveProduct,positiveCount,P,CapMacro.tripleCount,negWeight,CapNegative.event,CapNegative.stopCount])
    _ ↔ (∃ limit, signedHaltBy limit 4 118=true) :=
      signed_halt_step (by unfold ValidQ P; decide) (by simp [signedEvent,positiveNext,positiveProduct,positiveCount,P,CapMacro.tripleCount,negWeight,CapNegative.event,CapNegative.stopCount])
    _ ↔ _ := signed_halt_step (by unfold ValidQ P; decide) (by simp [signedEvent,positiveNext,positiveProduct,positiveCount,P,CapMacro.tripleCount,negWeight,CapNegative.event,CapNegative.stopCount])

theorem anchor_252 : (∃ limit, signedHaltBy limit 0 12=true) ↔
    ∃ limit, signedHaltBy limit 5 35=true := by
  calc
    _ ↔ (∃ limit, signedHaltBy limit 1 15=true) :=
      signed_halt_step (by unfold ValidQ P; decide) (by simp [signedEvent,positiveNext,positiveProduct,positiveCount,P,CapMacro.tripleCount,negWeight,CapNegative.event,CapNegative.stopCount])
    _ ↔ (∃ limit, signedHaltBy limit 2 28=true) :=
      signed_halt_step (by unfold ValidQ P; decide) (by simp [signedEvent,positiveNext,positiveProduct,positiveCount,P,CapMacro.tripleCount,negWeight,CapNegative.event,CapNegative.stopCount])
    _ ↔ (∃ limit, signedHaltBy limit 3 47=true) :=
      signed_halt_step (by unfold ValidQ P; decide) (by simp [signedEvent,positiveNext,positiveProduct,positiveCount,P,CapMacro.tripleCount,negWeight,CapNegative.event,CapNegative.stopCount])
    _ ↔ (∃ limit, signedHaltBy limit 4 64=true) :=
      signed_halt_step (by unfold ValidQ P; decide) (by simp [signedEvent,positiveNext,positiveProduct,positiveCount,P,CapMacro.tripleCount,negWeight,CapNegative.event,CapNegative.stopCount])
    _ ↔ _ := signed_halt_step (by unfold ValidQ P; decide) (by simp [signedEvent,positiveNext,positiveProduct,positiveCount,P,CapMacro.tripleCount,negWeight,CapNegative.event,CapNegative.stopCount])

theorem anchor_canon_421 : CanonQ 5 41 := by unfold CanonQ PosQ P; decide
theorem anchor_canon_754 : CanonQ 5 197 := by unfold CanonQ PosQ P; decide
theorem anchor_canon_252 : CanonQ 5 35 := by unfold CanonQ PosQ P; decide

theorem target_421 : (∃ limit, signedHaltBy limit 0 6=true) ↔
    ∃ k n q, 5≤k ∧ terminalAt k n=some q ∧ anchorOf k q=some (5,41) :=
  anchor_421.trans (anchor_terminal_iff anchor_canon_421)

theorem target_754 : (∃ limit, signedHaltBy limit 0 8=true) ↔
    ∃ k n q, 5≤k ∧ terminalAt k n=some q ∧ anchorOf k q=some (5,197) :=
  anchor_754.trans (anchor_terminal_iff anchor_canon_754)

theorem target_252 : (∃ limit, signedHaltBy limit 0 12=true) ↔
    ∃ k n q, 5≤k ∧ terminalAt k n=some q ∧ anchorOf k q=some (5,35) :=
  anchor_252.trans (anchor_terminal_iff anchor_canon_252)

#print axioms target_421
#print axioms target_754
#print axioms target_252
end CapSieve
