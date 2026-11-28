import Raw54E1Compose
import Raw54ZeroLFCut
import Raw54RACut
import Raw54ZeroRBCut
import Raw54ZeroRFCut
import Raw54LACut
import Raw54LBComplete
import Raw54LFComplete
import Raw54OneRACut
import Raw54RBCut
import Raw54RFCut
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option autoImplicit false
namespace BB6.Agent8Raw54
open BB6Coverage BB6.Agent13BlankDelay BB6.Agent8TNFPath BB6.Agent50TNFPilot BB6.Agent31ThreeHole

theorem lift39447 {B : Nat} {p : PartialMachine}
    (h : ∀ m, compatible p m → WeightedBound B m) (hB : B ≤ 39447) :
    ∀ m, compatible p m → WeightedBound 39447 m :=
  fun m hm k d hk hd => Nat.le_trans (h m hm k d hk hd) hB

theorem e1_complete : ∀ m, compatible e1 m → WeightedBound 39447 m :=
  e1_cover39447 (lift39447 ZeroLF.cover (by decide))
    (lift39447 RA.cover (by decide)) (lift39447 ZeroRB.cover (by decide))
    (lift39447 ZeroRF.cover (by decide)) (lift39447 LA.cover (by decide))
    (lift39447 complete_cover (by decide)) (lift39447 LF.complete_cover (by decide))
    OneRA.cover (lift39447 RB.cover (by decide)) (lift39447 RF.cover (by decide))

theorem e1_attained : ∃ m, compatible e1 m ∧ HaltsAfter m 39446 ∧ 0 ∈ delays (zeroNext m) 0 := by
  obtain ⟨m,hm,hh,hd⟩ := OneRALate.M39447.attained
  exact ⟨m, refine_preserves_compat e1 m (4,false) (some ⟨true,true,0⟩) (by decide) hm, hh, hd⟩

theorem e1_exact_threshold (B : Nat) :
    (∀ m, compatible e1 m → WeightedBound B m) ↔ 39447 ≤ B := by
  constructor
  · intro h
    obtain ⟨m,hm,hh,hd⟩ := e1_attained
    have hbound := h m hm 39446 0 hh hd
    omega
  · intro h m hm k d hk hd
    exact Nat.le_trans (e1_complete m hm k d hk hd) h

#print axioms e1_complete
#print axioms e1_attained
#print axioms e1_exact_threshold
end BB6.Agent8Raw54
