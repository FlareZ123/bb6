import Raw54RootEightCut
import Raw54E1LEComplete
import Raw54E1RAComplete
import Raw54E1RBComplete
import Raw54E1RCComplete
import Raw54E1REComplete
import Raw54E1RFComplete
import Raw54E1OneRCComplete
import Raw54E1OneREComplete
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option autoImplicit false
namespace BB6.Agent8Raw54
open BB6Coverage BB6.Agent13BlankDelay BB6.Agent8TNFPath
open BB6.Agent50TNFPilot BB6.Agent31ThreeHole BB6.Agent10ZipAudit BB6.Agent47PartialAudit
open BB6Coverage.Agent10ZipAudit

/-- An original-source consumer of eight independently source-certified Raw54
    E1 cylinder Covers. The only remaining premises are precisely the twelve
    branches of rootRemaining12. No total Raw54 bound is claimed unconditionally. -/
theorem root_eight_complete_of_twelve
    (hRemaining : ∀ mv, mv ∈ rootRemaining12 →
       ∀ m, compatible (rootChild mv) m → WeightedBound 39447 m) :
    ∀ m, compatible raw54 m → WeightedBound 39447 m :=
  root_cover_of_eight_and_remaining12
    e1_complete
    (lift39447 E1RA.complete_cover (by decide))
    (lift39447 E1RB.complete_cover (by decide))
    (lift39447 E1RC.complete_cover (by decide))
    (lift39447 E1RE.complete_cover (by decide))
    (lift39447 E1RF.complete_cover (by decide))
    (lift39447 E1OneRC.complete_cover (by decide))
    (lift39447 E1OneRE.complete_cover (by decide))
    hRemaining

/-- The source-certified E1=0LE witness also attains the sharp weighted
    score 39447 in the full Raw54 parent cylinder. -/
theorem root_sharp_attained :
    ∃ m, compatible raw54 m ∧ HaltsAfter m 39446 ∧
      0 ∈ delays (zeroNext m) 0 := by
  obtain ⟨m,hm,hh,hd⟩ := e1_attained
  exact ⟨m, refine_preserves_compat raw54 m (4,true)
      (some ⟨false,false,4⟩) (by decide) hm, hh, hd⟩

/-- For this cylinder, the sharp upper-bound theorem follows from twelve
    residual covers; necessity of B >= 39447 is already unconditional. -/
theorem root_exact_of_twelve
    (hRemaining : ∀ mv, mv ∈ rootRemaining12 →
       ∀ m, compatible (rootChild mv) m → WeightedBound 39447 m)
    (B : Nat) :
    (∀ m, compatible raw54 m → WeightedBound B m) ↔ 39447 ≤ B := by
  constructor
  · intro h
    obtain ⟨m,hm,hh,hd⟩ := root_sharp_attained
    have hb := h m hm 39446 0 hh hd
    omega
  · intro h m hm k d hk hd
    exact Nat.le_trans (root_eight_complete_of_twelve hRemaining m hm k d hk hd) h

#print axioms root_eight_complete_of_twelve
#print axioms root_sharp_attained
#print axioms root_exact_of_twelve
end BB6.Agent8Raw54
