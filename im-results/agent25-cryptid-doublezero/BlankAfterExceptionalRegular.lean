import Lean.Elab.Tactic.Omega
import BlankRootRejoin

set_option maxHeartbeats 100000000
set_option maxRecDepth 50000
namespace BB6.Agent25RootRejoin
open CryptidBoundary BB6.BoundaryPadding BB6.Padding

/-- Every defined regular-model prefix after the actual blank-root
    exceptional E/B reentry transports to the original six-state machine.
    No assertion is made that all future model returns are defined. -/
theorem blank_regular_after_exception :
    ∃ t : Nat, ∀ (n : Nat) (s : DRegular.L),
      DRegular.run n ⟨64*t+29,1,5⟩ = some s →
      ObsEq
        (CryptidBoundary.run
          (((36 + DRegular.accumulated 8394 BB6.BlankRegular8394.seed9) +
              (BB6.Agent32EAll.duration (3*t) 5 + BB6.Agent25Rejoin.bCost t)) +
            DRegular.accumulated n ⟨64*t+29,1,5⟩)
          CryptidBoundary.blank)
        (DRegularSource.sourceSection s) := by
  rcases blank_two_more_returns with ⟨t, hroot⟩
  refine ⟨t, ?_⟩
  intro n s hn
  have hc : DRegular.Canon ⟨64*t+29,1,5⟩ := by
    constructor
    · show 64*t+29 ≥ 2
      omega
    · left
      decide
  have ht : ObsEq
      (CryptidBoundary.run
        (DRegular.accumulated n ⟨64*t+29,1,5⟩)
        (DRegularSource.sourceSection ⟨64*t+29,1,5⟩))
      (DRegularSource.sourceSection s) :=
    DRegular.transport_obs
      CryptidBoundary.run DRegularSource.sourceSection ObsEq
      (fun c => rfl) CryptidBoundary.run_add
      (fun c => cfgEq_refl (represent c))
      (fun x y z h g => cfgEq_trans h g)
      (fun m x y h => source_congr m h)
      BB6.ERemaining.source_contract
      n ⟨64*t+29,1,5⟩ s hc hn
  exact source_chain
    ((36 + DRegular.accumulated 8394 BB6.BlankRegular8394.seed9) +
      (BB6.Agent32EAll.duration (3*t) 5 + BB6.Agent25Rejoin.bCost t))
    (DRegular.accumulated n ⟨64*t+29,1,5⟩)
    CryptidBoundary.blank
    (DRegularSource.sourceSection ⟨64*t+29,1,5⟩)
    (DRegularSource.sourceSection s) hroot ht

#print axioms blank_regular_after_exception
end BB6.Agent25RootRejoin
