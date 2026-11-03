import Lean.Elab.Tactic.Omega
import ExceptionalBRejoin
import BlankRegular8394

set_option maxHeartbeats 100000000
set_option maxRecDepth 50000
namespace BB6.Agent25RootRejoin
open CryptidBoundary BB6.BoundaryPadding

/-- Two additional exact physical F/0 checkpoints on the original blank orbit. -/
theorem blank_two_more_returns :
    ∃ t : Nat, ObsEq
      (run ((36 + DRegular.accumulated 8394 BB6.BlankRegular8394.seed9) +
        (BB6.Agent32EAll.duration (3*t) 5 + BB6.Agent25Rejoin.bCost t)) blank)
      (DRegularSource.sourceSection ⟨64*t+29,1,5⟩) := by
  rcases BB6.BlankRegular8394.blank8394 with ⟨s,hr,hobs⟩
  have hv : (DRegular.run 8394 BB6.BlankRegular8394.seed9).map
      (fun x => (x.a%9,x.q,x.b)) = some (4,6,1) := by decide
  rw [hr] at hv
  simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq] at hv
  rcases hv with ⟨hm,hq,hb⟩
  let t := s.a/9
  have ha : s.a = 9*t+4 := by dsimp [t]; omega
  have hs : s = (⟨9*t+4,6,1⟩ : DRegular.L) := by
    cases s with
    | mk a q b =>
      simp only [DRegular.L.mk.injEq]
      exact ⟨ha,hq,hb⟩
  refine ⟨t,?_⟩
  rw [hs] at hobs
  exact source_chain
    (36 + DRegular.accumulated 8394 BB6.BlankRegular8394.seed9)
    (BB6.Agent32EAll.duration (3*t) 5 + BB6.Agent25Rejoin.bCost t)
    blank (DRegularSource.sourceSection ⟨9*t+4,6,1⟩)
    (DRegularSource.sourceSection ⟨64*t+29,1,5⟩)
    hobs (BB6.Agent25Rejoin.exceptional_EB_two_source t)

#print axioms blank_two_more_returns
end BB6.Agent25RootRejoin
