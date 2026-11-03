import Lean.Elab.Tactic.Omega
import ExceptionalAGeneral
import BlankSecondExceptional
namespace BB6.Agent25RootChain
open CryptidBoundary BB6.BoundaryPadding BB6.Padding

theorem extend_regular (start : CryptidBoundary.Cfg)
    (clock n : Nat) (s u : DRegular.L)
    (hs : DRegular.Canon s)
    (hn : DRegular.run n s = some u)
    (hroot : ObsEq (CryptidBoundary.run clock start)
      (DRegularSource.sourceSection s)) :
    ObsEq (CryptidBoundary.run
      (clock + DRegular.accumulated n s) start)
      (DRegularSource.sourceSection u) := by
  have hstep : ObsEq
      (CryptidBoundary.run (DRegular.accumulated n s)
        (DRegularSource.sourceSection s))
      (DRegularSource.sourceSection u) :=
    DRegular.transport_obs
      CryptidBoundary.run DRegularSource.sourceSection ObsEq
      (fun c => rfl) CryptidBoundary.run_add
      (fun c => cfgEq_refl (represent c))
      (fun x y z h g => cfgEq_trans h g)
      (fun m x y h => source_congr m h)
      BB6.ERemaining.source_contract
      n s u hs hn
  exact source_chain clock (DRegular.accumulated n s) start
    (DRegularSource.sourceSection s)
    (DRegularSource.sourceSection u) hroot hstep

#print axioms extend_regular
end BB6.Agent25RootChain
