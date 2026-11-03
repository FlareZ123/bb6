import DObservedTransport
import BoundaryPadding

namespace DRegularSource
open CryptidBoundary

/-- Actual original source F/0 section, including the implicit all-zero right end.
    This representation uses 'init' with two leading unary bits already present. -/
def sourceSection (s : DRegular.L) : CryptidBoundary.Cfg :=
  CryptidBoundary.init
    (List.replicate (s.a-2) true ++
      CryptidBoundary.oppairs s.q ++ List.replicate s.b true)

/-- Exact missing original-source obligation: all eleven modeled successful
    L-returns must be derivable from existing quantified raw macros modulo the
    source's fully proved physical-blank observational equivalence. -/
def SourceContract : Prop :=
  ∀ s t : DRegular.L, DRegular.Canon s → DRegular.next s = some t →
    BB6.BoundaryPadding.ObsEq
      (CryptidBoundary.run (DRegular.duration s) (sourceSection s))
      (sourceSection t)

/-- The authentic original-source version of the 1711-return seed5 certificate,
    parameterized by exactly one explicit unfinished case-composition contract.
    Existing upstream source_congr gives correct tape-padding transport. -/
theorem first1711_source (hOne : SourceContract) :
    BB6.BoundaryPadding.ObsEq
      (CryptidBoundary.run
        (DRegular.accumulated 1711 DRegular.seed5)
        (sourceSection DRegular.seed5))
      (sourceSection DRegular.terminal5) := by
  exact DRegular.seed5_transport_obs
    CryptidBoundary.run sourceSection BB6.BoundaryPadding.ObsEq
    (fun c => rfl)
    CryptidBoundary.run_add
    (fun c => BB6.Padding.cfgEq_refl (BB6.BoundaryPadding.represent c))
    (fun x y z h g => BB6.Padding.cfgEq_trans h g)
    (fun n x y h => BB6.BoundaryPadding.source_congr n h)
    hOne

#print axioms first1711_source
end DRegularSource
