import BB429RootOddSection
import BB429RootLanguageCast
import BB429PhysicalBridge
import Lean.Elab.Tactic.Omega

namespace BB429RootOddPhysical
open BB6Coverage BB429PhysicalFrontier

/-- The all-parameter C/0 prefix and E/0 pair normalizer lifted to the
    unmodified physical six-state machine on its complete bi-infinite tape.
    The input is an explicitly prepared tape, not assumed blank reachable. -/
theorem c0_odd_pairs_raw (k n : Nat) (l : List Bool) (c : Config)
    (hrep : BB429PhysicalBridge.Represents
      (BB429RootLanguageCast.cast
        (⟨2,true :: Frontier429.ones2 (k+1) ++
          (false :: true :: false :: BB429RootPairNormalizer.inWords n ++ l),
          false,[]⟩ : Frontier429.Z)) c) :
    ∃ c', BB6Coverage.run target429 (2*k+10+6*n) c = some c' ∧
      BB429PhysicalBridge.Represents
        (BB429RootLanguageCast.cast
          (⟨4,l,false,BB429RootPairNormalizer.outWords n ++
               ([true,true,true,true,false] ++ Frontier429.pairs k ++ [false,true])⟩ :
               Frontier429.Z)) c' := by
  have hcast := BB429RootLanguageCast.run_cast (2*k+10+6*n)
    (⟨2,true :: Frontier429.ones2 (k+1) ++
       (false :: true :: false :: BB429RootPairNormalizer.inWords n ++ l),
       false,[]⟩ : Frontier429.Z)
  rw [BB429RootOddSection.c0_odd_pairs_to_e0] at hcast
  exact BB429PhysicalBridge.source_run_rep _ _ _ hrep _ hcast

#print axioms c0_odd_pairs_raw
end BB429RootOddPhysical
