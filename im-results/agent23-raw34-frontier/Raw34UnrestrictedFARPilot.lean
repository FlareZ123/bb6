import FastFAR
import Raw34TripleSweepGrowthF
import Raw34D1RDOneStepCore

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace BB6.Agent23Raw34UnrestrictedFAR
open BB6Coverage BB6Coverage.FAR

/-! Earlier FastFAR fastSearch contains an empirical knownPrefix p 24
prefilter, not a hypothesis in fastTryDfa's verified-result soundness.
This defines a legitimate unrestricted source search which can discover
FAR certificates on short partial tables whose next missing instruction
is queried before 24 blank steps. It does not assert success for any
specific table without a source checked Boolean certificate. -/
def unrestrictedSearch (p : PartialMachine) (limit : Nat) : Option (Verified p) :=
  (List.range limit).findSome? fun d =>
    fastSearchD p (⟨0,by omega⟩ : Fin (d+1))

theorem unrestrictedSearch_sound (p : PartialMachine) (limit : Nat)
    (h : (unrestrictedSearch p limit).isSome = true)
    (m : Machine) (hm : compatible p m) : NeverHalts m := by
  cases hc : unrestrictedSearch p limit with
  | none => simp [hc] at h
  | some C => exact C.2.1.sound p C.2.2 m hm

/-- Three short partial tables, including a source-proved unbounded
growth pF. These diagnostics guide whether unrestricted FAR is useful;
they are not accepted new nonhalting certificates by themselves. -/
def pF : PartialMachine := BB6.Agent23Raw34TripleSweepF.p

def qA : PartialMachine := BB6.Agent23Raw34Next.table
  [20,0,20,0,7,2,0,0,0,0,0,0]

def qE : PartialMachine := BB6.Agent23Raw34Next.table
  [20,0,20,0,7,16,0,0,0,0,0,0]

#eval ("pF d1:", (unrestrictedSearch pF 1).isSome)
#eval ("pF d2:", (unrestrictedSearch pF 2).isSome)
#eval ("qA d2:", (unrestrictedSearch qA 2).isSome)
#eval ("qE d2:", (unrestrictedSearch qE 2).isSome)

#print axioms unrestrictedSearch_sound
end BB6.Agent23Raw34UnrestrictedFAR
