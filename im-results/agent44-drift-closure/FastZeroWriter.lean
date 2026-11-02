import ZeroWriterOracle

namespace BB6Coverage

/-- Extract a candidate closed state set by following exactly seven
    deterministic zero-transition successors, using 0 as a fallback when
    the requested sparse action is absent or halting. -/
def zeroSuccessor (p : PartialMachine) (s : Fin 6) : Fin 6 :=
  match p (s, false) with
  | some (some mv) => mv.next
  | _ => ⟨0, by decide⟩

def zeroTrace (p : PartialMachine) : Nat → Fin 6
  | 0 => ⟨0, by decide⟩
  | n+1 => zeroSuccessor p (zeroTrace p n)

def zeroOrbitMask (p : PartialMachine) (s : Fin 6) : Bool :=
  ((List.range 7).map (zeroTrace p)).contains s

/-- One-mask candidate checker that avoids searching all 64 masks.
    False may be inconclusive. True is always an authentic certificate. -/
def zeroWriterFastOracle (p : PartialMachine) : Bool :=
  zeroMaskCheck p (zeroOrbitMask p)

theorem zeroWriterFastOracle_sound (p : PartialMachine) (bound : Nat)
    (h : zeroWriterFastOracle p = true) : Cover (DecidedBelow bound) p := by
  exact zeroMaskCheck_sound p (zeroOrbitMask p) bound h

theorem alternating_zero_fast_accept :
    zeroWriterFastOracle alternatingZeroTable = true := by decide

theorem alternating_zero_fast_cover (bound : Nat) :
    Cover (DecidedBelow bound) alternatingZeroTable :=
  zeroWriterFastOracle_sound alternatingZeroTable bound alternating_zero_fast_accept

#print axioms zeroWriterFastOracle_sound
#print axioms alternating_zero_fast_cover

end BB6Coverage
