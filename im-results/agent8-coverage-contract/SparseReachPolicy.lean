import SparsePruneSearch
namespace BB6Coverage

/-- Continue along already assigned ordinary transitions; return the
    first slot required by the run but not yet specified. -/
def firstReachedHole (p : PartialMachine) : Nat → FinRayCfg → Option Slot
  | 0, _ => none
  | n+1, c =>
      let slot := (c.state, finiteTape c c.head)
      match p slot with
      | none => some slot
      | some none => none
      | some (some mv) => firstReachedHole p n (finiteMove c mv)

theorem firstReachedHole_sound (p : PartialMachine) (n : Nat)
    (c : FinRayCfg) (s : Slot)
    (h : firstReachedHole p n c = some s) : p s = none := by
  induction n generalizing c with
  | zero => simp [firstReachedHole] at h
  | succ n ih =>
    cases hp : p (c.state, finiteTape c c.head) with
    | none =>
      simp [firstReachedHole, hp] at h
      subst s
      exact hp
    | some t =>
      cases t with
      | none => simp [firstReachedHole, hp] at h
      | some mv =>
        have hnext : firstReachedHole p n (finiteMove c mv) = some s := by
          simpa [firstReachedHole, hp] using h
        exact ih (finiteMove c mv) hnext

/-- Prefer a reached unknown slot; fall back to the first table hole. -/
def chooseReachHole (p : PartialMachine) (probeLimit : Nat) : Option Slot :=
  match firstReachedHole p probeLimit finiteBlank with
  | some s => some s
  | none => findUnassigned p allSlots

theorem chooseReachHole_sound (p : PartialMachine) (probeLimit : Nat)
    (s : Slot) (h : chooseReachHole p probeLimit = some s) : p s = none := by
  cases hf : firstReachedHole p probeLimit finiteBlank with
  | some q =>
    have hs : q = s := by simpa [chooseReachHole, hf] using h
    subst s
    exact firstReachedHole_sound p probeLimit finiteBlank q hf
  | none =>
    have hs : findUnassigned p allSlots = some s := by
      simpa [chooseReachHole, hf] using h
    exact findUnassigned_sound p allSlots s hs

/-- Source-verified branch policy: unassigned slots actually consulted
    by the blank run are explored first; all 25 choices are still covered. -/
def reachCoverSearch (p : PartialMachine) (bound rayLimit probeLimit : Nat) : Nat → Bool
  | 0 => finiteDecisionOracle p bound rayLimit
  | depth+1 =>
      if finiteDecisionOracle p bound rayLimit = true then true else
        match chooseReachHole p probeLimit with
        | none => false
        | some slot => choices.all
            (fun t => reachCoverSearch (refine p slot t) bound rayLimit probeLimit depth)

theorem reachCoverSearch_sound (bound rayLimit probeLimit depth : Nat) :
    ∀ p : PartialMachine,
      reachCoverSearch p bound rayLimit probeLimit depth = true →
        Cover (DecidedBelow bound) p := by
  induction depth with
  | zero =>
    intro p h
    exact finiteDecisionOracle_sound p bound rayLimit h
  | succ depth ih =>
    intro p h
    by_cases hleaf : finiteDecisionOracle p bound rayLimit = true
    · exact finiteDecisionOracle_sound p bound rayLimit hleaf
    · cases hslot : chooseReachHole p probeLimit with
      | none => simp [reachCoverSearch, hleaf, hslot] at h
      | some slot =>
        have hchildren : choices.all (fun t =>
              reachCoverSearch (refine p slot t) bound rayLimit probeLimit depth) = true := by
          simpa [reachCoverSearch, hleaf, hslot] using h
        have hs : p slot = none := chooseReachHole_sound p probeLimit slot hslot
        apply Cover.branch p slot hs
        intro t ht
        exact ih (refine p slot t) ((List.all_eq_true.mp hchildren) t ht)

/-- With A0 assigned to go to B, the first *reachable* hole is B0.
    Naive lexical slot choice would choose the unvisited A1. -/
def reachTest : PartialMachine := fun s =>
  if s = (⟨0,by decide⟩,false) then
    some (some ⟨true,true,⟨1,by decide⟩⟩)
  else none

theorem reachable_choice_test :
    chooseReachHole reachTest 2 = some (⟨1,by decide⟩,false) := by decide

theorem table_order_misses_reachable :
    findUnassigned reachTest allSlots = some (⟨0,by decide⟩,true) := by decide

theorem oneHoleReachCertificate :
    Cover (DecidedBelow 2) oneHoleUniversalTable := by
  apply reachCoverSearch_sound 2 0 2 1
  decide

#print axioms firstReachedHole_sound
#print axioms chooseReachHole_sound
#print axioms reachCoverSearch_sound
#print axioms oneHoleReachCertificate
end BB6Coverage
