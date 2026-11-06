import SymbolCompleteTrap
import FiniteHalting

namespace BB6Coverage

/-- Physically observable three-step halt on a read-one input:
    A marks 1, q reverses onto the marker, and q/1 halts.
    The other nine input rows remain unrestricted. -/
def markedHaltTable (q : Fin 6) (dir w0 : Bool) : PartialMachine :=
  fun slot =>
    if slot = initialSlot then some (some ⟨true, dir, q⟩)
    else if slot = (q, false) then some (some ⟨w0, !dir, q⟩)
    else if slot = (q, true) then some none
    else none

def markedHaltParams : List (Fin 6 × Bool × Bool) :=
  ((List.finRange 6).filter (fun q => q != 0)).flatMap (fun q =>
    [true, false].flatMap (fun dir =>
      [true, false].map (fun w0 => (q, dir, w0))))

def markedHaltCases : List PartialMachine :=
  markedHaltParams.map (fun (q, dir, w0) => markedHaltTable q dir w0)

theorem markedHaltParams_length : markedHaltParams.length = 20 := by decide
theorem markedHaltParams_nodup : markedHaltParams.Nodup := by decide

theorem markedHaltParams_check :
    markedHaltParams.all (fun (q, dir, w0) =>
      finiteHaltCheck (markedHaltTable q dir w0) 2) = true := by
  decide

/-- Exact source-authentic sparse halted score, for any finite prefix
    whose last actual input has an explicitly assigned halt. -/
theorem finiteHaltCheck_exact (p : PartialMachine)
    (n : Nat) (h : finiteHaltCheck p n = true)
    (m : Machine) (hm : compatible p m) : HaltsAfter m n := by
  cases he : finitePartialRun p n finiteBlank with
  | none => simp [finiteHaltCheck, he] at h
  | some c =>
    have hhalt : p (c.state, finiteTape c c.head) = some none := by
      simpa only [finiteHaltCheck, he, decide_eq_true_eq] using h
    have hr : run m n blank = some (embedFinRay c) := by
      simpa only [embedFinRay_blank] using
        finitePartialRun_sound p m hm finiteBlank c n he
    constructor
    · simp [hr]
    · have hnone : m (c.state, finiteTape c c.head) = none := hm _ _ hhalt
      simp [run, hr, rawStep, readSlot, embedFinRay, hnone]

theorem markedHalt_exact (q : Fin 6) (dir w0 : Bool)
    (h : (q, dir, w0) ∈ markedHaltParams)
    (m : Machine) (hm : compatible (markedHaltTable q dir w0) m) :
    HaltsAfter m 2 :=
  finiteHaltCheck_exact _ 2
    ((List.all_eq_true.mp markedHaltParams_check) _ h) m hm

theorem markedHalt_source_cover (q : Fin 6) (dir w0 : Bool)
    (h : (q, dir, w0) ∈ markedHaltParams) :
    Cover (DecidedBelow 3) (markedHaltTable q dir w0) :=
  finiteHaltCheck_sound _ 2 3 (by decide)
    ((List.all_eq_true.mp markedHaltParams_check) _ h)

theorem markedHaltCases_mass :
    markedHaltCases.all (fun p => decide (cylinderMass p = 25^9)) = true := by
  decide

theorem markedHalt_unique (m : Machine) (q q' : Fin 6)
    (dir dir' w0 w0' : Bool) (hq : q ≠ 0) (_hq' : q' ≠ 0)
    (h : compatible (markedHaltTable q dir w0) m)
    (h' : compatible (markedHaltTable q' dir' w0') m) :
    (q, dir, w0) = (q', dir', w0') := by
  have hA : m initialSlot = some ⟨true, dir, q⟩ :=
    h initialSlot _ (by simp [markedHaltTable])
  have hA' : m initialSlot = some ⟨true, dir', q'⟩ :=
    h' initialSlot _ (by simp [markedHaltTable])
  have heq : (⟨true, dir, q⟩ : Move) = ⟨true, dir', q'⟩ :=
    Option.some.inj (hA.symm.trans hA')
  have hdir : dir = dir' := congrArg Move.right heq
  have hstate : q = q' := congrArg Move.next heq
  subst dir'
  subst q'
  have hs0 : (q, false) ≠ initialSlot := by
    simp [initialSlot, hq]
  have h0 : m (q, false) = some ⟨w0, !dir, q⟩ :=
    h (q, false) _ (by simp [markedHaltTable, hs0])
  have h0' : m (q, false) = some ⟨w0', !dir, q⟩ :=
    h' (q, false) _ (by simp [markedHaltTable, hs0])
  have hw0 : w0 = w0' :=
    congrArg Move.write (Option.some.inj (h0.symm.trans h0'))
  simp [hw0]

theorem markedHalt_sink_disjoint (m : Machine) (q q' : Fin 6)
    (dir dir' w0 w0' w1 e : Bool) (hq : q ≠ 0)
    (h : compatible (markedHaltTable q dir w0) m)
    (h' : compatible (markedSinkTable q' dir' w0' w1 e) m) : False := by
  have hA : m initialSlot = some ⟨true, dir, q⟩ :=
    h initialSlot _ (by simp [markedHaltTable])
  have hA' : m initialSlot = some ⟨true, dir', q'⟩ :=
    h' initialSlot _ (by simp [markedSinkTable])
  have hstate : q = q' :=
    congrArg Move.next (Option.some.inj (hA.symm.trans hA'))
  subst q'
  have hnone : m (q, true) = none :=
    h (q, true) _ (by simp [markedHaltTable, initialSlot])
  have hsome : m (q, true) = some ⟨w1, e, q⟩ :=
    h' (q, true) _ (by simp [markedSinkTable, initialSlot])
  rw [hnone] at hsome
  contradiction

#print axioms finiteHaltCheck_exact
#print axioms markedHaltParams_check
#print axioms markedHalt_exact
#print axioms markedHalt_source_cover
#print axioms markedHaltCases_mass
#print axioms markedHalt_unique
#print axioms markedHalt_sink_disjoint

end BB6Coverage
