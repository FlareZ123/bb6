import RayFinite
namespace BB6Coverage

/-- A sparse simulation explicitly encounters an assigned halt. -/
def finiteHaltCheck (p : PartialMachine) (n : Nat) : Bool :=
  match finitePartialRun p n finiteBlank with
  | none => false
  | some c => decide (p (c.state, finiteTape c c.head) = some none)

/-- Every total completion halts at exactly the certified attempted step. -/
theorem finiteHaltCheck_sound (p : PartialMachine) (n bound : Nat)
    (hbound : n+1 ≤ bound) (h : finiteHaltCheck p n = true) :
    Cover (DecidedBelow bound) p := by
  cases he : finitePartialRun p n finiteBlank with
  | none => simp [finiteHaltCheck, he] at h
  | some c =>
    have hhalt : p (c.state, finiteTape c c.head) = some none := by
      simpa only [finiteHaltCheck, he, decide_eq_true_eq] using h
    apply Cover.leaf
    intro m hm
    right
    refine ⟨n, hbound, ?_⟩
    have hr : run m n blank = some (embedFinRay c) := by
      have hs := finitePartialRun_sound p m hm finiteBlank c n he
      simpa only [embedFinRay_blank] using hs
    constructor
    · simp [hr]
    · have hnone : m (c.state, finiteTape c c.head) = none := hm _ _ hhalt
      simp [run, hr, rawStep, readSlot, embedFinRay, hnone]

def finiteHaltOracle (p : PartialMachine) (bound : Nat) : Bool :=
  (List.range bound).any (finiteHaltCheck p)

theorem finiteHaltOracle_sound (p : PartialMachine) (bound : Nat)
    (h : finiteHaltOracle p bound = true) :
    Cover (DecidedBelow bound) p := by
  obtain ⟨n, hn, hh⟩ := List.any_eq_true.mp h
  exact finiteHaltCheck_sound p n bound (Nat.succ_le_of_lt (List.mem_range.mp hn)) hh

/-- Actual two-step halter cylinder, ten other slots unconstrained. -/
def twoStepHaltTable : PartialMachine := fun s =>
  if s = (⟨0, by decide⟩, false) then
    some (some ⟨false,true, ⟨1, by decide⟩⟩) else
  if s = (⟨1, by decide⟩, false) then some none else none

theorem twoStepHaltCheck : finiteHaltOracle twoStepHaltTable 2 = true := by decide

theorem twoStepHaltCertificate : Cover (DecidedBelow 2) twoStepHaltTable :=
  finiteHaltOracle_sound twoStepHaltTable 2 twoStepHaltCheck

#print axioms finiteHaltCheck_sound
#print axioms finiteHaltOracle_sound
#print axioms twoStepHaltCertificate
end BB6Coverage
