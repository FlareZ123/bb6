import DirectedDrift
import RayChecker
namespace BB6Coverage

/-- All marked states must have assigned zero-reading, zero-writing
    ordinary transitions into the same marked control-state set. -/
def zeroMaskGood (p : PartialMachine) (mask : Fin 6 → Bool) (s : Fin 6) : Bool :=
  if mask s then
    match p (s, false) with
    | some (some mv) => (!mv.write) && mask mv.next
    | _ => false
  else true

def zeroMaskCheck (p : PartialMachine) (mask : Fin 6 → Bool) : Bool :=
  mask ⟨0,by decide⟩ &&
    (List.finRange 6).all (zeroMaskGood p mask)

/-- Reuses Agent44's original-source zero-writer theorem directly:
    zero-only writers may reverse direction arbitrarily. -/
theorem zeroMaskCheck_sound (p : PartialMachine) (mask : Fin 6 → Bool)
    (bound : Nat) (h : zeroMaskCheck p mask = true) :
    Cover (DecidedBelow bound) p := by
  have hboth : mask ⟨0,by decide⟩ = true ∧
      (List.finRange 6).all (zeroMaskGood p mask) = true := by
    simpa only [zeroMaskCheck, Bool.and_eq_true] using h
  apply partial_zero_writer_cover p (fun s => mask s = true) bound hboth.1
  intro s hs
  have hall : zeroMaskGood p mask s = true :=
    (List.all_eq_true.mp hboth.2) s (List.mem_finRange s)
  simp only [zeroMaskGood, hs, ite_true] at hall
  cases hp : p (s,false) with
  | none => simp [hp] at hall
  | some t =>
    cases t with
    | none => simp [hp] at hall
    | some mv =>
      have htwo : mv.write = false ∧ mask mv.next = true := by
        simpa [hp, Bool.and_eq_true] using hall
      cases mv with
      | mk write dir next =>
        have hw : write = false := htwo.1
        subst write
        exact ⟨dir, next, rfl, htwo.2⟩

def zeroMaskOracle (p : PartialMachine) : Bool :=
  (List.range 64).any (fun u =>
    zeroMaskCheck p (fun s => u.testBit s.val))

theorem zeroMaskOracle_sound (p : PartialMachine) (bound : Nat)
    (h : zeroMaskOracle p = true) : Cover (DecidedBelow bound) p := by
  obtain ⟨u, _, hu⟩ := List.any_eq_true.mp h
  exact zeroMaskCheck_sound p (fun s => u.testBit s.val) bound hu

/-- A0=0RB, B0=0LA: head bounces between two blank cells forever;
    the other ten slots remain completely arbitrary. -/
def turningZeroWriter : PartialMachine := fun slot =>
  if slot = (⟨0,by decide⟩,false) then
    some (some ⟨false,true,⟨1,by decide⟩⟩) else
  if slot = (⟨1,by decide⟩,false) then
    some (some ⟨false,false,⟨0,by decide⟩⟩) else none

theorem turningZeroWriterCheck : zeroMaskOracle turningZeroWriter = true := by decide

theorem turningZeroWriterCertificate (bound : Nat) :
    Cover (DecidedBelow bound) turningZeroWriter :=
  zeroMaskOracle_sound turningZeroWriter bound turningZeroWriterCheck

#print axioms zeroMaskCheck_sound
#print axioms zeroMaskOracle_sound
#print axioms turningZeroWriterCertificate
end BB6Coverage
