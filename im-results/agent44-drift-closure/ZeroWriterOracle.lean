import DirectedDrift

namespace BB6Coverage

/-- A six-bit state mask whose zero-reading edges must all be assigned,
    write 0, and remain inside the state mask. Directions are unrestricted. -/
def zeroMaskGood (p : PartialMachine) (mask : Fin 6 → Bool) (s : Fin 6) : Bool :=
  if mask s then
    match p (s, false) with
    | some (some mv) => (!mv.write) && mask mv.next
    | _ => false
  else true

def zeroMaskCheck (p : PartialMachine) (mask : Fin 6 → Bool) : Bool :=
  mask ⟨0, by decide⟩ &&
    (List.finRange 6).all (zeroMaskGood p mask)

/-- Every accepted mask yields an authentic all-completions coverage leaf;
    the source theorem certifies all physical tape positions at every step. -/
theorem zeroMaskCheck_sound (p : PartialMachine) (mask : Fin 6 → Bool)
    (bound : Nat) (h : zeroMaskCheck p mask = true) :
    Cover (DecidedBelow bound) p := by
  have hpair : mask ⟨0, by decide⟩ = true ∧
      (List.finRange 6).all (zeroMaskGood p mask) = true := by
    simpa only [zeroMaskCheck, Bool.and_eq_true] using h
  have hclosed : PartialZeroWriterClosed p (fun s => mask s = true) := by
    intro s hs
    have hall : zeroMaskGood p mask s = true :=
      (List.all_eq_true.mp hpair.2) s (List.mem_finRange s)
    simp only [zeroMaskGood, hs, ite_true] at hall
    cases hslot : p (s, false) with
    | none => simp [hslot] at hall
    | some outcome =>
      cases outcome with
      | none => simp [hslot] at hall
      | some mv =>
        have hboth : (!mv.write) = true ∧ mask mv.next = true := by
          simpa [hslot, Bool.and_eq_true] using hall
        rcases mv with ⟨write, direction, next⟩
        cases write with
        | true => simp at hboth
        | false => exact ⟨direction, next, rfl, hboth.2⟩
  exact partial_zero_writer_cover p (fun s => mask s = true) bound hpair.1 hclosed

/-- Executable complete search over 64 candidate closed state subsets. -/
def zeroMaskOf (u : Nat) (s : Fin 6) : Bool := u.testBit s.val

def zeroWriterOracle (p : PartialMachine) : Bool :=
  (List.range 64).any (fun u => zeroMaskCheck p (zeroMaskOf u))

theorem zeroWriterOracle_sound (p : PartialMachine) (bound : Nat)
    (h : zeroWriterOracle p = true) : Cover (DecidedBelow bound) p := by
  obtain ⟨u, _, hu⟩ := List.any_eq_true.mp h
  exact zeroMaskCheck_sound p (zeroMaskOf u) bound hu

/-- This alternating-direction example is rejected by the existing
    one-direction ray oracle but accepted by the zero-writer oracle. -/
theorem alternating_zero_oracle_accepts :
    zeroWriterOracle alternatingZeroTable = true := by decide

theorem alternating_zero_oracle_cover (bound : Nat) :
    Cover (DecidedBelow bound) alternatingZeroTable :=
  zeroWriterOracle_sound alternatingZeroTable bound alternating_zero_oracle_accepts

#print axioms zeroMaskCheck_sound
#print axioms zeroWriterOracle_sound
#print axioms alternating_zero_oracle_cover

end BB6Coverage
