import RayClosed

namespace BB6Coverage

/-- Six-bit mask certifies a proposed forward-closed control-state set.
    Only the already assigned scanned-zero transitions are consulted. -/
def rayMaskGood (p : PartialMachine) (direction : Bool)
    (mask : Fin 6 → Bool) (s : Fin 6) : Bool :=
  if mask s then
    match p (s, false) with
    | some (some mv) => (mv.right == direction) && mask mv.next
    | _ => false
  else true

def rayMaskCheck (p : PartialMachine) (direction : Bool)
    (mask : Fin 6 → Bool) : Bool :=
  mask ⟨0, by decide⟩ &&
    (List.finRange 6).all (rayMaskGood p direction mask)

/-- Every accepted six-bit mask produces an actual sparse proof-tree leaf,
    with all-time infinite-tape nonhalting proved rather than assumed. -/
theorem rayMaskCheck_sound (p : PartialMachine) (direction : Bool)
    (mask : Fin 6 → Bool) (bound : Nat)
    (h : rayMaskCheck p direction mask = true) :
    Cover (DecidedBelow bound) p := by
  have hpair : mask ⟨0, by decide⟩ = true ∧
      (List.finRange 6).all (rayMaskGood p direction mask) = true := by
    simpa only [rayMaskCheck, Bool.and_eq_true] using h
  have hstart := hpair.1
  have hclosed : ∀ s, mask s = true → ∃ mv : Move,
      p (s, false) = some (some mv) ∧
      mv.right = direction ∧ mask mv.next = true := by
    intro s hs
    have hall : rayMaskGood p direction mask s = true :=
      (List.all_eq_true.mp hpair.2) s (List.mem_finRange s)
    simp only [rayMaskGood, hs, ite_true] at hall
    cases hslot : p (s, false) with
    | none => simp [hslot] at hall
    | some outcome =>
      cases outcome with
      | none => simp [hslot] at hall
      | some mv =>
        have hboth : mv.right = direction ∧ mask mv.next = true := by
          simpa [hslot, Bool.and_eq_true] using hall
        exact ⟨mv, rfl, hboth.1, hboth.2⟩
  cases direction with
  | false =>
    apply leftClosed_leaf p (fun s => mask s = true) hstart
    intro s hs
    obtain ⟨mv, hp, hr, hn⟩ := hclosed s hs
    exact ⟨mv, hp, hr, hn⟩
  | true =>
    apply rightClosed_leaf p (fun s => mask s = true) hstart
    intro s hs
    obtain ⟨mv, hp, hr, hn⟩ := hclosed s hs
    exact ⟨mv, hp, hr, hn⟩

/-- Executable kernel-checked witness for the two-state write-one ray. -/
def twoRayMask : Fin 6 → Bool := fun s => s.val < 2

theorem twoRay_mask_check :
    rayMaskCheck twoRayTable true twoRayMask = true := by decide

theorem twoRay_from_mask (bound : Nat) :
    Cover (DecidedBelow bound) twoRayTable :=
  rayMaskCheck_sound twoRayTable true twoRayMask bound twoRay_mask_check

#print axioms rayMaskCheck_sound
#print axioms twoRay_from_mask
end BB6Coverage
