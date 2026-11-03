import CrossFirstUpper

namespace BB6.CoverageAdapter

open BB6Coverage

/-- Two sparse initial-transition cylinders; every other input remains
    genuinely unassigned, with no inferred automatic decision. -/
def firstZeroCylinder : PartialMachine :=
  refine emptyTable initialSlot (some ⟨false, true, (1 : Fin 6)⟩)

def firstOneCylinder : PartialMachine :=
  refine emptyTable initialSlot (some ⟨true, true, (1 : Fin 6)⟩)

private theorem compatible_firstZero (m : Machine)
    (h : m initialSlot = some ⟨false, true, (1 : Fin 6)⟩) :
    compatible firstZeroCylinder m := by
  exact (compatible_refine_iff emptyTable m initialSlot rfl
    (some ⟨false, true, (1 : Fin 6)⟩)).2 ⟨empty_compatible m, h⟩

private theorem compatible_firstOne (m : Machine)
    (h : m initialSlot = some ⟨true, true, (1 : Fin 6)⟩) :
    compatible firstOneCylinder m := by
  exact (compatible_refine_iff emptyTable m initialSlot rfl
    (some ⟨true, true, (1 : Fin 6)⟩)).2 ⟨empty_compatible m, h⟩

private theorem covered_halter_bound (B : Nat) {p : PartialMachine}
    (cert : Cover (DecidedBelow B) p) (m : Machine)
    (hm : compatible p m) (n : Nat) (hh : HaltsAfter m n) :
    n+1 ≤ B := by
  rcases cert.sound m hm with hnever | ⟨k, hbound, hk⟩
  · have hs := hnever (n+1)
    rw [hh.2] at hs
    simp at hs
  · have heq : n = k := halting_time_unique m n k hh hk
    simpa only [heq] using hbound

/-- A complete source-authentic coverage certificate for each of the two
    explicitly fixed initial actions suffices for the global raw 28-action
    universal six-state halting-score upper bound. No third root or default
    "unknown = nonhalting" convention is required. -/
theorem raw_upper_from_two_cylinder_covers (B : Nat) (hB : 1 ≤ B)
    (cert0 : Cover (DecidedBelow B) firstZeroCylinder)
    (cert1 : Cover (DecidedBelow B) firstOneCylinder) :
    ∀ m : BB6.Coverage.RawMachine, ∀ n : Nat,
      BB6.Coverage.HaltsAt (BB6.Coverage.tickRaw m) n → n ≤ B := by
  apply (raw_upper_iff_two_first B hB).mpr
  intro m hm n hh
  rcases hm with h0 | h1
  · exact covered_halter_bound B cert0 m (compatible_firstZero m h0) n hh
  · exact covered_halter_bound B cert1 m (compatible_firstOne m h1) n hh

/-- The fully explicit BB(6) proof obligation at two canonical initial
    cylinders, plus a genuine raw halting witness attaining B.
    Both certificates and the champion witness remain UNSUPPLIED. -/
theorem exact_from_two_cylinder_covers (B : Nat) (hB : 1 ≤ B)
    (cert0 : Cover (DecidedBelow B) firstZeroCylinder)
    (cert1 : Cover (DecidedBelow B) firstOneCylinder)
    (champ : ∃ m : BB6.Coverage.RawMachine,
      BB6.Coverage.HaltsAt (BB6.Coverage.tickRaw m) B) :
    BB6.Coverage.ExactBB6 B := by
  exact ⟨champ, raw_upper_from_two_cylinder_covers B hB cert0 cert1⟩

#print axioms raw_upper_from_two_cylinder_covers
#print axioms exact_from_two_cylinder_covers
end BB6.CoverageAdapter
