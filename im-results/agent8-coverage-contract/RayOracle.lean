import RayChecker
namespace BB6Coverage

/-- Each integer 0..63 represents a candidate six-bit state mask. -/
def rayMaskOf (u : Nat) (s : Fin 6) : Bool := u.testBit s.val

/-- Exhaustive six-bit search over both consistent sweep directions. -/
def rayOracle (p : PartialMachine) : Bool :=
  (List.range 64).any (fun u =>
    rayMaskCheck p true (rayMaskOf u) || rayMaskCheck p false (rayMaskOf u))

/-- An accepted Boolean decision constructs a fully justified nonhalting
    certificate over every completion of the sparse table. -/
theorem rayOracle_sound (p : PartialMachine) (bound : Nat)
    (h : rayOracle p = true) : Cover (DecidedBelow bound) p := by
  obtain ⟨u, _, hu⟩ := (List.any_eq_true.mp h)
  rcases (Bool.or_eq_true _ _).mp hu with hr | hl
  · exact rayMaskCheck_sound p true (rayMaskOf u) bound hr
  · exact rayMaskCheck_sound p false (rayMaskOf u) bound hl

theorem twoRay_oracle_check : rayOracle twoRayTable = true := by decide

theorem twoRay_oracle_leaf (bound : Nat) :
    Cover (DecidedBelow bound) twoRayTable :=
  rayOracle_sound twoRayTable bound twoRay_oracle_check

#print axioms rayOracle_sound
#print axioms twoRay_oracle_leaf
end BB6Coverage
