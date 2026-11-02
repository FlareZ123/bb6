import RayFinite
import RayTurnExample
namespace BB6Coverage

def rayFiniteMask (u : Nat) (s : Fin 6) : Bool := u.testBit s.val

/-- Search all six-bit control-state masks and all prefix lengths through
    maxSteps. The cutoff bounds proof discovery, not the nonhalting theorem. -/
def finiteRayOracle (p : PartialMachine) (maxSteps : Nat) : Bool :=
  (List.range (maxSteps + 1)).any (fun n =>
    (List.range 64).any (fun u =>
      finiteRayCheck p n true (rayFiniteMask u) ||
      finiteRayCheck p n false (rayFiniteMask u)))

/-- Any accepted finite search constructs a genuine all-time Cover leaf for
    all full tables extending p, with no assumption about their other slots. -/
theorem finiteRayOracle_sound (p : PartialMachine) (maxSteps bound : Nat)
    (h : finiteRayOracle p maxSteps = true) :
    Cover (DecidedBelow bound) p := by
  obtain ⟨n, _, hn⟩ := List.any_eq_true.mp h
  obtain ⟨u, _, hu⟩ := List.any_eq_true.mp hn
  rcases (Bool.or_eq_true _ _).mp hu with hr | hl
  · exact finiteRayCheck_sound p n true (rayFiniteMask u) bound hr
  · exact finiteRayCheck_sound p n false (rayFiniteMask u) bound hl

example : finiteRayOracle turnTable 2 = true := by decide

theorem turn_finite_oracle_leaf (bound : Nat) :
    Cover (DecidedBelow bound) turnTable := by
  apply finiteRayOracle_sound turnTable 2 bound
  decide

#print axioms finiteRayOracle_sound
#print axioms turn_finite_oracle_leaf
end BB6Coverage
