import Lean.Elab.Tactic.Omega
import PhysicalReturnObs
import EExceptionalAppend

namespace BB6.EExceptionalFirstPhysical
open CryptidBoundary BB6.BoundaryPadding

/-- The extra two explicit right-end zeros in the strict E1100 source theorem
    represent the same physical input as the canonical regular E-exception
    section. The distinction matters for physical first-return transport. -/
theorem source_input_obs (k q : Nat) :
    ObsEq
      (DRegularSource.sourceSection ⟨3*k+4,q+1,1⟩)
      (BB6.Agent32EAll.start k q []) := by
  rw [BB6.EExceptionalShift.e_input]
  have hp := source_init_pad 0 2
    (List.replicate (3*k+2) true ++ false :: (pairs q ++ [true,true]))
  simpa [BB6.Agent32EAll.start, CryptidBoundary.run,
    List.append_assoc] using hp

/-- Every canonical, physically unpadded E-exception input has an exact
    original six-state first PHYSICAL F/0 return at Agent32EAll.duration.
    Interior syntactic F visits with marked left tape are correctly excluded.
    Applies for every k,q; no blank-root assumption is used. -/
theorem source_exception_first_physical (k q : Nat) :
    BB6.Agent32EDoubleFirst.PhysicalF0
      (run (BB6.Agent32EAll.duration k q)
        (DRegularSource.sourceSection ⟨3*k+4,q+1,1⟩)) ∧
    (∀ t, 0<t → t<BB6.Agent32EAll.duration k q →
      ¬ BB6.Agent32EDoubleFirst.PhysicalF0
        (run t (DRegularSource.sourceSection ⟨3*k+4,q+1,1⟩))) := by
  have hi := source_input_obs k q
  have he := BB6.EExceptionalShift.e_source k q
  constructor
  · have target : BB6.Agent32EDoubleFirst.PhysicalF0
        (BB6.Agent32EAll.output k q []) := by
      cases q <;> simp
        [BB6.Agent32EDoubleFirst.PhysicalF0, BB6.Agent32EAll.output]
    exact (BB6.Agent32PhysicalObs.physicalF0_congr he).mpr target
  · intro t hp ht hf
    have hf' := (BB6.Agent32PhysicalObs.physicalF0_congr
      (source_congr t hi)).mp hf
    exact (BB6.Agent32EDoubleFirst.all_e_double_first_return k q []).2
      t hp ht hf'

#print axioms source_input_obs
#print axioms source_exception_first_physical
end BB6.EExceptionalFirstPhysical
