import Lean.Elab.Tactic.Omega
import ERemaining

set_option maxHeartbeats 20000000
set_option maxRecDepth 20000
namespace BB6.BlankRegular500
open CryptidBoundary BB6.BoundaryPadding BB6.Padding

def seed9 : DRegular.L := ⟨9,0,0⟩

private theorem source_seed : DRegularSource.sourceSection seed9 =
    init (List.replicate 7 true) := by
  simp [seed9,DRegularSource.sourceSection,oppairs]

private theorem seed_canon : DRegular.Canon seed9 := by
  simp [seed9,DRegular.Canon]

/-- A certified 500-return source trace beginning at the authentic blank
    Turing-machine configuration, with exact accumulated raw transition time. -/
theorem blank500 :
    ∃ t : DRegular.L,
      DRegular.run 500 seed9 = some t ∧
      ObsEq
        (CryptidBoundary.run (36 + DRegular.accumulated 500 seed9)
          CryptidBoundary.blank)
        (DRegularSource.sourceSection t) := by
  have hsome : (DRegular.run 500 seed9).isSome = true := by decide
  cases h : DRegular.run 500 seed9 with
  | none => simp [h] at hsome
  | some t =>
    refine ⟨t,rfl,?_⟩
    rw [CryptidBoundary.run_add,CryptidBoundary.blank36,←source_seed]
    exact DRegular.transport_obs
      CryptidBoundary.run DRegularSource.sourceSection ObsEq
      (fun c => rfl) CryptidBoundary.run_add
      (fun c => cfgEq_refl (represent c))
      (fun x y z h g => cfgEq_trans h g)
      (fun n x y h => source_congr n h)
      BB6.ERemaining.source_contract
      500 seed9 t seed_canon h

#print axioms blank500
end BB6.BlankRegular500
