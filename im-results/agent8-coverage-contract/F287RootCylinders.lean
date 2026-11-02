import F287RenamedRoots
import F287HaltFreedom

namespace BB6.F287
open BB6Coverage

def dCylinder : PartialMachine := freeHaltCylinder dLiteral haltInput
def eCylinder : PartialMachine := freeHaltCylinder eLiteral haltInput

/-- The source-authenticated A6/F287 nonhalting theorem also certifies
25 F/1 replacements of each rooted D and E permutation. -/
theorem dCylinder_cover (bound : Nat) :
    Cover (DecidedBelow bound) dCylinder :=
  freeHaltCylinder_cover bound dLiteral haltInput rfl d_literal_never

theorem eCylinder_cover (bound : Nat) :
    Cover (DecidedBelow bound) eCylinder :=
  freeHaltCylinder_cover bound eLiteral haltInput rfl e_literal_never

theorem dCylinder_mass : cylinderMass dCylinder = 25 := by decide
theorem eCylinder_mass : cylinderMass eCylinder = 25 := by decide

/-- Distinct fixed live instructions entail disjoint source-certified
free-halt cylinders, avoiding double counting after rooted renamings. -/
theorem freeHaltCylinders_disjoint (a b full : Machine) (halt s : Slot)
    (hs : s ≠ halt) (hdiff : a s ≠ b s)
    (ha : compatible (freeHaltCylinder a halt) full)
    (hb : compatible (freeHaltCylinder b halt) full) : False := by
  have haa : full s = a s := ha s (a s) (by simp [freeHaltCylinder, hs])
  have hbb : full s = b s := hb s (b s) (by simp [freeHaltCylinder, hs])
  exact hdiff (haa.symm.trans hbb)

private def bOne : Slot := (⟨1, by decide⟩, true)

/-- Three proven nonhalting cylinders are pairwise disjoint in the
actual original-root six-state full-table universe. -/
theorem original_D_disjoint (full : Machine)
    (ha : compatible twentyFiveCylinder full)
    (hd : compatible dCylinder full) : False := by
  exact freeHaltCylinders_disjoint expectedRLE dLiteral full haltInput (⟨0, by decide⟩, false)
    (by decide) (by decide) ha hd

theorem original_E_disjoint (full : Machine)
    (ha : compatible twentyFiveCylinder full)
    (he : compatible eCylinder full) : False := by
  exact freeHaltCylinders_disjoint expectedRLE eLiteral full haltInput (⟨0, by decide⟩, false)
    (by decide) (by decide) ha he

theorem D_E_disjoint (full : Machine)
    (hd : compatible dCylinder full)
    (he : compatible eCylinder full) : False := by
  exact freeHaltCylinders_disjoint dLiteral eLiteral full haltInput bOne
    (by decide) (by decide) hd he

#print axioms dCylinder_cover
#print axioms eCylinder_cover
#print axioms original_D_disjoint
#print axioms original_E_disjoint
#print axioms D_E_disjoint
end BB6.F287
