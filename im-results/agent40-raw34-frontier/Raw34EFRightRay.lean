import Raw34FRightRay
import Lean.Elab.Tactic.Omega

/-!
Thirty-two genuine infinite rightward blank-ray Raw34 three-hole cylinders.
The first six steps reach pristine tape (head +4, state E/F); both E0 and
F0 go right to E or F, so every subsequently queried cell is 0. No E1 or
F1 transition ever matters.  Both the E→F and F→E entry families are
covered. All other five physical entries are arbitrary, including HALT.
-/
namespace BB6.Agent40Raw34EFRightRay
open BB6Coverage BB6.Agent23Raw34Next

def efMask (s : Fin 6) : Bool :=
  decide (s = ⟨4,by decide⟩ ∨ s = ⟨5,by decide⟩)

def tables : List (List Nat) := [
  [21,0,22,0,11,0,16,13,12,0,12,0],
  [21,0,22,0,11,0,16,13,13,0,12,0],
  [21,0,22,0,11,0,16,13,24,0,12,0],
  [21,0,22,0,11,0,16,13,25,0,12,0],
  [21,0,22,0,11,0,16,13,12,0,24,0],
  [21,0,22,0,11,0,16,13,13,0,24,0],
  [21,0,22,0,11,0,16,13,24,0,24,0],
  [21,0,22,0,11,0,16,13,25,0,24,0],
  [21,0,22,0,11,0,16,25,12,0,12,0],
  [21,0,22,0,11,0,16,25,13,0,12,0],
  [21,0,22,0,11,0,16,25,24,0,12,0],
  [21,0,22,0,11,0,16,25,25,0,12,0],
  [21,0,22,0,11,0,16,25,12,0,24,0],
  [21,0,22,0,11,0,16,25,13,0,24,0],
  [21,0,22,0,11,0,16,25,24,0,24,0],
  [21,0,22,0,11,0,16,25,25,0,24,0],
  [21,0,22,0,11,0,16,12,13,0,12,0],
  [21,0,22,0,11,0,16,12,13,0,13,0],
  [21,0,22,0,11,0,16,12,13,0,24,0],
  [21,0,22,0,11,0,16,12,13,0,25,0],
  [21,0,22,0,11,0,16,12,25,0,12,0],
  [21,0,22,0,11,0,16,12,25,0,13,0],
  [21,0,22,0,11,0,16,12,25,0,24,0],
  [21,0,22,0,11,0,16,12,25,0,25,0],
  [21,0,22,0,11,0,16,24,13,0,12,0],
  [21,0,22,0,11,0,16,24,13,0,13,0],
  [21,0,22,0,11,0,16,24,13,0,24,0],
  [21,0,22,0,11,0,16,24,13,0,25,0],
  [21,0,22,0,11,0,16,24,25,0,12,0],
  [21,0,22,0,11,0,16,24,25,0,13,0],
  [21,0,22,0,11,0,16,24,25,0,24,0],
  [21,0,22,0,11,0,16,24,25,0,25,0]
]

theorem count : tables.length = 32 := by decide
theorem checked :
    tables.all (fun code => finiteRayCheck (table code) 6 true efMask) = true := by
  decide +kernel

/-- Source kernel-checked universal nonhalting, not a bounded simulation. -/
theorem never (code : List Nat) (hc : code ∈ tables)
    (m : Machine) (hm : compatible (table code) m) : NeverHalts m := by
  have hh : finiteRayCheck (table code) 6 true efMask = true :=
    List.all_eq_true.mp checked code hc
  have h := (finiteRayCheck_sound (table code) 6 true efMask 0 hh).sound m hm
  rcases h with hn | ⟨n, hn, _⟩
  · exact hn
  · omega

#print axioms count
#print axioms checked
#print axioms never
end BB6.Agent40Raw34EFRightRay
