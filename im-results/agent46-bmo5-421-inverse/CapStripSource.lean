import CapStrip
import CapSieveSource
namespace CapSieve

theorem up_run_root {j n x y : Nat} (h : UpRun j n x y) : Cap.rootOf y=Cap.rootOf x := by
  induction h with
  | zero => rfl
  | head hr hs ih => rw [ih,Cap.root_edge (arc_iff.mp (regFrom_arc hr))]

/-- Unbounded exclusion, simultaneously valid for all three BMO5 roots. -/
theorem stripped_unit_excludes {j n w : Nat} (hj : 6≤j)
    (h : 3^n*w=2*(j+n)+3) (hc : w%12=1 ∨ w%12=11) :
    3<Cap.rootOf (Cap.halt (j+n)) := by
  obtain ⟨x,hr,hn,hx⟩:=stripped_unit_root hj h hc
  have he:=up_run_root hr
  rw [t_eq] at he
  have hp : Cap.predecessor x=none := by
    cases h : Cap.predecessor x with
    | none => rfl
    | some y => exact False.elim (hn ⟨y,arc_iff_pred.mpr h⟩)
  have hxroot : Cap.rootOf x=x := by rw [Cap.rootOf.eq_def,hp]
  rw [he,hxroot]
  exact hx

#print axioms stripped_unit_excludes
end CapSieve
