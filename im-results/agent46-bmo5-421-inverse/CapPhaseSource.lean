import CapPhase
import CapStripSource
namespace CapSieve

/-- Every negative-sector unit has the same mod-12 root test as a stripped
    terminal, even after an arbitrary earlier positive-sector excursion. -/
theorem negative_unit_stop {j x : Nat} {w : Int} (hj : 6≤j)
    (hx : Band j x) (hw : W j x= -w) (hpos : 0<w) (hu : w%3≠0) :
    (¬ ∃ z, Arc z x) ↔ w%12=1 ∨ w%12=11 := by
  have hpar := w_mod4 j x
  rw [hw] at hpar
  have hh := negative_unit_parent hj hx (by omega) (by omega)
  have hp := p_parity_mod3 j
  rw [hh]
  simp only [hw]
  have h4 : (w%12)%4=w%4 := by omega
  have h3 : (w%12)%3=w%3 := by omega
  have hn3 : (-w)%3=(3-w%3)%3 := by omega
  split at hp <;> rename_i hparity
  · have ha : w%4=3 := by omega
    have hb : (P j:Int)%3=2 := by exact_mod_cast hp
    have hr : w%12=7 ∨ w%12=11 := by omega
    rcases hr with hr|hr <;> rw [hr,hb] <;> omega
  · have ha : w%4=1 := by omega
    have hb : (P j:Int)%3=1 := by exact_mod_cast hp
    have hr : w%12=1 ∨ w%12=5 := by omega
    rcases hr with hr|hr <;> rw [hr,hb] <;> omega

/-- A negative reset can be fully stripped and rejected by the unit test,
    for any authentic ancestry, not just at the initial terminal. -/
theorem negative_phase_root_exclusion {j n y : Nat} {w : Int} (hj : 6≤j)
    (hy : Band (j+n) y) (hw : W (j+n) y= -(3^n:Int)*w)
    (hpos : 0<w) (hc : w%12=1 ∨ w%12=11) : 3<Cap.rootOf y := by
  obtain ⟨x,hr,hx,_⟩:=negative_strip_general hj hy hw hpos (by omega)
  have hb:=(up_run_bands hr).1
  have he:=up_run_root hr
  have hn:=(negative_unit_stop hj hb hx hpos (by omega)).mpr hc
  have hp : Cap.predecessor x=none := by
    cases h : Cap.predecessor x with
    | none => rfl
    | some z => exact False.elim (hn ⟨z,arc_iff_pred.mpr h⟩)
  have hroot : Cap.rootOf x=x := by rw [Cap.rootOf.eq_def,hp]
  rw [he,hroot]
  have hP:=p_ge_large hj
  have hL:=l_add j
  have hl:=hb.1
  omega

#print axioms negative_unit_stop
#print axioms negative_phase_root_exclusion
end CapSieve
