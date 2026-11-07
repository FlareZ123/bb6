import LastLeftExcursion
import BB429HaltLeftWriter
import Lean.Elab.Tactic.Omega

namespace BB429HaltExcursion
open BB6Coverage BB429PhysicalFrontier

private def D : Fin 6 := ⟨3, by decide⟩
private def E : Fin 6 := ⟨4, by decide⟩
private def F : Fin 6 := ⟨5, by decide⟩

/-- An actual blank-tape #429 halt entails an earlier D/0, E/1 or F/1
left-write-one instruction at a fixed physical boundary. Between that
instruction and the later fatal C/01, the head NEVER reaches or crosses
this marked boundary: the entire raw segment stays strictly to its left. -/
theorem halt_requires_bounded_left_excursion
    (hhalt : ∃ t, HaltsAfter target429 t) :
    ∃ k n c d, k < n ∧
      run target429 k blank = some d ∧
      run target429 n blank = some c ∧
      BB429FreshFrontier.fatalC c ∧
      d.head = c.head+1 ∧
      (readSlot d = (D,false) ∨ readSlot d = (E,true) ∨
        readSlot d = (F,true)) ∧
      (∀ j e, k < j → j ≤ n →
        run target429 j blank = some e → e.head < d.head) := by
  obtain ⟨n,c,hr,hfatal⟩ :=
    BB429FreshFrontier.halts_iff_original_C_right_marked.mp hhalt
  obtain ⟨k,d,t,hk,hd,hxy,hs,hw,hl,hall⟩ :=
    right_marked_has_left_excursion target429 n c (c.head+1)
      hr (by omega) hfatal.2.2
  have hslot := BB429LastWriter.left_marking_source (readSlot d) t hs hw hl
  refine ⟨k,n,c,d,hk,hd,hr,hfatal,hxy,hslot,?_⟩
  intro j e hj hle hjrun
  have hx := hall j e hj hle hjrun
  omega

#print axioms halt_requires_bounded_left_excursion
end BB429HaltExcursion
