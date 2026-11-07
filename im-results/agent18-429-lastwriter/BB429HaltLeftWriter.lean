import BB429LastWriter
import BB429FreshFrontier
import Lean.Elab.Tactic.Omega

namespace BB429HaltLeftWriter
open BB6Coverage BB429PhysicalFrontier

private def D : Fin 6 := ⟨3, by decide⟩
private def E : Fin 6 := ⟨4, by decide⟩
private def F : Fin 6 := ⟨5, by decide⟩

/-- Every genuine original #429 halt forces an earlier left-write-one
instruction on exactly the physical cell which later lies one square
right of the fatal C/0 head, with the earlier row in {D/0,E/1,F/1}. -/
theorem halt_requires_one_of_three_previous_left_writes
    (hhalt : ∃ t, HaltsAfter target429 t) :
    ∃ k n c d, k < n ∧
      run target429 k blank = some d ∧
      run target429 n blank = some c ∧
      BB429FreshFrontier.fatalC c ∧
      d.head = c.head + 1 ∧
      (readSlot d = (D,false) ∨
        readSlot d = (E,true) ∨ readSlot d = (F,true)) := by
  obtain ⟨n,c,hr,hfatal⟩ :=
    BB429FreshFrontier.halts_iff_original_C_right_marked.mp hhalt
  obtain ⟨k,d,hk,hd,hxy,hslot⟩ :=
    BB429LastWriter.marked_C_right_requires_left_mark n c hr
      hfatal.1 hfatal.2.1 hfatal.2.2
  exact ⟨k,n,c,d,hk,hd,hr,hfatal,hxy,hslot⟩

#print axioms halt_requires_one_of_three_previous_left_writes
end BB429HaltLeftWriter
