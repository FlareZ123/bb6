import LastLeftWrite
import BB429PhysicalFrontier
import Lean.Elab.Tactic.Omega
namespace BB429LastWriter
open BB6Coverage BB429PhysicalFrontier

private def C : Fin 6 := ⟨2, by decide⟩
private def D : Fin 6 := ⟨3, by decide⟩
private def E : Fin 6 := ⟨4, by decide⟩
private def F : Fin 6 := ⟨5, by decide⟩

/-- The only leftward write-one source rows are D/0, E/1 and F/1. -/
theorem left_marking_source (s : Slot) (t : Move)
    (hs : target429 s = some t) (hw : t.write = true) (hl : t.right = false) :
    s = (D,false) ∨ s = (E,true) ∨ s = (F,true) := by
  rcases s with ⟨q,b⟩
  have hq : q=0 ∨ q=1 ∨ q=2 ∨ q=3 ∨ q=4 ∨ q=5 := by
    have hlt := q.isLt
    omega
  rcases hq with h|h|h|h|h|h <;> subst q <;> cases b <;>
    simp [target429,prefix11,prefix10,prefix9,prefix8,prefix7,prefix6,
      prefix5,prefix4,prefix3,prefix2,prefix1,prefix0,refine,emptyTable]
      at hs <;> cases hs <;> simp_all [C,D,E,F]

/-- A physically fatal C/01 gate requires an earlier left-writing one
instruction at the cell immediately right of this C head, from one of
exactly three source rows. This is a necessary condition on the authentic
blank trajectory, with no synthetic start configurations. -/
theorem marked_C_right_requires_left_mark (n : Nat) (c : Config)
    (hr : run target429 n blank = some c)
    (_hc : c.state = C) (_hzero : c.tape c.head = false)
    (hmark : c.tape (c.head+1) = true) :
    ∃ k d, k < n ∧ run target429 k blank = some d ∧
      d.head = c.head+1 ∧
      (readSlot d = (D,false) ∨ readSlot d = (E,true) ∨
        readSlot d = (F,true)) := by
  obtain ⟨k,d,t,hk,hd,hxy,hs,hw,hl⟩ :=
    right_marked_has_left_writer target429 n c (c.head+1) hr (by omega) hmark
  exact ⟨k,d,hk,hd,hxy,left_marking_source (readSlot d) t hs hw hl⟩

#print axioms left_marking_source
#print axioms marked_C_right_requires_left_mark
end BB429LastWriter
