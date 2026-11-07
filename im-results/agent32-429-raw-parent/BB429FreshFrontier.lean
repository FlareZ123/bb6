import BB429FatalB
import FreshCell
import Lean.Elab.Tactic.Omega

namespace BB429FreshFrontier
open BB6Coverage BB429PhysicalFrontier

private def B : Fin 6 := ⟨1,by decide⟩
private def C : Fin 6 := ⟨2,by decide⟩
private def D : Fin 6 := ⟨3,by decide⟩

/-- A physically decisive C/0 input with a marked cell immediately right. -/
def fatalC (c : Config) : Prop :=
  c.state = C ∧ c.tape c.head = false ∧ c.tape (c.head+1)=true

private theorem b0 : target429 (B,false) = some ⟨true,true,C⟩ := by decide
private theorem c0 : target429 (C,false) = some ⟨false,true,D⟩ := by decide
private theorem d1 : target429 (D,true) = none := by decide

private theorem right_head_tape (c : Config) (t : Move) (hr : t.right = true) :
    (applyMove c t).tape ((applyMove c t).head) = c.tape (c.head+1) := by
  simp only [applyMove,hr,ite_true]
  have hx : c.head + 1 ≠ c.head := by omega
  simp [hx]

private theorem right_next_tape (c : Config) (t : Move) (hr : t.right = true) :
    (applyMove c t).tape ((applyMove c t).head+1) = c.tape (c.head+2) := by
  simp only [applyMove,hr,ite_true]
  have hx : c.head + 2 ≠ c.head := by omega
  have hs : c.head + 1 + 1 = c.head + 2 := by omega
  simp [hx,hs]

private theorem from_fatalB_to_fatalC (n : Nat) (b : Config)
    (hb : run target429 n blank = some b)
    (hf : BB429FatalB.fatalB b) :
    ∃ c, run target429 (n+1) blank = some c ∧ fatalC c := by
  rcases hf with ⟨hstate,hzero,h1,h2⟩
  let moveB : Move := ⟨true,true,C⟩
  let c := applyMove b moveB
  have hslot : readSlot b = (B,false) := by
    change (b.state,b.tape b.head)=(B,false)
    exact Prod.ext hstate hzero
  have hrun : run target429 (n+1) blank = some c := by
    change (run target429 n blank).bind (rawStep target429) = some c
    rw [hb]
    simp [rawStep,hslot,b0,c,moveB]
  refine ⟨c,hrun,?_,?_,?_⟩
  · rfl
  · exact (right_head_tape b moveB rfl).trans h1
  · exact (right_next_tape b moveB rfl).trans h2

private theorem fatalC_causes_halt (n : Nat) (c : Config)
    (hr : run target429 n blank = some c) (hf : fatalC c) :
    BB6Coverage.HaltsAfter target429 (n+1) := by
  rcases hf with ⟨hstate,hzero,hright⟩
  let moveC : Move := ⟨false,true,D⟩
  let d := applyMove c moveC
  have hslot : readSlot c = (C,false) := by
    change (c.state,c.tape c.head)=(C,false)
    exact Prod.ext hstate hzero
  have hdslot : readSlot d = (D,true) := by
    change (d.state,d.tape d.head)=(D,true)
    exact Prod.ext rfl ((right_head_tape c moveC rfl).trans hright)
  have hrun : run target429 (n+1) blank = some d := by
    change (run target429 n blank).bind (rawStep target429) = some d
    rw [hr]
    simp [rawStep,hslot,c0,d,moveC]
  constructor
  · simp [hrun]
  · change (run target429 (n+1) blank).bind (rawStep target429) = none
    rw [hrun]
    simp [rawStep,hdslot,d1]

/-- The original #429 raw trajectory halts iff it visits C/0 with a one directly right. -/
theorem halts_iff_original_C_right_marked :
    (∃ n, BB6Coverage.HaltsAfter target429 n) ↔
    (∃ n c, run target429 n blank = some c ∧ fatalC c) := by
  constructor
  · intro h
    obtain ⟨n,b,hb,hf⟩ := BB429FatalB.target429_halts_iff_root_B001.mp h
    obtain ⟨c,hc,hfatal⟩ := from_fatalB_to_fatalC n b hb hf
    exact ⟨n+1,c,hc,hfatal⟩
  · rintro ⟨n,c,hr,hfatal⟩
    exact ⟨n+1, fatalC_causes_halt n c hr hfatal⟩

/-- A precise geometric sufficient condition for #429 nonhalting.
It requires *every* original C/0 to be at or beyond all earlier head positions. -/
theorem all_C_zero_at_record_head_implies_nonhalt
    (hrecord : ∀ n c, run target429 n blank = some c →
      c.state = C → c.tape c.head = false →
      ∀ k d, k < n → run target429 k blank = some d → d.head ≤ c.head) :
    ∀ n, ¬BB6Coverage.HaltsAfter target429 n := by
  intro n hn
  have hh : ∃ t, BB6Coverage.HaltsAfter target429 t := ⟨n,hn⟩
  obtain ⟨k,c,hc,hfatal⟩ := halts_iff_original_C_right_marked.mp hh
  have hzero : c.tape (c.head+1) = false :=
    blank_right_of_scanned_frontier target429 k c hc
      (hrecord k c hc hfatal.1 hfatal.2.1)
  exact Bool.false_ne_true (hzero.symm.trans hfatal.2.2)

#print axioms halts_iff_original_C_right_marked
#print axioms all_C_zero_at_record_head_implies_nonhalt
end BB429FreshFrontier
