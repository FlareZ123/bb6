import SparseFAR

namespace BB6Coverage.FAR.Direct
open BB6Coverage BB6Coverage.FAR
open BB6Coverage.FAR.Sparse

/-- Check each DFA predecessor at its uniquely determined destination.
    This removes the redundant loop over candidate destinations. -/
def slotRule {d : Nat} (C : Data d) (S : Rows) (p : PartialMachine)
    (q : Fin 6) (a : Bool) : Bool :=
  match p (q,a) with
  | some (some mv) =>
    if mv.right then
      (List.finRange d).all fun l =>
        decide (C.edge a (some (l,q)) (some (C.push l mv.write,mv.next)))
    else
      (List.finRange d).all fun j => [false,true].all fun b =>
        (S.row b (some (j,mv.next))).all fun i =>
          subsetMask (codeMask C mv.write i) (C.mask a (some (C.push j b,q)))
  | _ => (List.finRange d).all fun l => decide (C.edge a (some (l,q)) none)

theorem slotRule_sound {d : Nat} (C : Data d) (S : Rows) (p : PartialMachine)
    (q : Fin 6) (a : Bool) (l : Fin d) (h : slotRule C S p q a = true) :
    Sparse.rule C S p l q a = true := by
  unfold slotRule at h
  unfold Sparse.rule
  split at h <;> rename_i mv he
  · rw [he]
    split at h
    · rename_i hr
      simpa [hr] using List.all_eq_true.mp h l (List.mem_finRange l)
    · rename_i hr
      simp only [hr, Bool.false_eq_true, ite_false, List.all_eq_true] at h ⊢
      intro j hj b hb
      by_cases hp : C.push j b = l
      · simpa [hp] using h j hj b hb
      · simp [hp]
  · split
    · rename_i mv hm
      exact False.elim (he mv hm)
    · exact List.all_eq_true.mp h l (List.mem_finRange l)

def check {d : Nat} (C : Data d) (S : Rows) (p : PartialMachine) : Bool :=
  decide (C.push C.start false = C.start ∧ C.zero none ∧
    (∀ a, C.edge a none none) ∧ ¬ C.zero (some (C.start,0))) &&
  (nodes d).all (Weak.zeroClosed C) &&
  rowsOK C S &&
  (List.finRange 6).all (fun q => [false,true].all (slotRule C S p q))

theorem check_sparse {d : Nat} (C : Data d) (S : Rows) (p : PartialMachine)
    (h : check C S p = true) : Sparse.check C S p = true := by
  simp only [check,Bool.and_eq_true] at h
  simp only [Sparse.check,Bool.and_eq_true]
  refine ⟨h.1,?_⟩
  apply List.all_eq_true.mpr
  intro l hl
  apply List.all_eq_true.mpr
  intro q hq
  apply List.all_eq_true.mpr
  intro a ha
  exact slotRule_sound C S p q a l
    (List.all_eq_true.mp (List.all_eq_true.mp h.2 q hq) a ha)

theorem sound {d : Nat} (C : Data d) (S : Rows) (p : PartialMachine)
    (h : check C S p = true) (m : Machine) (hm : compatible p m) : NeverHalts m :=
  Sparse.sound C S p (check_sparse C S p h) m hm

#print axioms sound
end BB6Coverage.FAR.Direct
