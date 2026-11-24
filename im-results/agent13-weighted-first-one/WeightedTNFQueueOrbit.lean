import WeightedTNF

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace BB6.Agent13BlankDelay
open BB6Coverage

/-- Composition is written in the order "first f, then e". -/
def composeStatePerm (e f : StatePerm) : StatePerm where
  forward := fun q => e.forward (f.forward q)
  backward := fun q => f.backward (e.backward q)
  leftInverse := by
    intro q
    simp [e.leftInverse, f.leftInverse]
  rightInverse := by
    intro q
    simp [e.rightInverse, f.rightInverse]

theorem renameMove_comp (e f : StatePerm) (mv : Move) :
    renameMove e (renameMove f mv) =
      renameMove (composeStatePerm e f) mv := by
  cases mv
  rfl

/-- Renaming a machine twice is the same as composing the state permutations. -/
theorem renameTable_comp (e f : StatePerm) (m : Machine) :
    renameTable (composeStatePerm e f) m =
      renameTable e (renameTable f m) := by
  funext slot
  rcases slot with ⟨q,b⟩
  simp [renameTable, composeStatePerm, renameMove_comp]

/-- A root-fixing state renaming preserves whether state zero has a
    zero-writing successor. -/
theorem zeroNext_none_rename_iff (e : StatePerm) (m : Machine)
    (hroot : e.forward 0 = 0) :
    zeroNext (renameTable e m) 0 = none ↔ zeroNext m 0 = none := by
  have h := renamed_zeroNext e m 0
  rw [hroot] at h
  constructor
  · intro hn
    rw [h] at hn
    cases hz : zeroNext m 0 with
    | none => rfl
    | some q => simp [hz] at hn
  · intro hn
    rw [h, hn]
    rfl

/-- Compatibility modulo arbitrary state renaming that fixes the initial
    state. This is the quotient needed by TNF: unused labels are names, not
    distinct semantic branches. -/
def TNFQuotientCompatible (p : PartialMachine) (m : Machine) : Prop :=
  ∃ e : StatePerm, e.forward 0 = 0 ∧ compatible p (renameTable e m)

/-- Every canonical first-hole branch is represented modulo unused-state
    renaming. A halt at the queried slot is immediately weighted-good;
    otherwise the ordinary transition is retained, renaming its destination
    to the least fresh label when necessary. -/
theorem tnf_branch_frontier (B cut : Nat) (p : PartialMachine) (slot : Slot)
    (hcut : 0 < cut) (hs : TNFSupport p cut) (_hu : p slot = none)
    (hslot : slot.1.val < cut)
    (hf : p initialSlot = some (some ⟨true,true,1⟩))
    (hhalt : ∀ m, compatible (refine p slot none) m → WeightedBound B m) :
    ∀ m, TNFQuotientCompatible p m →
      WeightedBound B m ∨
        ∃ mv : Move, mv.next.val ≤ cut ∧
          TNFQuotientCompatible (refine p slot (some mv)) m := by
  intro m hcompat
  rcases hcompat with ⟨e,he0,hp⟩
  let m' : Machine := renameTable e m
  have hterm : zeroNext m' 0 = none :=
    firstOne_terminal p hf m' hp
  cases ht : m' slot with
  | none =>
    have hc : compatible (refine p slot none) m' := by
      intro s t hs'
      by_cases he : s = slot
      · subst s
        simp [refine] at hs'
        subst t
        exact ht
      · exact hp s t (by simpa [refine,he] using hs')
    have hgood := hhalt m' hc
    have htermOriginal : zeroNext m 0 = none :=
      (zeroNext_none_rename_iff e m he0).mp hterm
    exact Or.inl (weighted_rename_back B e m he0 htermOriginal hgood)
  | some mv =>
    by_cases hused : mv.next.val < cut
    · have hc : compatible (refine p slot (some mv)) m' := by
        intro s t hs'
        by_cases he : s = slot
        · subst s
          simp [refine] at hs'
          subst t
          exact ht
        · exact hp s t (by simpa [refine,he] using hs')
      exact Or.inr ⟨mv, by omega, e, he0, by simpa [m'] using hc⟩
    · have hc6 : cut < 6 := by
        have hmv := mv.next.isLt
        omega
      let q : Fin 6 := ⟨cut,hc6⟩
      let s := swapStates mv.next q
      have ha : cut ≤ mv.next.val := by omega
      have hb : cut ≤ q.val := by simp [q]
      have hren : compatible p (renameTable s m') :=
        rename_compatible_unused p m' cut mv.next q ha hb hs hp
      have hslotA : slot.1 ≠ mv.next := by
        intro heq
        have hv := congrArg Fin.val heq
        omega
      have hslotQ : slot.1 ≠ q := by
        intro heq
        have hv := congrArg Fin.val heq
        simp [q] at hv
        omega
      have hback : s.backward slot.1 = slot.1 :=
        (swapStates_fixes mv.next q slot.1 hslotA hslotQ).2
      have hrow : (renameTable s m') slot =
          some ⟨mv.write,mv.right,q⟩ := by
        unfold renameTable
        rw [hback]
        cases slot with
        | mk st bit =>
          change (m' (st,bit)).map (renameMove s) =
            some ⟨mv.write,mv.right,q⟩
          rw [ht]
          simp [renameMove, s, swapStates_a]
      have hc : compatible
          (refine p slot (some ⟨mv.write,mv.right,q⟩))
          (renameTable s m') := by
        intro st t hs'
        by_cases he : st = slot
        · subst st
          simp [refine] at hs'
          subst t
          exact hrow
        · exact hren st t (by simpa [refine,he] using hs')
      let e' := composeStatePerm s e
      have he'0 : e'.forward 0 = 0 := by
        have h0a : (0 : Fin 6) ≠ mv.next := by
          intro heq
          have hv := congrArg Fin.val heq
          omega
        have h0q : (0 : Fin 6) ≠ q := by
          intro heq
          have hv := congrArg Fin.val heq
          simp [q] at hv
          omega
        have hs0 := (swapStates_fixes mv.next q 0 h0a h0q).1
        change s.forward (e.forward 0) = 0
        rw [he0, hs0]
      have hcomp : renameTable e' m = renameTable s m' := by
        simpa [e', m'] using renameTable_comp s e m
      refine Or.inr ⟨⟨mv.write,mv.right,q⟩, by simp [q], e', he'0, ?_⟩
      rw [hcomp]
      exact hc

#print axioms composeStatePerm
#print axioms renameTable_comp
#print axioms tnf_branch_frontier

end BB6.Agent13BlankDelay
