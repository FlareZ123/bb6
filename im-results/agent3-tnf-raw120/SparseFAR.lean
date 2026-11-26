import WeakFAR

namespace BB6Coverage.FAR.Sparse
open BB6Coverage BB6Coverage.FAR

structure Rows where
  zero : List (List Nat)
  one : List (List Nat)

def Rows.row {d : Nat} (S : Rows) (a : Bool) (s : Node (Fin d)) : List Nat :=
  (if a then S.one else S.zero)[nodeCode s]?.getD []

def maskCodes : List Nat → Nat
  | [] => 0
  | i::is => 2^i ||| maskCodes is

theorem maskCodes_mem (xs : List Nat) (i : Nat) (h : (maskCodes xs).testBit i = true) :
    i ∈ xs := by
  induction xs with
  | nil => simp [maskCodes] at h
  | cons x xs ih =>
    simp only [maskCodes,Nat.testBit_or,Nat.testBit_two_pow] at h
    rcases (Bool.or_eq_true _ _).mp h with hl | hr
    · have he : x = i := of_decide_eq_true hl
      subst x
      exact List.mem_cons_self
    · exact List.mem_cons_of_mem _ (ih hr)

def rowOK {d : Nat} (C : Data d) (S : Rows) (a : Bool) (s : Node (Fin d)) : Bool :=
  maskCodes (S.row a s) == C.mask a s

def rowsOK {d : Nat} (C : Data d) (S : Rows) : Bool :=
  (nodes d).all (fun s => [false,true].all (fun a => rowOK C S a s))

theorem row_mem {d : Nat} (C : Data d) (S : Rows) (h : rowsOK C S = true)
    (a : Bool) (s t : Node (Fin d)) (he : C.edge a s t) : nodeCode t ∈ S.row a s := by
  have hr := List.all_eq_true.mp (List.all_eq_true.mp h s (mem_nodes s)) a (by cases a <;> simp)
  have hm : maskCodes (S.row a s) = C.mask a s := by simpa [rowOK] using hr
  apply maskCodes_mem
  rw [hm]
  exact he

def codeMask {d : Nat} (C : Data d) (a : Bool) (i : Nat) : Nat :=
  (if a then C.masks1 else C.masks0)[i]?.getD 0

def rule {d : Nat} (C : Data d) (S : Rows) (p : PartialMachine) (l : Fin d) (q : Fin 6) (a : Bool) : Bool :=
  match p (q,a) with
  | some (some mv) =>
    if mv.right then decide (C.edge a (some (l,q)) (some (C.push l mv.write,mv.next)))
    else (List.finRange d).all fun j => [false,true].all fun b =>
      if C.push j b = l then (S.row b (some (j,mv.next))).all fun i =>
        subsetMask (codeMask C mv.write i) (C.mask a (some (l,q)))
      else true
  | _ => decide (C.edge a (some (l,q)) none)

theorem rule_fast {d : Nat} (C : Data d) (S : Rows) (p : PartialMachine) (l : Fin d) (q : Fin 6) (a : Bool)
    (hs : rowsOK C S = true) (h : rule C S p l q a = true) : C.fastRule p l q a = true := by
  unfold rule at h
  unfold Data.fastRule
  split at h <;> rename_i mv he
  · rw [he]
    split at h
    · rename_i hr
      simpa [hr] using h
    · rename_i hr
      simp only [hr, Bool.false_eq_true, ite_false, List.all_eq_true] at h ⊢
      intro j hj b hb
      by_cases hp : C.push j b = l
      · simp only [hp,ite_true]
        apply List.all_eq_true.mpr
        intro v hv
        by_cases hv' : C.edge b (some (j,mv.next)) v
        · simp only [hv',ite_true]
          have hs' := h j hj b hb
          simp only [hp,ite_true] at hs'
          exact List.all_eq_true.mp hs' (nodeCode v) (row_mem C S hs b (some (j,mv.next)) v hv')
        · simp [hv']
      · simp [hp]
  · split
    · rename_i mv hm
      exact False.elim (he mv hm)
    · exact h

def check {d : Nat} (C : Data d) (S : Rows) (p : PartialMachine) : Bool :=
  decide (C.push C.start false = C.start ∧ C.zero none ∧
    (∀ a, C.edge a none none) ∧ ¬ C.zero (some (C.start,0))) &&
  (nodes d).all (Weak.zeroClosed C) &&
  rowsOK C S &&
  (List.finRange d).all (fun l => (List.finRange 6).all (fun q => [false,true].all (rule C S p l q)))

theorem check_weak {d : Nat} (C : Data d) (S : Rows) (p : PartialMachine)
    (h : check C S p = true) : Weak.check C p = true := by
  simp only [check, Bool.and_eq_true] at h
  simp only [Weak.check, Bool.and_eq_true]
  refine ⟨h.1.1,?_⟩
  apply List.all_eq_true.mpr
  intro l hl
  apply List.all_eq_true.mpr
  intro q hq
  apply List.all_eq_true.mpr
  intro a ha
  exact rule_fast C S p l q a h.1.2
    (List.all_eq_true.mp (List.all_eq_true.mp (List.all_eq_true.mp h.2 l hl) q hq) a ha)

theorem sound {d : Nat} (C : Data d) (S : Rows) (p : PartialMachine) (h : check C S p = true)
    (m : Machine) (hm : compatible p m) : NeverHalts m :=
  Weak.sound C p (check_weak C S p h) m hm

#print axioms sound
end BB6Coverage.FAR.Sparse
