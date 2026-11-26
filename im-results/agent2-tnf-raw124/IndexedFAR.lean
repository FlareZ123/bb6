import SparseFAR

namespace BB6Coverage.FAR.Indexed
open BB6Coverage BB6Coverage.FAR

/-- Low-bit radix table with logarithmic kernel lookup depth. Missing entries
    have a caller-chosen default. The certificate semantics use the table
    directly, so no unchecked conversion to dense list data is necessary. -/
inductive Radix (α : Type) where
  | empty
  | leaf (value : α)
  | branch (even odd : Radix α)

def Radix.getD {α : Type} : Radix α → Nat → α → α
  | .empty, _, d => d
  | .leaf v, i, d => if i == 0 then v else d
  | .branch e o, i, d =>
      if i % 2 == 0 then e.getD (i/2) d else o.getD (i/2) d

structure Data (d : Nat) where
  start : Fin d
  dfa : Radix (Fin d)
  masks0 : Radix Nat
  masks1 : Radix Nat
  zmask : Nat
  rows0 : Radix (List Nat)
  rows1 : Radix (List Nat)

def Data.push {d} (C : Data d) (l : Fin d) (a : Bool) : Fin d :=
  C.dfa.getD (2*l.val + a.toNat) C.start

def Data.codeMask {d} (C : Data d) (a : Bool) (i : Nat) : Nat :=
  (if a then C.masks1 else C.masks0).getD i 0

def Data.mask {d} (C : Data d) (a : Bool) (s : Node (Fin d)) : Nat :=
  C.codeMask a (nodeCode s)

def Data.edge {d} (C : Data d) (a : Bool) (s t : Node (Fin d)) : Prop :=
  (C.mask a s).testBit (nodeCode t) = true

def Data.zero {d} (C : Data d) (s : Node (Fin d)) : Prop :=
  C.zmask.testBit (nodeCode s) = true

instance {d} (C : Data d) (a : Bool) (s t : Node (Fin d)) :
    Decidable (C.edge a s t) := inferInstanceAs (Decidable (_ = true))
instance {d} (C : Data d) (s : Node (Fin d)) :
    Decidable (C.zero s) := inferInstanceAs (Decidable (_ = true))

def Data.row {d} (C : Data d) (a : Bool) (s : Node (Fin d)) : List Nat :=
  (if a then C.rows1 else C.rows0).getD (nodeCode s) []

def Data.rowsOK {d} (C : Data d) : Bool :=
  (nodes d).all (fun s => [false,true].all (fun a =>
      Sparse.maskCodes (C.row a s) == C.mask a s))

theorem Data.row_mem {d} (C : Data d) (h : C.rowsOK = true)
    (a : Bool) (s t : Node (Fin d)) (he : C.edge a s t) :
    nodeCode t ∈ C.row a s := by
  have hr := List.all_eq_true.mp (List.all_eq_true.mp h s (mem_nodes s)) a
    (by cases a <;> simp)
  have hm : Sparse.maskCodes (C.row a s) = C.mask a s := by simpa using hr
  apply Sparse.maskCodes_mem
  rw [hm]
  exact he

def Data.zeroClosed {d} (C : Data d) (s : Node (Fin d)) : Bool :=
  C.zmask.testBit (nodeCode s) || ((C.mask false s &&& C.zmask) == 0)

theorem Data.zeroClosed_sound {d} (C : Data d) (s t : Node (Fin d))
    (hc : C.zeroClosed s = true) (he : C.edge false s t) (hz : C.zero t) :
    C.zero s := by
  rcases (Bool.or_eq_true _ _).mp hc with h | h
  · exact h
  · have H : C.mask false s &&& C.zmask = 0 := by simpa using h
    have hb := congrArg (fun n => n.testBit (nodeCode t)) H
    have hm : (C.mask false s).testBit (nodeCode t) = true := he
    simp [Nat.testBit_and,hm,Data.zero] at hb hz
    exact False.elim (by simp [hz] at hb)

def Data.slotRule {d} (C : Data d) (p : PartialMachine) (q : Fin 6) (a : Bool) : Bool :=
  match p (q,a) with
  | some (some mv) =>
    if mv.right then
      (List.finRange d).all fun l =>
        decide (C.edge a (some (l,q)) (some (C.push l mv.write,mv.next)))
    else
      (List.finRange d).all fun j => [false,true].all fun b =>
        (C.row b (some (j,mv.next))).all fun i =>
          subsetMask (C.codeMask mv.write i) (C.mask a (some (C.push j b,q)))
  | _ => (List.finRange d).all fun l => decide (C.edge a (some (l,q)) none)

def Data.check {d} (C : Data d) (p : PartialMachine) : Bool :=
  decide (C.push C.start false = C.start ∧ C.zero none ∧
    (∀ a, C.edge a none none) ∧ ¬ C.zero (some (C.start,0))) &&
  (nodes d).all C.zeroClosed &&
  C.rowsOK &&
  (List.finRange 6).all (fun q => [false,true].all (C.slotRule p q))

def Data.cert {d} (C : Data d) (p : PartialMachine) (h : C.check p = true) :
    Weak.Cert (Fin d) p := by
  simp only [Data.check,Bool.and_eq_true] at h
  have hbase := of_decide_eq_true h.1.1.1
  have hz := h.1.1.2
  have hs := h.1.2
  have hslot : ∀ q a, C.slotRule p q a = true := by
    intro q a
    exact List.all_eq_true.mp (List.all_eq_true.mp h.2 q (List.mem_finRange q)) a
      (by cases a <;> simp)
  refine {
    start := C.start
    push := C.push
    edge := C.edge
    zero := C.zero
    start_zero := hbase.1
    stop_zero := hbase.2.1
    zero_back := fun s t => C.zeroClosed_sound s t
      (List.all_eq_true.mp hz s (mem_nodes s))
    stop_loop := hbase.2.2.1
    blank_safe := hbase.2.2.2
    unknown_bad := ?_
    right_closed := ?_
    left_closed := ?_
  }
  · intro l q a hn
    have hq := hslot q a
    unfold Data.slotRule at hq
    cases hp : p (q,a) with
    | none =>
      rw [hp] at hq
      exact of_decide_eq_true (List.all_eq_true.mp hq l (List.mem_finRange l))
    | some tr =>
      cases tr with
      | none =>
        rw [hp] at hq
        exact of_decide_eq_true (List.all_eq_true.mp hq l (List.mem_finRange l))
      | some mv => exact False.elim (hn ⟨mv,hp⟩)
  · intro l q a mv hp hd
    have hq := hslot q a
    simp only [Data.slotRule,hp,hd,ite_true] at hq
    exact of_decide_eq_true (List.all_eq_true.mp hq l (List.mem_finRange l))
  · intro l q a mv j b v t hp hd hl hv ht
    have hq := hslot q a
    simp only [Data.slotRule,hp,hd,Bool.false_eq_true,ite_false] at hq
    have hj := List.all_eq_true.mp hq j (List.mem_finRange j)
    have hb := List.all_eq_true.mp hj b (by cases b <;> simp)
    have hi := List.all_eq_true.mp hb (nodeCode v) (C.row_mem hs b _ v hv)
    rw [hl] at hi
    exact subsetMask_sound hi ht

theorem Data.sound {d} (C : Data d) (p : PartialMachine) (h : C.check p = true)
    (m : Machine) (hm : compatible p m) : NeverHalts m :=
  Weak.never (C.cert p h) m hm

#print axioms Data.sound
end BB6Coverage.FAR.Indexed
