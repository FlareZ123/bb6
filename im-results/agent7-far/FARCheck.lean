import FAR
namespace BB6Coverage.FAR

instance nodeForall {d : Nat} (P : Node (Fin d) → Prop) [DecidablePred P] :
    Decidable (∀ x, P x) :=
  decidable_of_iff (P none ∧ ∀ (l : Fin d) (q : Fin 6), P (some (l,q))) (by
    constructor
    · rintro ⟨hn,hs⟩ x
      cases x with
      | none => exact hn
      | some x => exact hs x.1 x.2
    · intro h
      exact ⟨h none, fun l q => h (some (l,q))⟩)

instance nodeExists {d : Nat} (P : Node (Fin d) → Prop) [DecidablePred P] :
    Decidable (∃ x, P x) :=
  decidable_of_iff (P none ∨ ∃ (l : Fin d) (q : Fin 6), P (some (l,q))) (by
    constructor
    · rintro (hn|⟨l,q,h⟩)
      · exact ⟨none,hn⟩
      · exact ⟨some (l,q),h⟩
    · rintro ⟨x,h⟩
      cases x with
      | none => exact Or.inl h
      | some x => exact Or.inr ⟨x.1,x.2,h⟩)

def nodeCode {d : Nat} : Node (Fin d) → Nat
  | none => 6*d
  | some (l,q) => 6*l.val+q.val

structure Data (d : Nat) where
  start : Fin d
  dfa : List (Fin d)
  masks0 : List Nat
  masks1 : List Nat
  zmask : Nat

def Data.push {d} (C : Data d) (l : Fin d) (a : Bool) : Fin d :=
  C.dfa[2*l.val + a.toNat]?.getD C.start

def Data.edge {d} (C : Data d) (a : Bool) (s t : Node (Fin d)) : Prop :=
  ((if a then C.masks1 else C.masks0)[nodeCode s]?.getD 0).testBit (nodeCode t) = true

def Data.zero {d} (C : Data d) (s : Node (Fin d)) : Prop :=
  C.zmask.testBit (nodeCode s) = true

instance {d} (C : Data d) (a : Bool) (s t : Node (Fin d)) : Decidable (C.edge a s t) :=
  inferInstanceAs (Decidable (_ = true))
instance {d} (C : Data d) (s : Node (Fin d)) : Decidable (C.zero s) :=
  inferInstanceAs (Decidable (_ = true))

def Data.rule {d} (C : Data d) (p : PartialMachine) (l : Fin d) (q : Fin 6) (a : Bool) : Prop :=
  match p (q,a) with
  | some (some mv) =>
    if mv.right then C.edge a (some (l,q)) (some (C.push l mv.write,mv.next))
    else ∀ (j : Fin d) (b : Bool) (v t : Node (Fin d)),
      C.push j b = l → C.edge b (some (j,mv.next)) v → C.edge mv.write v t → C.edge a (some (l,q)) t
  | _ => C.edge a (some (l,q)) none

instance {d} (C : Data d) (p : PartialMachine) (l : Fin d) (q : Fin 6) (a : Bool) :
    Decidable (C.rule p l q a) := by
  unfold Data.rule
  split
  · rename_i mv _
    split <;> infer_instance
  · infer_instance

def Data.valid {d} (C : Data d) (p : PartialMachine) : Prop :=
  C.push C.start false = C.start ∧
  C.zero none ∧
  (∀ s, C.zero s ↔ ∃ t, C.edge false s t ∧ C.zero t) ∧
  (∀ a, C.edge a none none) ∧
  ¬ C.zero (some (C.start,0)) ∧
  (∀ l q a, C.rule p l q a)

instance {d} (C : Data d) (p : PartialMachine) : Decidable (C.valid p) := by
  unfold Data.valid
  infer_instance

def Data.cert {d} (C : Data d) (p : PartialMachine) (h : C.valid p) : Certificate (Fin d) p where
  start := C.start
  push := C.push
  edge := C.edge
  zero := C.zero
  start_zero := h.1
  stop_zero := h.2.1
  zero_equiv := h.2.2.1
  stop_loop := h.2.2.2.1
  blank_safe := h.2.2.2.2.1
  unknown_bad := by
    intro l q a hn
    have hr := h.2.2.2.2.2 l q a
    unfold Data.rule at hr
    cases hp : p (q,a) with
    | none => simpa [hp] using hr
    | some t =>
      cases t with
      | none => simpa [hp] using hr
      | some mv => exact False.elim (hn ⟨mv,hp⟩)
  right_closed := by
    intro l q a mv hp hd
    simpa [Data.rule,hp,hd] using h.2.2.2.2.2 l q a
  left_closed := by
    intro l q a mv j b v t hp hd hl hv ht
    have hr := h.2.2.2.2.2 l q a
    simp [Data.rule,hp,hd] at hr
    cases b
    · exact (hr j).1 v t hl hv ht
    · exact (hr j).2 v t hl hv ht

theorem Data.sound {d} (C : Data d) (p : PartialMachine) (h : C.valid p)
    (m : Machine) (hm : compatible p m) : NeverHalts m :=
  never (C.cert p h) m hm

-- Unassigned rows are deliberately treated as possible halts.
def fromCodes (xs : List Nat) : PartialMachine := fun (q,a) =>
  match xs[2*q.val+a.toNat]? with
  | some n => if n < 24 then some (some ⟨(n/2)%2=1,n%2=1,⟨n/4 % 6, by omega⟩⟩) else none
  | none => none

#print axioms Data.sound
end BB6Coverage.FAR
