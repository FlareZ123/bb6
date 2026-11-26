import FastFAR

namespace BB6Coverage.FAR.Weak
open BB6Coverage BB6Coverage.FAR

/-- A backward-closed set of bad zero suffixes suffices; exact fixed-point
    equality is unnecessary for proving blank-tape nonhalting. -/
structure Cert (D : Type) (p : PartialMachine) where
  start : D
  push : D → Bool → D
  edge : Bool → Node D → Node D → Prop
  zero : Node D → Prop
  start_zero : push start false = start
  stop_zero : zero none
  zero_back : ∀ s t, edge false s t → zero t → zero s
  stop_loop : ∀ a, edge a none none
  blank_safe : ¬ zero (some (start, 0))
  unknown_bad : ∀ l q a, (¬ ∃ mv, p (q,a) = some (some mv)) → edge a (some (l,q)) none
  right_closed : ∀ l q a mv, p (q,a) = some (some mv) → mv.right = true →
    edge a (some (l,q)) (some (push l mv.write,mv.next))
  left_closed : ∀ l q a mv j b v t, p (q,a) = some (some mv) → mv.right = false →
    push j b = l → edge b (some (j,mv.next)) v → edge mv.write v t → edge a (some (l,q)) t

def leftVal {D : Type} {p : PartialMachine} (C : Cert D p) : List Bool → D
  | [] => C.start
  | a::r => C.push (leftVal C r) a

def rightVal {D : Type} {p : PartialMachine} (C : Cert D p) : List Bool → Node D → Prop
  | [] => C.zero
  | a::r => fun s => ∃ t, C.edge a s t ∧ rightVal C r t

theorem left_unfold {D : Type} {p : PartialMachine} (C : Cert D p) (l : List Bool) :
    leftVal C l = C.push (leftVal C l.tail) (l.headD false) := by
  cases l with
  | nil => exact C.start_zero.symm
  | cons a r => rfl

theorem right_back {D : Type} {p : PartialMachine} (C : Cert D p) (r : List Bool) (s : Node D) :
    (∃ t, C.edge (r.headD false) s t ∧ rightVal C r.tail t) → rightVal C r s := by
  cases r with
  | nil =>
    rintro ⟨t,he,hz⟩
    exact C.zero_back s t he hz
  | cons a r => exact id

theorem stop_bad {D : Type} {p : PartialMachine} (C : Cert D p) (r : List Bool) :
    rightVal C r none := by
  induction r with
  | nil => exact C.stop_zero
  | cons a r ih => exact ⟨none,C.stop_loop a,ih⟩

theorem safe_step {D : Type} {p : PartialMachine} (C : Cert D p) (m : Machine)
    (hm : compatible p m) (c : Config) (l r : List Bool) (hr : Represents c l r)
    (hs : ¬ rightVal C r (some (leftVal C l,c.state))) :
    ∃ d l' r', rawStep m c = some d ∧ Represents d l' r' ∧
      ¬ rightVal C r' (some (leftVal C l',d.state)) := by
  have hknown : ∃ mv, p (c.state,r.headD false) = some (some mv) := by
    apply Classical.byContradiction
    intro hn
    exact hs (right_back C r _ ⟨none,C.unknown_bad _ _ _ hn,stop_bad C _⟩)
  obtain ⟨mv,hp⟩ := hknown
  have hstep : rawStep m c = some (applyMove c mv) := by
    unfold rawStep readSlot
    rw [rep_read hr, hm _ _ hp]
    rfl
  cases hdir : mv.right with
  | true =>
    refine ⟨applyMove c mv,mv.write::l,r.tail,hstep,rep_right hr mv hdir,?_⟩
    intro hbad
    apply hs
    exact right_back C r _ ⟨_,C.right_closed _ _ _ _ hp hdir,hbad⟩
  | false =>
    refine ⟨applyMove c mv,l.tail,l.headD false::mv.write::r.tail,hstep,rep_left hr mv hdir,?_⟩
    intro hbad
    obtain ⟨v,hv,t,ht,hrest⟩ := hbad
    apply hs
    exact right_back C r _ ⟨t,C.left_closed _ _ _ _ _ _ _ _ hp hdir (left_unfold C l).symm hv ht,hrest⟩

theorem never {D : Type} {p : PartialMachine} (C : Cert D p) (m : Machine)
    (hm : compatible p m) : NeverHalts m := by
  have h : ∀ n, ∃ c l r, run m n blank = some c ∧ Represents c l r ∧
      ¬ rightVal C r (some (leftVal C l,c.state)) := by
    intro n
    induction n with
    | zero => exact ⟨blank,[],[],rfl,rep_blank,C.blank_safe⟩
    | succ n ih =>
      obtain ⟨c,l,r,hc,hr,hs⟩ := ih
      obtain ⟨d,l',r',hd,hr',hs'⟩ := safe_step C m hm c l r hr hs
      exact ⟨d,l',r',by simp [run,hc,hd],hr',hs'⟩
  intro n
  obtain ⟨c,l,r,hc,_,_⟩ := h n
  simp [hc]

def zeroClosed {d : Nat} (C : Data d) (s : Node (Fin d)) : Bool :=
  C.zmask.testBit (nodeCode s) || ((C.mask false s &&& C.zmask) == 0)

theorem zeroClosed_sound {d : Nat} (C : Data d) (s t : Node (Fin d))
    (hc : zeroClosed C s = true) (he : C.edge false s t) (hz : C.zero t) : C.zero s := by
  rcases (Bool.or_eq_true _ _).mp hc with h | h
  · exact h
  · have H : C.mask false s &&& C.zmask = 0 := by simpa using h
    have hbit := congrArg (fun n => n.testBit (nodeCode t)) H
    have hm : (C.mask false s).testBit (nodeCode t) = true := he
    simp [Nat.testBit_and,hm,Data.zero] at hbit hz
    exact False.elim (by simp [hz] at hbit)

def check {d : Nat} (C : Data d) (p : PartialMachine) : Bool :=
  decide (C.push C.start false = C.start ∧ C.zero none ∧
    (∀ a, C.edge a none none) ∧ ¬ C.zero (some (C.start,0))) &&
  (nodes d).all (zeroClosed C) &&
  (List.finRange d).all (fun l => (List.finRange 6).all (fun q => [false,true].all (C.fastRule p l q)))

def cert {d : Nat} (C : Data d) (p : PartialMachine) (h : check C p = true) : Cert (Fin d) p := by
  have h' := (Bool.and_eq_true _ _).mp h
  have h'' := (Bool.and_eq_true _ _).mp h'.1
  have hbase := of_decide_eq_true h''.1
  have hr : ∀ l q a, C.rule p l q a := by
    intro l q a
    exact C.fastRule_sound p l q a (List.all_eq_true.mp
      (List.all_eq_true.mp (List.all_eq_true.mp h'.2 l (List.mem_finRange l)) q (List.mem_finRange q)) a
      (by cases a <;> simp))
  refine {
    start := C.start
    push := C.push
    edge := C.edge
    zero := C.zero
    start_zero := hbase.1
    stop_zero := hbase.2.1
    zero_back := fun s t => zeroClosed_sound C s t (List.all_eq_true.mp h''.2 s (mem_nodes s))
    stop_loop := hbase.2.2.1
    blank_safe := hbase.2.2.2
    unknown_bad := ?_
    right_closed := ?_
    left_closed := ?_
  }
  · intro l q a hn
    have hrow := hr l q a
    unfold Data.rule at hrow
    cases hp : p (q,a) with
    | none => simpa [hp] using hrow
    | some t =>
      cases t with
      | none => simpa [hp] using hrow
      | some mv => exact False.elim (hn ⟨mv,hp⟩)
  · intro l q a mv hp hd
    simpa [Data.rule,hp,hd] using hr l q a
  · intro l q a mv j b v t hp hd hl hv ht
    have hrow := hr l q a
    simp [Data.rule,hp,hd] at hrow
    cases b
    · exact (hrow j).1 v t hl hv ht
    · exact (hrow j).2 v t hl hv ht

theorem sound {d : Nat} (C : Data d) (p : PartialMachine) (h : check C p = true)
    (m : Machine) (hm : compatible p m) : NeverHalts m :=
  never (cert C p h) m hm

#print axioms sound
end BB6Coverage.FAR.Weak
