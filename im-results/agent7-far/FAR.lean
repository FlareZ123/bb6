import Frontier
import Lean.Elab.Tactic.Omega
namespace BB6Coverage.FAR

def bitAt : List Bool → Nat → Bool
  | [], _ => false
  | a::_, 0 => a
  | _::r, n+1 => bitAt r n

theorem bitAt_zero (xs : List Bool) : bitAt xs 0 = xs.headD false := by cases xs <;> rfl
theorem bitAt_tail (xs : List Bool) (i : Nat) : bitAt xs.tail i = bitAt xs (i+1) := by cases xs <;> rfl

/-- Both infinite tape rays are represented by nearest-first finite words
    padded by zeros. -/
def Represents (c : Config) (l r : List Bool) : Prop :=
  (∀ i : Nat, c.tape (c.head - (i : Int) - 1) = bitAt l i) ∧
  (∀ i : Nat, c.tape (c.head + (i : Int)) = bitAt r i)

theorem rep_blank : Represents blank [] [] := by
  constructor <;> intro i <;> rfl

theorem rep_read {c : Config} {l r : List Bool} (h : Represents c l r) :
    c.tape c.head = r.headD false := by
  simpa [bitAt_zero] using h.2 0

theorem rep_right {c : Config} {l r : List Bool} (h : Represents c l r)
    (t : Move) (ht : t.right = true) :
    Represents (applyMove c t) (t.write :: l) r.tail := by
  rcases h with ⟨hl,hr⟩
  constructor
  · intro i
    simp only [applyMove, ht, ite_true]
    cases i with
    | zero => simp [bitAt]
    | succ i =>
      have hc : c.head + 1 - (↑(i+1) : Int) - 1 = c.head - (i : Int) - 1 := by omega
      rw [hc, if_neg (by omega)]
      exact hl i
  · intro i
    simp only [applyMove, ht, ite_true]
    have hc : c.head + 1 + (i : Int) = c.head + (↑(i+1) : Int) := by omega
    rw [hc, if_neg (by omega), bitAt_tail]
    exact hr (i+1)

theorem rep_left {c : Config} {l r : List Bool} (h : Represents c l r)
    (t : Move) (ht : t.right = false) :
    Represents (applyMove c t) l.tail (l.headD false :: t.write :: r.tail) := by
  rcases h with ⟨hl,hr⟩
  constructor
  · intro i
    simp only [applyMove, ht, Bool.false_eq_true, ite_false]
    have hc : c.head + (-1) - (i : Int) - 1 = c.head - (↑(i+1) : Int) - 1 := by omega
    rw [hc, if_neg (by omega), bitAt_tail]
    exact hl (i+1)
  · intro i
    simp only [applyMove, ht, Bool.false_eq_true, ite_false]
    cases i with
    | zero =>
      have hc : c.head + (-1) + (↑(0:Nat) : Int) = c.head - (↑(0:Nat) : Int) - 1 := by omega
      rw [hc, if_neg (by omega), bitAt, ← bitAt_zero]
      exact hl 0
    | succ i =>
      cases i with
      | zero =>
        have hc : c.head + (-1) + (↑(0+1:Nat) : Int) = c.head := by omega
        rw [hc, if_pos rfl]
        rfl
      | succ i =>
        have hc : c.head + (-1) + (↑(i+1+1) : Int) = c.head + (↑(i+1) : Int) := by omega
        rw [hc, if_neg (by omega)]
        change c.tape (c.head + (↑(i+1) : Int)) = bitAt r.tail i
        rw [bitAt_tail]
        exact hr (i+1)

abbrev Node (D : Type) := Option (D × Fin 6)
/-- One-sided finite-automata reduction. Unassigned rows are possible
    halts, so every accepted proof works for all compatible completions. -/
structure Certificate (D : Type) (p : PartialMachine) where
  start : D
  push : D → Bool → D
  edge : Bool → Node D → Node D → Prop
  zero : Node D → Prop
  start_zero : push start false = start
  stop_zero : zero none
  zero_equiv : ∀ s, zero s ↔ ∃ t, edge false s t ∧ zero t
  stop_loop : ∀ a, edge a none none
  blank_safe : ¬ zero (some (start, 0))
  unknown_bad : ∀ l q a, (¬ ∃ mv, p (q,a) = some (some mv)) → edge a (some (l,q)) none
  right_closed : ∀ l q a mv, p (q,a) = some (some mv) → mv.right = true →
    edge a (some (l,q)) (some (push l mv.write,mv.next))
  left_closed : ∀ l q a mv j b v t, p (q,a) = some (some mv) → mv.right = false →
    push j b = l → edge b (some (j,mv.next)) v → edge mv.write v t → edge a (some (l,q)) t

def leftVal {D : Type} {p : PartialMachine} (C : Certificate D p) : List Bool → D
  | [] => C.start
  | a::r => C.push (leftVal C r) a

def rightVal {D : Type} {p : PartialMachine} (C : Certificate D p) : List Bool → Node D → Prop
  | [] => C.zero
  | a::r => fun s => ∃ t, C.edge a s t ∧ rightVal C r t

theorem left_unfold {D : Type} {p : PartialMachine} (C : Certificate D p) (l : List Bool) :
    leftVal C l = C.push (leftVal C l.tail) (l.headD false) := by
  cases l with
  | nil => exact C.start_zero.symm
  | cons a r => rfl

theorem right_unfold {D : Type} {p : PartialMachine} (C : Certificate D p) (r : List Bool) (s : Node D) :
    rightVal C r s ↔ ∃ t, C.edge (r.headD false) s t ∧ rightVal C r.tail t := by
  cases r with
  | nil => exact C.zero_equiv s
  | cons a r => rfl

theorem stop_bad {D : Type} {p : PartialMachine} (C : Certificate D p) (r : List Bool) :
    rightVal C r none := by
  induction r with
  | nil => exact C.stop_zero
  | cons a r ih => exact ⟨none,C.stop_loop a,ih⟩

theorem safe_step {D : Type} {p : PartialMachine} (C : Certificate D p) (m : Machine)
    (hm : compatible p m) (c : Config) (l r : List Bool) (hr : Represents c l r)
    (hs : ¬ rightVal C r (some (leftVal C l,c.state))) :
    ∃ d l' r', rawStep m c = some d ∧ Represents d l' r' ∧
      ¬ rightVal C r' (some (leftVal C l',d.state)) := by
  have hknown : ∃ mv, p (c.state,r.headD false) = some (some mv) := by
    apply Classical.byContradiction
    intro hn
    exact hs ((right_unfold C r _).mpr ⟨none,C.unknown_bad _ _ _ hn,stop_bad C _⟩)
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
    exact (right_unfold C r _).mpr ⟨_,C.right_closed _ _ _ _ hp hdir,hbad⟩
  | false =>
    refine ⟨applyMove c mv,l.tail,l.headD false::mv.write::r.tail,hstep,rep_left hr mv hdir,?_⟩
    intro hbad
    obtain ⟨v,hv,t,ht,hrest⟩ := hbad
    apply hs
    exact (right_unfold C r _).mpr ⟨t,C.left_closed _ _ _ _ _ _ _ _ hp hdir (left_unfold C l).symm hv ht,hrest⟩

theorem never {D : Type} {p : PartialMachine} (C : Certificate D p) (m : Machine)
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

#print axioms never
end BB6Coverage.FAR
