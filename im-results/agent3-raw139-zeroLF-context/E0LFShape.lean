import E0LFMacro
import Lean

namespace BB6Coverage.Agent3E0LFShape
open BB6Coverage.Agent3E0LFMacro

/-- State 0 means all zeros; 1/2 clean ending in 1/0; 3 means exactly one
internal 00 at the near end; 4 means such 00 followed by one 1; 5 other. -/
def lstep (a : Bool) (k : Fin 6) : Fin 6 :=
  match k.val, a with
  | 0, false => 0 | 0, true => 1
  | 1, false => 2 | 1, true => 1
  | 2, false => 3 | 2, true => 1
  | 3, false => 5 | 3, true => 4
  | _, _ => 5

def lkey (l : List Bool) : Fin 6 := l.foldr lstep 0

def rstep (a : Bool) (k : Fin 8) : Fin 8 := ⟨k.val / 2 + (if a then 4 else 0), by
  have hk := k.isLt
  cases a <;> simp <;> omega⟩

def rkey (r : List Bool) : Fin 8 := r.foldr rstep 0

def shapeKey (q : Phase) (l : Fin 6) (r : Fin 8) : Bool :=
  match q with
  | .a => if r.val < 4 then l.val ≤ 1 else l.val ≤ 2 && r.val == 4
  | .c => l.val == 1 || (l.val == 4 && r.val < 2)
  | .e => l.val ≤ 3 && r.val < 4

def Shape (q : Phase) (l r : List Bool) : Prop := shapeKey q (lkey l) (rkey r) = true

theorem lkey_append (l t : List Bool) : lkey (l++t) = l.foldr lstep (lkey t) := by
  simp [lkey,List.foldr_append]

theorem rkey_append (r t : List Bool) : rkey (r++t) = r.foldr rstep (rkey t) := by
  simp [rkey,List.foldr_append]

private theorem rule_shape (r : Rule) (hr : r ∈ rules false) :
    ∀ (l : Fin 6) (t : Fin 8),
      shapeKey r.q (r.u.foldr lstep l) (r.v.foldr rstep t) = true →
      shapeKey r.q' (r.x.foldr lstep l) (r.y.foldr rstep t) = true := by
  simp [rules,common] at hr
  rcases hr with (hr|hr|hr|hr|hr|hr|hr|hr|hr|hr|hr|hr) <;> subst r <;> decide

theorem shape_closed (r : Rule) (hr : r ∈ rules false) (l t : List Bool)
    (h : Shape r.q (r.u++l) (r.v++t)) : Shape r.q' (r.x++l) (r.y++t) := by
  unfold Shape at h ⊢
  rw [lkey_append,rkey_append] at h ⊢
  exact rule_shape r hr _ _ h

theorem shape_padding (q : Phase) (l r : List Bool) (h : Shape q l r) :
    Shape q (l++[false,false,false]) (r++[false,false,false]) := by
  unfold Shape at h ⊢
  rw [lkey_append,rkey_append]
  change shapeKey q (l.foldr lstep 0) (r.foldr rstep 0) = true
  exact h

theorem shape_start : Shape .a [] [] := by rfl

theorem lkey_zero_iff (l : List Bool) : lkey l = 0 ↔ ∀ b ∈ l, b = false := by
  induction l with
  | nil => simp [lkey]
  | cons a l ih =>
    have H : ∀ (a : Bool) (k : Fin 6), lstep a k = 0 ↔ a = false ∧ k = 0 := by decide
    change lstep a (lkey l) = 0 ↔ _
    rw [H,ih]
    simp

/-- On the structural invariant, the only remaining bad macro configurations
are A1 at a leftmost 1 with two immediate right zeros. -/
theorem shape_bad (q : Phase) (l r : List Bool) (hs : Shape q l r) (hb : Bad q l r) :
    q = .a ∧ lkey l = 0 ∧ rkey r = 4 := by
  cases hb with
  | a l r =>
    unfold Shape at hs
    change shapeKey .a (lstep false (lstep false (lkey l))) (rstep true (rkey r)) = true at hs
    have H : ∀ (i : Fin 6) (j : Fin 8),
        shapeKey .a (lstep false (lstep false i)) (rstep true j) = true →
        lstep false (lstep false i) = 0 ∧ rstep true j = 4 := by decide
    exact ⟨rfl,H _ _ hs⟩
  | c l r =>
    unfold Shape at hs
    change shapeKey .c (lstep false (lkey l)) (rstep false (rkey r)) = true at hs
    have H : ∀ (i : Fin 6) (j : Fin 8),
        shapeKey .c (lstep false i) (rstep false j) = false := by decide
    rw [H] at hs
    contradiction
  | e l r =>
    unfold Shape at hs
    change shapeKey .e (lkey l) (rstep true (rkey r)) = true at hs
    have H : ∀ (i : Fin 6) (j : Fin 8),
        shapeKey .e i (rstep true j) = false := by decide
    rw [H] at hs
    contradiction

/-- A candidate only needs to exclude the single structural danger class. -/
structure EdgeStable (I : Phase → List Bool → List Bool → Prop) : Prop where
  start : I .a [] []
  padding : ∀ q l r, Shape q l r → I q l r → I q (l++[false,false,false]) (r++[false,false,false])
  edgeSafe : ∀ l r, Shape .a l r → I .a l r → lkey l = 0 → rkey r ≠ 4
  closed : ∀ rule ∈ rules false, ∀ l r, Shape rule.q (rule.u++l) (rule.v++r) →
    I rule.q (rule.u++l) (rule.v++r) → I rule.q' (rule.x++l) (rule.y++r)

theorem edgeStable_stable {I : Phase → List Bool → List Bool → Prop} (s : EdgeStable I) :
    Stable false (fun q l r => Shape q l r ∧ I q l r) := by
  constructor
  · exact ⟨shape_start,s.start⟩
  · intro q l r h; exact ⟨shape_padding q l r h.1,s.padding q l r h.1 h.2⟩
  · intro q l r h hb
    obtain ⟨hq,hl,hr⟩ := shape_bad q l r h.1 hb
    subst q
    exact s.edgeSafe l r h.1 h.2 hl hr
  · intro rule hr l r h
    exact ⟨shape_closed rule hr l r h.1,s.closed rule hr l r h.1 h.2⟩

#print axioms shape_closed
#print axioms shape_bad
#print axioms edgeStable_stable
end BB6Coverage.Agent3E0LFShape
