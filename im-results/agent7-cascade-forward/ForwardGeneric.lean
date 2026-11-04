import Std

namespace CascadeForwardCert

inductive Chain (R : Nat → Nat → Prop) (start : Nat) : Nat → Prop where
  | root : Chain R start start
  | append {h u : Nat} (hr : Chain R start h) (hp : R h u) : Chain R start u

theorem chain_lower {R : Nat → Nat → Prop}
    (strict : ∀ h u, R h u → h < u) {s u : Nat}
    (hr : Chain R s u) : s ≤ u := by
  induction hr with
  | root => omega
  | @append h u hr hp ih =>
      exact Nat.le_trans ih (Nat.le_of_lt (strict h u hp))

theorem chain_split {R : Nat → Nat → Prop}
    (functional : ∀ h u v, R h u → R h v → u = v)
    {s t x : Nat} (hedge : R s t) (hr : Chain R s x) :
    x = s ∨ Chain R t x := by
  induction hr with
  | root => exact Or.inl rfl
  | @append h u hr hp ih =>
      rcases ih with heq | ht
      · subst h
        have heq : t = u := functional s t u hedge hp
        subst u
        exact Or.inr Chain.root
      · exact Or.inr (Chain.append ht hp)

structure Edge where
  u : Nat
  k : Nat
  t : Nat
  odd : Bool

def check (good : Nat → Edge → Bool) (bad : Nat → Bool) (cap : Nat) :
    Nat → List Edge → Bool
  | h, [] => decide (cap < h)
  | h, e :: es =>
      if bad h then false else if good h e then check good bad cap e.u es else false

theorem check_sound {R : Nat → Nat → Prop}
    (strict : ∀ h u, R h u → h < u)
    (functional : ∀ h u v, R h u → R h v → u = v)
    (good : Nat → Edge → Bool) (good_sound : ∀ h e, good h e = true → R h e.u)
    (bad : Nat → Bool) (cap : Nat) :
    ∀ es h, check good bad cap h es = true →
       ∀ x, Chain R h x → x ≤ cap → bad x = true → False := by
  intro es
  induction es with
  | nil =>
      intro h hc x hx hcap hbad
      have hbound : cap < h := by simpa [check] using hc
      have hlo := chain_lower strict hx
      omega
  | cons e es ih =>
      intro h hc x hx hcap hbad
      have hb : bad h = false := by
        by_cases hh : bad h = true
        · simp [check, hh] at hc
        · cases hh2 : bad h <;> simp_all
      have hg : good h e = true := by
        by_cases hh : good h e = true
        · exact hh
        · cases hh2 : good h e <;> simp_all [check]
      have ht : check good bad cap e.u es = true := by
        simpa [check,hb,hg] using hc
      have he := good_sound h e hg
      rcases chain_split functional he hx with heq | hx'
      · subst x
        simp [hb] at hbad
      · exact ih e.u ht x hx' hcap hbad

/-- Split a long finite kernel check into independently checked blocks. -/
def segment (good : Nat → Edge → Bool) (bad : Nat → Bool) (finish : Nat) :
    Nat → List Edge → Bool
  | h, [] => decide (h = finish)
  | h, e :: es =>
      if bad h then false else if good h e then segment good bad finish e.u es else false

theorem segment_append (good : Nat → Edge → Bool) (bad : Nat → Bool)
    (cap finish : Nat) : ∀ es h tail,
      segment good bad finish h es = true →
      check good bad cap h (es ++ tail) = check good bad cap finish tail := by
  intro es
  induction es with
  | nil =>
      intro h tail hs
      have he : h = finish := of_decide_eq_true
        (show decide (h=finish)=true by simpa [segment] using hs)
      subst h
      rfl
  | cons e es ih =>
      intro h tail hs
      have hb : bad h = false := by
        by_cases hh : bad h = true
        · simp [segment, hh] at hs
        · cases hh2 : bad h <;> simp_all
      have hg : good h e = true := by
        by_cases hh : good h e = true
        · exact hh
        · cases hh2 : good h e <;> simp_all [segment]
      have hrest : segment good bad finish e.u es = true := by
        simpa [segment,hb,hg] using hs
      simp only [List.cons_append]
      simp only [check,hb,hg, ↓reduceIte]
      exact ih e.u tail hrest

#print axioms chain_split
#print axioms check_sound
#print axioms segment_append

end CascadeForwardCert
