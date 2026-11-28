import Q0151ResidueSemantics

/-!
A sound finite-control/finite-alphabet overapproximation for the q0-151
push/pop macro certificate. Each push stores one abstract left-segment symbol.
At each pop we may restore ANY symbol from the global Saved invariant, even
if the actual stack would force a particular one. An empty stack restores
the distinguished blank symbol and remains empty. Thus this is coarser than
ordinary pushdown reachability but permits a finite independent closure test.

This theorem is generic: the q0-151 source macro interpretation and the
814-control/50-symbol closed certificate must still be supplied.
-/

namespace BB6.Agent5Q0151StackSaturation

inductive Action (C S R : Type) where
  | stay (next : C)
  | push (next : C) (saved : S)
  | pop (request : R)
  | bad
  deriving DecidableEq, Repr

def SafeAction {C S R : Type} (Good : C → Prop)
    (Saved : S → Prop) (resume : R → S → C) : Action C S R → Prop
  | .stay c => Good c
  | .push c s => Good c ∧ Saved s
  | .pop r => ∀ s, Saved s → Good (resume r s)
  | .bad => False

inductive MacroStep {C S R : Type} (delta : C → List (Action C S R))
    (resume : R → S → C) (blank : S) :
    C → List S → C → List S → Prop where
  | stay {c d st} (h : Action.stay d ∈ delta c) :
      MacroStep delta resume blank c st d st
  | push {c d st symbol} (h : Action.push d symbol ∈ delta c) :
      MacroStep delta resume blank c st d (symbol :: st)
  | pop_some {c r symbol tail} (h : Action.pop r ∈ delta c) :
      MacroStep delta resume blank c (symbol :: tail) (resume r symbol) tail
  | pop_empty {c r} (h : Action.pop r ∈ delta c) :
      MacroStep delta resume blank c [] (resume r blank) []

inductive Reach {C S R : Type} (delta : C → List (Action C S R))
    (resume : R → S → C) (blank : S) (start : C) :
    C → List S → Prop where
  | init : Reach delta resume blank start start []
  | extend {c st d st'} :
      Reach delta resume blank start c st →
      MacroStep delta resume blank c st d st' →
      Reach delta resume blank start d st'

variable {C S R : Type} {delta : C → List (Action C S R)}
  {resume : R → S → C} {blank : S}
  {Good : C → Prop} {Saved : S → Prop}

theorem step_preserves
    (closed : ∀ c, Good c → ∀ a, a ∈ delta c →
      SafeAction Good Saved resume a)
    (hblank : Saved blank)
    {c st d st'}
    (step : MacroStep delta resume blank c st d st')
    (hc : Good c) (hst : List.Forall Saved st) :
    Good d ∧ List.Forall Saved st' := by
  cases step with
  | stay h =>
      exact ⟨closed _ hc _ h, hst⟩
  | push h =>
      have hsafe := closed _ hc _ h
      exact ⟨hsafe.1, .cons hsafe.2 hst⟩
  | pop_some h =>
      cases hst with
      | cons hsymbol htail =>
          exact ⟨(closed _ hc _ h) _ hsymbol, htail⟩
  | pop_empty h =>
      exact ⟨(closed _ hc _ h) _ hblank, .nil⟩

theorem reachable_safe
    (closed : ∀ c, Good c → ∀ a, a ∈ delta c →
      SafeAction Good Saved resume a)
    (hblank : Saved blank) {start : C} (hstart : Good start)
    {c st} (hr : Reach delta resume blank start c st) :
    Good c ∧ List.Forall Saved st := by
  induction hr with
  | init => exact ⟨hstart, .nil⟩
  | extend _ step ih =>
      exact step_preserves closed hblank step ih.1 ih.2

theorem reachable_no_bad
    (closed : ∀ c, Good c → ∀ a, a ∈ delta c →
      SafeAction Good Saved resume a)
    (hblank : Saved blank) {start : C} (hstart : Good start)
    {c st} (hr : Reach delta resume blank start c st) :
    Action.bad ∉ delta c := by
  intro hbad
  have hc := (reachable_safe closed hblank hstart hr).1
  exact closed c hc .bad hbad

#print axioms step_preserves
#print axioms reachable_safe
#print axioms reachable_no_bad

end BB6.Agent5Q0151StackSaturation
