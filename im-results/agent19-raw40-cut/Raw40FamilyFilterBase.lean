import CanonicalPartial
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace BB6.Agent19Raw40.FamilyFilter
open BB6Coverage BB6.Agent13BlankDelay BB6.Agent47CanonicalFrontier

def tableExtends (p q : PartialMachine) : Bool :=
  (List.finRange 6).all fun s => [false,true].all fun b =>
    match p (s,b) with
    | none => true
    | some t => decide (q (s,b) = some t)

theorem extends_sound {p q : PartialMachine} (h : tableExtends p q = true)
    {m : Machine} (hm : compatible q m) : compatible p m := by
  intro slot t ht
  rcases slot with ⟨s,b⟩
  have hs := List.all_eq_true.mp h s (List.mem_finRange s)
  have hb : b ∈ [false,true] := by cases b <;> simp
  have htq := List.all_eq_true.mp hs b hb
  rw [ht] at htq
  exact hm (s,b) t (of_decide_eq_true htq)

theorem extends_quotient {p q : PartialMachine} (h : tableExtends p q = true)
    {m : Machine} (hm : TNFQuotientCompatible q m) : TNFQuotientCompatible p m := by
  obtain ⟨e,he,hq⟩ := hm
  exact ⟨e,he,extends_sound h hq⟩

def kept (closed : List PartialMachine) (roster : List (List Move × PartialMachine)) :=
  roster.filter fun e => !(closed.any fun p => tableExtends p e.2)

/-- Remove whole certified subcylinders from an arbitrary canonical roster. -/
theorem filter_sound {B : Nat} {r : PartialMachine}
    {roster : List (List Move × PartialMachine)} {closed : List PartialMachine}
    (hroot : ∀ m, TNFQuotientCompatible r m → WeightedBound B m ∨
      ∃ e ∈ roster, TNFQuotientCompatible e.2 m)
    (hclosed : ∀ p ∈ closed, ∀ m, TNFQuotientCompatible p m → WeightedBound B m) :
    ∀ m, TNFQuotientCompatible r m → WeightedBound B m ∨
      ∃ e ∈ kept closed roster, TNFQuotientCompatible e.2 m := by
  intro m hm
  rcases hroot m hm with h | ⟨e,he,hq⟩
  · exact Or.inl h
  · cases ht : closed.any (fun p => tableExtends p e.2) with
    | false => exact Or.inr ⟨e,by simp [kept,he,ht],hq⟩
    | true =>
      obtain ⟨p,hp,h⟩ := List.any_eq_true.mp ht
      exact Or.inl (hclosed p hp m (extends_quotient h hq))

#print axioms filter_sound
end BB6.Agent19Raw40.FamilyFilter
