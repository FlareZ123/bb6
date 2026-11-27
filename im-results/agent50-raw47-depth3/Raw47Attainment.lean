import Raw47Late61Macro
namespace BB6.Agent50Raw47Attainment
open BB6Coverage BB6.Agent13BlankDelay BB6.Agent47CanonicalFrontier

def p : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 2,false => some (some ⟨false,true,3⟩)
  | 3,false => some (some ⟨true,false,3⟩)
  | 3,true => some (some ⟨false,true,2⟩)
  | _,_ => none
abbrev witness := BB6.Agent50CheckedLateHole.haltCompletion BB6.Agent50Raw47Late61Macro.p

theorem extends_leaf : ∀ s : Slot, p s = none ∨ p s = BB6.Agent50Raw47Late61Macro.p s := by
  intro s; rcases s with ⟨q,b⟩
  have hq : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := by omega
  rcases hq with rfl|rfl|rfl|rfl|rfl|rfl <;> cases b <;> decide

theorem witness_compatible : compatible p witness := by
  intro s t ht
  rcases extends_leaf s with h | h
  · rw [ht] at h; contradiction
  · exact BB6.Agent50CheckedLateHole.haltCompletion_compatible _ s t (h.symm.trans ht)

theorem attainment : ∃ m : Machine, compatible p m ∧ HaltsAfter m 143975 ∧ 1 ∈ delays (zeroNext m) 0 :=
  ⟨witness, witness_compatible, BB6.Agent50Raw47Late61Macro.attained⟩

theorem lower (B : Nat) (h : ∀ m, compatible p m → WeightedBound B m) : 143977 ≤ B := by
  obtain ⟨m,hm,hhalt,hd⟩ := attainment
  exact h m hm 143975 1 hhalt hd
#print axioms attainment
#print axioms lower
end BB6.Agent50Raw47Attainment
