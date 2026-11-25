import PartialAudit
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace BB6.Agent16ResidualCover
open BB6Coverage BB6.Agent13BlankDelay BB6.Agent47PartialAudit

structure Accepted (B : Nat) where
  table : PartialMachine
  sound : ∀ m, compatible table m → WeightedBound B m

def sameTable (p q : PartialMachine) : Bool :=
  (List.finRange 6).all fun state =>
    [false,true].all fun symbol => decide (p (state,symbol) = q (state,symbol))

theorem sameTable_sound {p q : PartialMachine} (h : sameTable p q = true) : p = q := by
  funext s
  rcases s with ⟨state,symbol⟩
  have h1 := List.all_eq_true.mp h state (List.mem_finRange state)
  have h2 := List.all_eq_true.mp h1 symbol (by cases symbol <;> simp)
  exact of_decide_eq_true h2

def covered (as : List (Accepted B)) (p : PartialMachine) : Bool :=
  as.any (fun c => sameTable p c.table)

theorem covered_sound {B : Nat} {as : List (Accepted B)} {p : PartialMachine}
    (h : covered as p = true) : ∀ m, compatible p m → WeightedBound B m := by
  obtain ⟨c,_,hc⟩ := List.any_eq_true.mp h
  rw [sameTable_sound hc]
  exact c.sound

def remaining (as : List (Accepted B)) (rs : List (List Move × PartialMachine)) :=
  rs.filter (fun e => !(covered as e.2))

theorem consume {B : Nat} {root : PartialMachine} {rs : List (List Move × PartialMachine)}
    (as : List (Accepted B))
    (h : ∀ m, compatible root m → WeightedBound B m ∨
      ∃ e ∈ rs, compatible e.2 m) :
    ∀ m, compatible root m → WeightedBound B m ∨
      ∃ e ∈ remaining as rs, compatible e.2 m := by
  intro m hm
  rcases h m hm with hb | ⟨e,he,hc⟩
  · exact Or.inl hb
  · by_cases hh : covered as e.2 = true
    · exact Or.inl (covered_sound hh m hc)
    · have hf : covered as e.2 = false := by cases h : covered as e.2 <;> simp_all
      exact Or.inr ⟨e,List.mem_filter.mpr ⟨he, by simp [hf]⟩,hc⟩

def nonhalt (B : Nat) (p : PartialMachine)
    (h : ∀ m, compatible p m → NeverHalts m) : Accepted B :=
  ⟨p,fun m hm => weighted_never B m (h m hm)⟩

#print axioms consume
end BB6.Agent16ResidualCover
