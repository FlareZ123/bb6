module

public import SheepSourceBridge
public import BlankEven

@[expose] public section

namespace BB6.Agent16.SheepEvenSource

/-- Each machine-certified Sheep section return has our exact source relation. -/
theorem section_to_even {x y : Nat} (h : SheepBridge.SectionNext x y) :
    SheepEven.Step x y := by
  cases h with
  | triple a => exact SheepEven.Step.special a
  | general a u hu hodd => exact SheepEven.Step.generic a u hodd hu

theorem even_to_section {x y : Nat} (h : SheepEven.Step x y) :
    SheepBridge.SectionNext x y := by
  cases h with
  | special a => exact SheepBridge.SectionNext.triple a
  | generic a u hodd hu => exact SheepBridge.SectionNext.general a u hu hodd

/-- Machine-certified reachability implies our length-indexed exact path. -/
theorem reach_to_even_steps {x y : Nat}
    (h : BB6.Agent22.Sheep.Reach x y) :
    ∃ n, SheepEven.Steps n x y := by
  induction h with
  | refl x => exact ⟨0,SheepEven.Steps.nil x⟩
  | cons edge tail ih =>
      obtain ⟨n,hn⟩ := ih
      exact ⟨n+1,SheepEven.Steps.cons (section_to_even edge) hn⟩

theorem even_steps_to_reach {n x y : Nat}
    (h : SheepEven.Steps n x y) : BB6.Agent22.Sheep.Reach x y := by
  induction h with
  | nil x => exact BB6.Agent22.Sheep.Reach.refl x
  | cons edge tail ih =>
      exact BB6.Agent22.Sheep.Reach.cons (even_to_section edge) ih

theorem reach_iff_even_steps {x y : Nat} :
    BB6.Agent22.Sheep.Reach x y ↔ ∃ n, SheepEven.Steps n x y := by
  constructor
  · exact reach_to_even_steps
  · rintro ⟨n,p⟩
    exact even_steps_to_reach p

/-- Entire original six-state machine and exact induced even graph:
every finite halting witness is preserved in both directions. -/
theorem raw_halts_iff_even_power :
    BusyBeaver.IsHalt BB6.Agent22.SheepSource.Source.target ↔
      ∃ a, 2 ≤ a ∧ SheepEven.EvenReach 10 (2^a) := by
  rw [BB6.Agent22.SheepSource.raw_halts_iff_power]
  constructor
  · rintro ⟨a,ha,hr⟩
    obtain ⟨n,p⟩ := reach_to_even_steps hr
    have he : (2^a)%2=0 := by
      cases a with
      | zero => omega
      | succ k => simp [Nat.pow_succ]
    exact ⟨a,ha,(SheepEven.blank_even_reach_iff he).mp ⟨n,p⟩⟩
  · rintro ⟨a,ha,hr⟩
    have he : (2^a)%2=0 := by
      cases a with
      | zero => omega
      | succ k => simp [Nat.pow_succ]
    obtain ⟨n,p⟩ := (SheepEven.blank_even_reach_iff he).mpr hr
    exact ⟨a,ha,even_steps_to_reach p⟩

#print axioms section_to_even
#print axioms even_to_section
#print axioms raw_halts_iff_even_power

end BB6.Agent16.SheepEvenSource
