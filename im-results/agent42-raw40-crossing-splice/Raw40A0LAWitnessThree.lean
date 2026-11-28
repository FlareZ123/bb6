import Raw40A0LABase

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace BB6.Agent42Raw40A0LAWitness
open BB6Coverage BB6.Agent13BlankDelay BB6.Agent47CanonicalFrontier

namespace W0RB
/-- Literal total halting witness from the saved A0LA frontier audit:
    1RB0LA_1RC1RE_0RD0RB_1LD1LA_1RF0RC_1LAHHH. The only undefined transition is its F1 halt. -/
def witness : Machine := fun s =>
  match s.1.val,s.2 with
  | 0,false => some ⟨true,true,1⟩
  | 0,true => some ⟨false,false,0⟩
  | 1,false => some ⟨true,true,2⟩
  | 1,true => some ⟨true,true,4⟩
  | 2,false => some ⟨false,true,3⟩
  | 2,true => some ⟨false,true,1⟩
  | 3,false => some ⟨true,false,3⟩
  | 3,true => some ⟨true,false,0⟩
  | 4,false => some ⟨true,true,5⟩
  | 4,true => some ⟨false,true,2⟩
  | 5,false => some ⟨true,false,0⟩
  | _,_ => none

def parent : PartialMachine := BB6.Agent19Raw40.A0LA.child ⟨false,true,1⟩

theorem witness_compatible : compatible parent witness := by
  intro s t ht
  rcases s with ⟨q,b⟩
  have hq : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := by omega
  rcases hq with rfl|rfl|rfl|rfl|rfl|rfl <;> cases b <;> first
    | have h : parent (_,_) = none := by decide
      rw [h] at ht
      contradiction
    | cases ht <;> rfl

theorem witness_halts : HaltsAfter witness 1212 := by
  constructor <;> rfl

theorem witness_delay : 0 ∈ delays (zeroNext witness) 0 := by decide

/-- Even before proving this five-hole family has a finite upper bound,
    a smaller weighted upper bound is impossible, via the original blank. -/
theorem witness_sharp (B : Nat) (hB : B < 1213) :
    ∃ m, compatible parent m ∧ ¬ WeightedBound B m := by
  refine ⟨witness,witness_compatible,?_⟩
  intro hb
  have h := hb 1212 0 witness_halts witness_delay
  omega

#print axioms witness_sharp
end W0RB

namespace W1LA
/-- Literal total halting witness from the saved A0LA frontier audit:
    1RB0LA_1RC1RE_0RD1LA_1LD1LA_1RF0RB_0RCHHH. The only undefined transition is its F1 halt. -/
def witness : Machine := fun s =>
  match s.1.val,s.2 with
  | 0,false => some ⟨true,true,1⟩
  | 0,true => some ⟨false,false,0⟩
  | 1,false => some ⟨true,true,2⟩
  | 1,true => some ⟨true,true,4⟩
  | 2,false => some ⟨false,true,3⟩
  | 2,true => some ⟨true,false,0⟩
  | 3,false => some ⟨true,false,3⟩
  | 3,true => some ⟨true,false,0⟩
  | 4,false => some ⟨true,true,5⟩
  | 4,true => some ⟨false,true,1⟩
  | 5,false => some ⟨false,true,2⟩
  | _,_ => none

def parent : PartialMachine := BB6.Agent19Raw40.A0LA.child ⟨true,false,0⟩

theorem witness_compatible : compatible parent witness := by
  intro s t ht
  rcases s with ⟨q,b⟩
  have hq : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := by omega
  rcases hq with rfl|rfl|rfl|rfl|rfl|rfl <;> cases b <;> first
    | have h : parent (_,_) = none := by decide
      rw [h] at ht
      contradiction
    | cases ht <;> rfl

theorem witness_halts : HaltsAfter witness 1138 := by
  constructor <;> rfl

theorem witness_delay : 0 ∈ delays (zeroNext witness) 0 := by decide

/-- Even before proving this five-hole family has a finite upper bound,
    a smaller weighted upper bound is impossible, via the original blank. -/
theorem witness_sharp (B : Nat) (hB : B < 1139) :
    ∃ m, compatible parent m ∧ ¬ WeightedBound B m := by
  refine ⟨witness,witness_compatible,?_⟩
  intro hb
  have h := hb 1138 0 witness_halts witness_delay
  omega

#print axioms witness_sharp
end W1LA

namespace W1RB
/-- Literal total halting witness from the saved A0LA frontier audit:
    1RB0LA_1RC1RE_0RD1RB_1LD1LA_1RF0RC_0LDHHH. The only undefined transition is its F1 halt. -/
def witness : Machine := fun s =>
  match s.1.val,s.2 with
  | 0,false => some ⟨true,true,1⟩
  | 0,true => some ⟨false,false,0⟩
  | 1,false => some ⟨true,true,2⟩
  | 1,true => some ⟨true,true,4⟩
  | 2,false => some ⟨false,true,3⟩
  | 2,true => some ⟨true,true,1⟩
  | 3,false => some ⟨true,false,3⟩
  | 3,true => some ⟨true,false,0⟩
  | 4,false => some ⟨true,true,5⟩
  | 4,true => some ⟨false,true,2⟩
  | 5,false => some ⟨false,false,3⟩
  | _,_ => none

def parent : PartialMachine := BB6.Agent19Raw40.A0LA.child ⟨true,true,1⟩

theorem witness_compatible : compatible parent witness := by
  intro s t ht
  rcases s with ⟨q,b⟩
  have hq : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := by omega
  rcases hq with rfl|rfl|rfl|rfl|rfl|rfl <;> cases b <;> first
    | have h : parent (_,_) = none := by decide
      rw [h] at ht
      contradiction
    | cases ht <;> rfl

theorem witness_halts : HaltsAfter witness 1755 := by
  constructor <;> rfl

theorem witness_delay : 0 ∈ delays (zeroNext witness) 0 := by decide

/-- Even before proving this five-hole family has a finite upper bound,
    a smaller weighted upper bound is impossible, via the original blank. -/
theorem witness_sharp (B : Nat) (hB : B < 1756) :
    ∃ m, compatible parent m ∧ ¬ WeightedBound B m := by
  refine ⟨witness,witness_compatible,?_⟩
  intro hb
  have h := hb 1755 0 witness_halts witness_delay
  omega

#print axioms witness_sharp
end W1RB

end BB6.Agent42Raw40A0LAWitness
