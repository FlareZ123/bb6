import SharpRaw95
import Raw99Data
import Raw103Data
import SharpRaw105

namespace BB6.Agent32FourSharp
open BB6Coverage BB6.Agent13BlankDelay

/-- The shared eight assigned transitions, with the F1 choice explicit. -/
def literal (mv : Move) : PartialMachine := fun (q,b) =>
  match q.val,b with
  | 0,false => some (some ⟨true,true,1⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 1,true => some (some ⟨true,false,5⟩)
  | 2,false => some (some ⟨false,true,3⟩)
  | 3,false => some (some ⟨true,false,3⟩)
  | 3,true => some (some ⟨true,true,4⟩)
  | 4,true => some (some ⟨false,false,1⟩)
  | 5,true => some (some mv)
  | _,_ => none

def parents : List PartialMachine :=
  [literal ⟨false,true,3⟩, literal ⟨false,true,4⟩,
   literal ⟨false,true,5⟩, literal ⟨true,true,5⟩]

theorem eq95 : BB6.Agent3Raw95.p95 = literal ⟨false,true,3⟩ := by
  funext s
  rcases s with ⟨q,b⟩
  have hq : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := by omega
  rcases hq with rfl|rfl|rfl|rfl|rfl|rfl <;> cases b <;> decide

theorem eq99 : BB6.Agent2Raw99.p99 = literal ⟨false,true,4⟩ := by
  funext s
  rcases s with ⟨q,b⟩
  have hq : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := by omega
  rcases hq with rfl|rfl|rfl|rfl|rfl|rfl <;> cases b <;> decide

theorem eq103 : BB6.Agent3Raw103.p103 = literal ⟨false,true,5⟩ := by
  funext s
  rcases s with ⟨q,b⟩
  have hq : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := by omega
  rcases hq with rfl|rfl|rfl|rfl|rfl|rfl <;> cases b <;> decide

theorem eq105 : BB6.Agent3Raw105.p105 = literal ⟨true,true,5⟩ := by
  funext s
  rcases s with ⟨q,b⟩
  have hq : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := by omega
  rcases hq with rfl|rfl|rfl|rfl|rfl|rfl <;> cases b <;> decide

theorem compatible_unique (a b : Move) (m : Machine)
    (ha : compatible (literal a) m) (hb : compatible (literal b) m) : a = b := by
  have h1 : m (5,true) = some a := ha (5,true) (some a) rfl
  have h2 : m (5,true) = some b := hb (5,true) (some b) rfl
  exact Option.some.inj (h1.symm.trans h2)

theorem parent_bound (B : Nat) (hB : 379 ≤ B) :
    ∀ p ∈ parents, ∀ m, compatible p m → WeightedBound B m := by
  intro p hp m hm
  simp only [parents, List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl|rfl|rfl|rfl
  · exact (BB6.Agent31SharpRaw95.exact95 B).2 hB m (eq95 ▸ hm)
  · exact (BB6.Agent2Raw99.exact99 B).2 (by omega) m (eq99 ▸ hm)
  · exact (BB6.Agent3Raw103.exact103 B).2 (by omega) m (eq103 ▸ hm)
  · exact (BB6.Agent31SharpRaw105.exact105 B).2 (by omega) m (eq105 ▸ hm)

theorem parent_covers (B : Nat) (hB : 379 ≤ B) :
    ∀ p ∈ parents, Cover (WeightedBound B) p := by
  intro p hp
  exact Cover.leaf p (parent_bound B hB p hp)

theorem union_exact (B : Nat) :
    (∀ m, (∃ p ∈ parents, compatible p m) → WeightedBound B m) ↔ 379 ≤ B := by
  constructor
  · intro h
    apply (BB6.Agent31SharpRaw95.exact95 B).1
    intro m hm
    exact h m ⟨literal ⟨false,true,3⟩, by simp [parents], eq95 ▸ hm⟩
  · intro h m hm
    obtain ⟨p,hp,hc⟩ := hm
    exact parent_bound B h p hp m hc

#print axioms eq95
#print axioms eq99
#print axioms eq103
#print axioms eq105
#print axioms compatible_unique
#print axioms parent_covers
#print axioms union_exact
end BB6.Agent32FourSharp
