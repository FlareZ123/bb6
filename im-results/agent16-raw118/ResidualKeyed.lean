import ResidualCover

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace BB6.Agent16ResidualCover
open BB6Coverage BB6.Agent13BlankDelay

def digit : Option Transition → Nat
  | none => 0
  | some none => 1
  | some (some mv) => 2 + 12 * mv.write.toNat + 6 * mv.right.toNat + mv.next.val

def tableKey (p : PartialMachine) : Nat :=
  (List.finRange 6).foldl (fun n q =>
    (n * 26 + digit (p (q,false))) * 26 + digit (p (q,true))) 0

inductive AcceptedTree (B : Nat) where
  | empty
  | node (key : Nat) (cert : Accepted B) (left right : AcceptedTree B)

def lookup (p : PartialMachine) (k : Nat) : AcceptedTree B → Bool
  | .empty => false
  | .node key cert l r =>
    if k < key then lookup p k l else
    if key < k then lookup p k r else sameTable p cert.table

/-- Keys route the lookup; exact table equality is checked at the hit.
    Soundness needs no ordering, injectivity, or correct generated keys. -/
theorem lookup_sound {B : Nat} {p : PartialMachine} {k : Nat} {t : AcceptedTree B}
    (h : lookup p k t = true) : ∀ m, compatible p m → WeightedBound B m := by
  induction t with
  | empty => simp [lookup] at h
  | node key cert l r ihl ihr =>
    simp only [lookup] at h
    split at h
    · exact ihl h
    · split at h
      · exact ihr h
      · rw [sameTable_sound h]
        exact cert.sound

def remainingTree (t : AcceptedTree B) (rs : List (List Move × PartialMachine)) :=
  rs.filter (fun e => !(lookup e.2 (tableKey e.2) t))

theorem consumeTree {B : Nat} {root : PartialMachine} {rs : List (List Move × PartialMachine)}
    (t : AcceptedTree B)
    (h : ∀ m, compatible root m → WeightedBound B m ∨
      ∃ e ∈ rs, compatible e.2 m) :
    ∀ m, compatible root m → WeightedBound B m ∨
      ∃ e ∈ remainingTree t rs, compatible e.2 m := by
  intro m hm
  rcases h m hm with hb | ⟨e,he,hc⟩
  · exact Or.inl hb
  · cases hh : lookup e.2 (tableKey e.2) t with
    | true => exact Or.inl (lookup_sound hh m hc)
    | false => exact Or.inr ⟨e,List.mem_filter.mpr ⟨he, by simp [hh]⟩,hc⟩

def AcceptedTree.size : AcceptedTree B → Nat
  | .empty => 0
  | .node _ _ l r => l.size + r.size + 1

#print axioms lookup_sound
#print axioms consumeTree
end BB6.Agent16ResidualCover
