import CoverBridge
import SparseBlankDelay

namespace F197.CoverBridge
open BB6Coverage (Cover Machine PartialMachine compatible NeverHalts Move)
open BB6.Agent13BlankDelay (WeightedBound)

def rows : List (Option (Option Move)) := [
  some (some ⟨true,true,1⟩), some (some ⟨false,true,4⟩),
  some (some ⟨true,true,2⟩), some (some ⟨false,false,4⟩),
  some (some ⟨false,true,3⟩), none,
  some (some ⟨false,true,4⟩), some (some ⟨false,true,0⟩),
  some (some ⟨true,false,5⟩), some (some ⟨false,false,1⟩),
  some (some ⟨true,false,0⟩), some (some ⟨true,false,5⟩)]

/-- The exact twelve-row manifest in A0,A1,...,F0,F1 order. -/
theorem table_eq_rows : table = (fun s =>
    (rows[2*s.1.val + (if s.2 then 1 else 0)]?).getD none) := by
  funext s
  rcases s with ⟨⟨n,hn⟩,b⟩
  have h : n=0 ∨ n=1 ∨ n=2 ∨ n=3 ∨ n=4 ∨ n=5 := by omega
  rcases h with h|h|h|h|h|h <;> subst n <;> cases b <;> rfl

theorem only_hole (s : BB6Coverage.Slot) : table s = none ↔ s = (2,true) := by
  rcases s with ⟨⟨n,hn⟩,b⟩
  have h : n=0 ∨ n=1 ∨ n=2 ∨ n=3 ∨ n=4 ∨ n=5 := by omega
  rcases h with h|h|h|h|h|h <;> subst n <;> cases b <;> decide +revert

/-- Conditional weighted leaf at any score; the sole unresolved input is
    blank liveness of the exact literal stream machine. -/
theorem weighted_leaf (B : Nat)
    (h : ∀ n, F197.run n ⟨.A,F197.blank,F197.blank⟩ ≠ none) :
    Cover (WeightedBound B) table := by
  apply Cover.leaf
  intro m hm k d hk _
  have hn := never_of_stream_live h m hm (k+1)
  rw [hk.2] at hn
  contradiction

#print axioms table_eq_rows
#print axioms only_hole
#print axioms weighted_leaf
end F197.CoverBridge
