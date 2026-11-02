import BlankRank
import Lean.Elab.Tactic.Omega
namespace BB6.Agent3
open BB6.Agent46

def ReachableSection (a k : Nat) : Prop :=
  ∃ n : Nat, BB6.Agent8Section.run secNext n (some (5,1))=some (a,k)

/-- Exact finite time bound for reaching any prescribed Machine C section
    state, based on the strict source-proved linear rank growth. -/
theorem reach_iff_finite (a k : Nat) :
    ReachableSection a k ↔
    ∃ n : Fin (a+2*k+1),
      BB6.Agent8Section.run secNext n.val (some (5,1))=some (a,k) := by
  constructor
  · rintro ⟨n,hn⟩
    refine ⟨⟨n, ?_⟩, hn⟩
    have hr := blank_rank_time n a k hn
    omega
  · rintro ⟨n,hn⟩
    exact ⟨n.val, hn⟩

/-- Fully constructive, terminating decision procedure for the reachability
    of each fixed section state from the genuine blank-origin entry. -/
def section_reach_decidable (a k : Nat) :
    Decidable (ReachableSection a k) := by
  apply decidable_of_iff
    (∃ n : Fin (a+2*k+1),
      BB6.Agent8Section.run secNext n.val (some (5,1))=some (a,k))
  exact (reach_iff_finite a k).symm

#print axioms section_reach_decidable
#print axioms reach_iff_finite
end BB6.Agent3
