import Raw59CanonicalAll
import Raw59Upgrade0LAData
import Raw59Upgrade0LBData
import Raw59Upgrade0LEData
import Raw59Upgrade0LFData
import Raw59Upgrade1LBData
import Raw59Upgrade1LEData
import Raw59Upgrade1LFData

set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace BB6.Agent32Raw59UpgradeAll
open BB6Coverage BB6.Agent13BlankDelay BB6.Agent8TNFPath
open BB6.Agent32Raw59 BB6.Agent32Raw59Partition

abbrev B : Nat := 4200000

theorem retained_exact :
    retained BB6.Agent32Raw59CanonicalAll.closed =
      [⟨false,false,0⟩,⟨false,false,1⟩,⟨true,false,1⟩,
       ⟨false,false,4⟩,⟨true,false,4⟩,⟨false,false,5⟩,⟨true,false,5⟩] := by decide

theorem retained_cover (mv : Move) (h : mv ∈ retained BB6.Agent32Raw59CanonicalAll.closed) :
    Cover (WeightedBound B) (child mv) := by
  rw [retained_exact] at h
  simp only [List.mem_cons,List.mem_singleton] at h
  rcases h with h|h|h|h|h|h|h
  · subst mv
    refine Cover.leaf _ ?_
    intro m hm k d hk hd
    exact Nat.le_trans (BB6.Agent32Raw59Upgrade0LA.bound m hm k d hk hd) (by decide)
  · subst mv
    exact Cover.leaf _ BB6.Agent32Raw59Upgrade0LB.bound
  · subst mv
    refine Cover.leaf _ ?_
    intro m hm k d hk hd
    exact Nat.le_trans (BB6.Agent32Raw59Upgrade1LB.bound m hm k d hk hd) (by decide)
  · subst mv
    refine Cover.leaf _ ?_
    intro m hm k d hk hd
    exact Nat.le_trans (BB6.Agent32Raw59Upgrade0LE.bound m hm k d hk hd) (by decide)
  · subst mv
    refine Cover.leaf _ ?_
    intro m hm k d hk hd
    exact Nat.le_trans (BB6.Agent32Raw59Upgrade1LE.bound m hm k d hk hd) (by decide)
  · subst mv
    refine Cover.leaf _ ?_
    intro m hm k d hk hd
    exact Nat.le_trans (BB6.Agent32Raw59Upgrade0LF.bound m hm k d hk hd) (by decide)
  · subst mv
    refine Cover.leaf _ ?_
    intro m hm k d hk hd
    exact Nat.le_trans (BB6.Agent32Raw59Upgrade1LF.bound m hm k d hk hd) (by decide)

theorem cover : Cover (WeightedBound B) p59 :=
  cover_raw59 B (by decide) BB6.Agent32Raw59CanonicalAll.closed
    BB6.Agent32Raw59CanonicalAll.closed_sound retained_cover

theorem bound (m : Machine) (hm : compatible p59 m) : WeightedBound B m :=
  cover.sound m hm

theorem exact_at_target (T : Nat) (hT : B ≤ T)
    (ho : ∀ e ∈ BB6.Agent47Canonical78.roster, e.2 ≠ p59 → Cover (WeightedBound T) e.2)
    (champ : ∃ m : BB6.Coverage.RawMachine, BB6.Coverage.HaltsAt (BB6.Coverage.tickRaw m) T) :
    BB6.Coverage.ExactBB6 T := by
  apply BB6.Agent47Canonical78.exact_at_target T (by omega) _ champ
  intro e he
  by_cases eq : e.2 = p59
  · rw [eq]
    refine Cover.leaf _ ?_
    intro m hm k d hk hd
    exact Nat.le_trans (bound m hm k d hk hd) hT
  · exact ho e he eq

#print axioms retained_cover
#print axioms cover
#print axioms bound
#print axioms exact_at_target
end BB6.Agent32Raw59UpgradeAll
