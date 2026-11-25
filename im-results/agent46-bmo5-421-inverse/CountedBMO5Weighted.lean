import CountedBMO5Bound
import SparseBlankDelay

namespace CountedBMO5Pair.Coverage
open BB6Coverage BB6.Agent13BlankDelay

abbrev machine421 := Counted421.Coverage.machine

theorem delays252 : delays (zeroNext machine252) 0=[0] := by decide
theorem delays421 : delays (zeroNext machine421) 0=[0] := by decide
theorem delays754 : delays (zeroNext machine754) 0=[0] := by decide

/-- For a complete table with no incoming blank delay, the raw count is
already the exact score used in weighted first-one coverage. -/
theorem weighted_iff_decided (B : Nat) (m : Machine)
    (hd : delays (zeroNext m) 0=[0]) :
    WeightedBound B m ↔ DecidedBelow B m := by
  constructor
  · intro hw
    classical
    by_cases hn : NeverHalts m
    · exact Or.inl hn
    · obtain ⟨n,hh⟩ := not_never m hn
      exact Or.inr ⟨n,by simpa using hw n 0 hh (by simp [hd]),hh⟩
  · intro h n d hh hdelay
    have he : d=0 := by simpa [hd] using hdelay
    subst d
    rcases h with hn|⟨k,hk,hhalt⟩
    · have ht := hn (n+1)
      rw [hh.2] at ht
      contradiction
    · have he := halting_time_unique m n k hh hhalt
      omega

def singleton (m : Machine) : PartialMachine := fun s => some (m s)

theorem singleton_cover (B : Nat) (m : Machine) (hd : delays (zeroNext m) 0=[0])
    (h : DecidedBelow B m) : Cover (WeightedBound B) (singleton m) := by
  refine Cover.leaf _ ?_
  intro m' hm
  have he : m'=m := by
    funext s
    exact hm s (m s) rfl
  subst m'
  exact (weighted_iff_decided B m hd).mpr h

theorem all_three_weighted_iff (B : Nat) :
    (WeightedBound B machine252 ∧ WeightedBound B machine421 ∧ WeightedBound B machine754)
      ↔ allThreeBelow B := by
  rw [weighted_iff_decided B machine252 delays252,weighted_iff_decided B machine421 delays421,
    weighted_iff_decided B machine754 delays754]
  rfl

theorem singleton252_of_bound {B : Nat} (h : ∀ i, Cap.rootOf (Cap.halt i)=1 → W i+3≤B) :
    Cover (WeightedBound B) (singleton machine252) :=
  singleton_cover B machine252 delays252 ((decidedBelow252_iff B).mpr h)

theorem singleton421_of_bound {B : Nat} (h : ∀ i, Cap.rootOf (Cap.halt i)=2 → W i+8≤B) :
    Cover (WeightedBound B) (singleton machine421) :=
  singleton_cover B machine421 delays421 ((decidedBelow421_iff B).mpr h)

theorem singleton754_of_bound {B : Nat} (h : ∀ i, Cap.rootOf (Cap.halt i)=3 → W i+18≤B) :
    Cover (WeightedBound B) (singleton machine754) :=
  singleton_cover B machine754 delays754 ((decidedBelow754_iff B).mpr h)

/-- No new whole parent cylinder is claimed: these are three exact complete
table descendants of the residual roster. -/
theorem all_three_singleton_covers {B L : Nat}
    (hb : 18+800*(L+5)*4^L≤B)
    (ht : ∀ i, L<i → Cap.rootOf (Cap.halt i)≠1 ∧
                          Cap.rootOf (Cap.halt i)≠2 ∧
                          Cap.rootOf (Cap.halt i)≠3) :
    Cover (WeightedBound B) (singleton machine252) ∧
    Cover (WeightedBound B) (singleton machine421) ∧
    Cover (WeightedBound B) (singleton machine754) := by
  obtain ⟨h1,h2,h3⟩ := allThreeBelow_of_tail_exclusion B L hb ht
  exact ⟨singleton_cover B machine252 delays252 h1,
    singleton_cover B machine421 delays421 h2,
    singleton_cover B machine754 delays754 h3⟩

#print axioms delays252
#print axioms delays421
#print axioms delays754
#print axioms all_three_weighted_iff
#print axioms all_three_singleton_covers
end CountedBMO5Pair.Coverage
