import CountedQ4Prefix
import Lean.Elab.Tactic.Omega

namespace BB6Coverage.Agent48M0EvenEightValuationSweepFacts

open BB6Coverage.Agent48Champion
open BB6Coverage.Agent6Q4Prefix

/-- After a counted left sweep over 3t ones, the new head and its two
leftward/forward boundary cells are zero, provided the following d0 block
begins with two zeros. -/
theorem sweptLeft_zeroBoundary (t : Nat) (T : Int → Bool) (h : Int)
    (hleft : T (h-(3*t:Int)-1) = false)
    (hzero : T (h-(3*t:Int)) = false)
    (hright : T (h+1) = false) :
    sweptLeft (3*t) T h (h-(3*t:Int)-1) = false ∧
    sweptLeft (3*t) T h (h-(3*t:Int)) = false ∧
    sweptLeft (3*t) T h (h-(3*t:Int)+1) = false := by
  have hpLeft := sweptLeft_preserves_left (3*t) T h
    (h-(3*t:Int)-1) (by omega)
  have hpHead := sweptLeft_preserves_left (3*t) T h
    (h-(3*t:Int)) (by omega)
  constructor
  · rw [hpLeft]
    exact hleft
  constructor
  · rw [hpHead]
    exact hzero
  · by_cases ht : t = 0
    · subst t
      simp [sweptLeft,hright]
    · have hpos : 0 < 3*t := by omega
      have hlen : (3*t-1)+1 = 3*t := by omega
      have hcoord : h-((3*t-1:Int)) = h-(3*t:Int)+1 := by omega
      have hp := sweptLeft_leftmost (3*t-1) T h
      simpa [hlen,hcoord] using hp

/-- The left sweep shifts 3t ones rightward, adjoining any fixed 12-one
suffix, so the state-1 scan sees exactly 4+t consecutive d1 blocks. -/
theorem sweptLeft_creates_rightOnes (t : Nat) (T : Int → Bool) (h : Int)
    (hfixed : ∀ i : Nat, i < 12 →
      T (h+2+(i:Int)) = true) :
    rightOnes (sweptLeft (3*t) T h)
      (h-(3*t:Int)+2) (4+t) := by
  have hcell : ∀ k : Nat, k < 3*(4+t) →
      sweptLeft (3*t) T h
        (h-(3*t:Int)+2+(k:Int)) = true := by
    intro k hk
    by_cases hlt : k < 3*t
    · by_cases hlast : k+1 = 3*t
      · have heq : h-(3*t:Int)+2+(k:Int) = h+1 := by omega
        rw [heq]
        have hpos : 0 < 3*t := by omega
        have hlen : (3*t-1)+1 = 3*t := by omega
        have hp := sweptLeft_plus1 (3*t-1) T h
        simpa [hlen] using hp
      · have hj : (3*t-2-k)+1 < 3*t := by omega
        have heq : h-(3*t:Int)+2+(k:Int) =
            h-((3*t-2-k:Int)) := by omega
        rw [heq]
        exact sweptLeft_block (3*t) (3*t-2-k) T h hj
    · have hx : h+2 ≤ h-(3*t:Int)+2+(k:Int) := by omega
      have heq : h-(3*t:Int)+2+(k:Int) =
          h+2+((k-3*t:Int)) := by omega
      rw [sweptLeft_preserves_right (3*t) T h _ hx, heq]
      exact hfixed (k-3*t) (by omega)
  intro j hj
  refine ⟨hcell (3*j) (by omega), ?_⟩
  refine ⟨hcell (3*j+1) (by omega), hcell (3*j+2) (by omega)⟩

#print axioms sweptLeft_zeroBoundary
#print axioms sweptLeft_creates_rightOnes

end BB6Coverage.Agent48M0EvenEightValuationSweepFacts
