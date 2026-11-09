import SheepAffine
import CoprimeAffine

namespace SheepAperiodic
open SheepAffine SheepWord

/-- No strictly increasing infinite sequence can traverse the same nonempty
ordered sequence of generic Sheep first-even branches at every macro step.
This is a theorem of the exact source-derived affine branch identities.
The independent source bridge from the physical machine to the branch map
is not imported into this standalone arithmetic module. -/
theorem no_infinite_repeated_word
    (w : List (Nat × Nat)) (hw : w ≠ [])
    (x : Nat → Nat)
    (hpath : ∀ i, WordPath w (x i) (x (i+1)))
    (hinc : ∀ i, x i < x (i+1)) : False := by
  let p := wordParams w
  have hL : 1 < p.L := nonempty_word_scale_gt_one hw
  have hcop : p.L.Coprime p.N := word_coprime w
  have haff : ∀ i, (p.L:Int) * x (i+1) =
      (p.N:Int) * x i + ((p.P:Int)-(p.Q:Int)) := by
    intro i
    exact holds_to_int_affine p (x i) (x (i+1)) (word_path_holds w _ _ (hpath i))
  exact coprime_affine_no_infinite_growth p.L p.N _ hL hcop x hinc haff

/-- Applies to any eventually periodic itinerary represented as a series
of complete generic word-path blocks. A finite prefix before the blocks
is irrelevant: x 0 is chosen at the start of the periodic tail. -/
theorem no_eventually_periodic_generic_tail
    (w : List (Nat × Nat)) (hw : w ≠ [])
    (x : Nat → Nat)
    (hpath : ∀ i, WordPath w (x i) (x (i+1)))
    (hinc : ∀ i, x i < x (i+1)) : False :=
  no_infinite_repeated_word w hw x hpath hinc

#print axioms no_infinite_repeated_word
#print axioms no_eventually_periodic_generic_tail
end SheepAperiodic
