import CanonicalSearch
import WeightedTNFCertificate

namespace BB6.Agent13BlankDelay
open BB6Coverage

/-- Halting time is unique for the deterministic blank-start run. -/
private theorem haltsAfter_unique (m : Machine) (k n : Nat)
    (hk : HaltsAfter m k) (hn : HaltsAfter m n) : k = n := by
  by_cases h : k = n
  · exact h
  rcases Nat.lt_or_gt_of_ne h with hlt | hgt
  · have he : n = (k + 1) + (n - (k + 1)) := by omega
    have hz : run m n blank = none := by
      rw [he, run_append, hk.2]
      rfl
    simp [HaltsAfter, hz] at hn
  · have he : k = (n + 1) + (k - (n + 1)) := by omega
    have hz : run m k blank = none := by
      rw [he, run_append, hn.2]
      rfl
    simp [HaltsAfter, hz] at hk

/-- A primitive-step decision below B-5 implies the weighted bound B on
    the authentic first-one cylinder. The five-step margin is exact: every
    possible incoming blank delay is enumerated by List.range 6. -/
theorem decidedBelow_to_weightedBound {B : Nat} {p : PartialMachine}
    (hB : 5 ≤ B)
    (hroot : p initialSlot = some (some ⟨true, true, 1⟩))
    (m : Machine) (hc : compatible p m)
    (hdecided : DecidedBelow (B - 5) m) :
    WeightedBound B m := by
  rcases hdecided with hnever | ⟨n, hn, hhalt⟩
  · exact weighted_never B m hnever
  · intro k d hk hd
    have hkn : k = n := haltsAfter_unique m k n hk hhalt
    subst k
    have hzero := firstOne_terminal p hroot m hc
    have hpossible := delays_subset_possible p m hc 0 hzero d hd
    have hrange : d ∈ List.range 6 := (List.mem_filter.mp hpossible).1
    have hdlt : d < 6 := List.mem_range.mp hrange
    omega

/-- Convert a closed canonical audit into a weighted cover. CanonicalSearch
    proves DecidedBelow(B-5); the first-one delay lemma supplies the missing
    at-most-five primitive steps. -/
theorem canonicalAudit_to_weightedCover {B : Nat} {p : PartialMachine} {k : Nat}
    (hB : 5 ≤ B)
    (hroot : p initialSlot = some (some ⟨true, true, 1⟩))
    (a : BB6Coverage.Canonical.Audit (B - 5) p k)
    (hclosed : a.report.2 = 0) :
    Cover (WeightedBound B) p := by
  let c : Cover (DecidedBelow (B - 5)) p := a.closed_of_zero hclosed
  exact .leaf p (fun m hc =>
    decidedBelow_to_weightedBound hB hroot m hc (c.sound m hc))

/-- A closed canonical audit can be used directly as a weighted-TNF leaf. -/
def canonicalAuditTNFLeaf {B : Nat} {p : PartialMachine} {cut k : Nat}
    (hB : 5 ≤ B)
    (hroot : p initialSlot = some (some ⟨true, true, 1⟩))
    (hsupport : TNFSupport p cut)
    (hnohalt : weightedTNFNoAssignedHalt p)
    (a : BB6Coverage.Canonical.Audit (B - 5) p k)
    (hclosed : a.report.2 = 0) :
    WeightedTNFCertificate B p cut :=
  WeightedTNFCertificate.ofWeightedCover hroot hsupport hnohalt
    (canonicalAudit_to_weightedCover hB hroot a hclosed)

/-- Canonical Scoped and weighted TNF support are the same finite
    successor-closure condition. -/
theorem scoped_to_TNFSupport {p : PartialMachine} {k : Nat}
    (hp : BB6Coverage.Canonical.Scoped k p) : TNFSupport p k :=
  hp

/-- Directly package a closed result of the existing canonical search as a
    weighted-TNF certificate. The canonical search runs at B-5 because its
    DecidedBelow measure counts primitive steps, while TNF adds at most five
    blank-delay steps. -/
def canonicalSearchTNFLeaf {B : Nat} {p : PartialMachine} {k : Nat}
    (hB : 5 ≤ B)
    (hroot : p initialSlot = some (some ⟨true, true, 1⟩))
    (hnohalt : weightedTNFNoAssignedHalt p)
    (rayLimit scanLimit lassoLimit entryLimit macroLimit farLimit depth : Nat)
    (hp : BB6Coverage.Canonical.Scoped k p)
    (hk : 0 < k ∧ k ≤ 6)
    (hclosed :
      (BB6Coverage.Canonical.search (B - 5) rayLimit scanLimit lassoLimit
        entryLimit macroLimit farLimit depth k p hp hk).report.2 = 0) :
    WeightedTNFCertificate B p k :=
  canonicalAuditTNFLeaf hB hroot (scoped_to_TNFSupport hp) hnohalt
    (BB6Coverage.Canonical.search (B - 5) rayLimit scanLimit lassoLimit
      entryLimit macroLimit farLimit depth k p hp hk) hclosed

#print axioms decidedBelow_to_weightedBound
#print axioms canonicalAudit_to_weightedCover
#print axioms canonicalAuditTNFLeaf
#print axioms canonicalSearchTNFLeaf
end BB6.Agent13BlankDelay
