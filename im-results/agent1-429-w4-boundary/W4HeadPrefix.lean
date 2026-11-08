import W4HeadMax
import Lean.Elab.Tactic.Omega

namespace BB429W4HeadPrefix

open BB429OddExcursion BB429SourceE1Return BB429SourceE1Delta BB429W4HeadMax

/-- The head displacement after any successful run is no greater than its
record maximum. This theorem interprets the max monitor as a true
all-prefix coordinate bound. -/
theorem runWithMax_final_le_max (n : Nat) (c : Zipper) (p : Zipper × Int × Int)
    (hp : runWithMax n c = some p) : p.2.1 ≤ p.2.2 := by
  induction n generalizing c p with
  | zero =>
      simp only [runWithMax, Option.some.injEq] at hp
      subst p
      simp
  | succ n ih =>
      simp only [runWithMax] at hp
      cases h : oneWithDelta c with
      | none => simp [h] at hp
      | some a =>
          simp only [h, Option.bind_some] at hp
          cases htail : runWithMax n a.1 with
          | none => simp [htail] at hp
          | some q =>
              have hq := ih a.1 q htail
              have heq : (q.1, a.2+q.2.1, max (0:Int) (a.2+q.2.2)) = p := by
                simpa [htail] using hp
              subst p
              simp only [Prod.fst, Prod.snd]
              simp [Int.max_def]
              split <;> omega

/-- Every successfully executed prefix ends at or before the maximum
head coordinate of the entire successful run. -/
theorem runWithMax_prefix_le (m n : Nat) (c : Zipper)
    (p : Zipper × Int × Int) (hprefix : runWithMax m c = some p)
    (q : Zipper × Int × Int) (hfull : runWithMax (m+n) c = some q) :
    p.2.1 ≤ q.2.2 := by
  rw [runWithMax_add, hprefix] at hfull
  simp only [Option.bind_some] at hfull
  cases hr : runWithMax n p.1 with
  | none => simp [hr] at hfull
  | some r =>
      have hmax := runWithMax_final_le_max m c p hprefix
      have heq : (r.1, p.2.1+r.2.1, max p.2.2 (p.2.1+r.2.2)) = q := by
        simpa [hr] using hfull
      subst q
      simp only [Prod.fst, Prod.snd]
      simp [Int.max_def]
      split <;> omega

/-- Main geometry theorem: for any source S_E input, every successfully
executed primitive prefix before revisiting the E/1 cell ends at a head
position at or to the left of its entry coordinate, regardless of the
number of alternating pairs or the arbitrary untouched right suffix. -/
theorem sourceScanE_all_prefixes_right_bound (b t : Nat) (suffix : List Bool)
    (ht : t ≤ crossTime b + 1) (p : Zipper × Int × Int)
    (hprefix : runWithMax t (sourceScanE b suffix) = some p) :
    p.2.1 ≤ 0 := by
  have hlen : t + (crossTime b + 1-t) = crossTime b+1 := by omega
  have hfull := sourceScanE_e1_max b suffix
  rw [← hlen] at hfull
  have hmax := runWithMax_prefix_le t (crossTime b+1-t) (sourceScanE b suffix)
     p hprefix (z 2 (finalLeft b) true suffix, 0, 0) hfull
  simpa using hmax

#print axioms runWithMax_final_le_max
#print axioms runWithMax_prefix_le
#print axioms sourceScanE_all_prefixes_right_bound

end BB429W4HeadPrefix
