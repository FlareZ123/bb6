import DyadicCheckerDuality
import DyadicOpenMonotone

namespace BB6.Agent21Duality
open BB6.Agent42ModularCone

/-- Once the executable checker has excluded a signed state, increasing
    the dyadic precision never retracts that exclusion. This is a
    theorem of the exact inverse-word semantics, not an empirical scan. -/
theorem excluded_monotone_precision (b : Nat) (s : Pair)
    (hb : excluded b s=true) : excluded (b+1) s=true := by
  apply (excluded_open_duality (b+1) s).mpr
  intro ho
  exact ((excluded_open_duality b s).mp hb)
    (BB6.Agent21Dyadic.OpenMonotone.open_at_down _ _ b ho)

/-- Exclusions remain valid for all further integer bit budgets. -/
theorem excluded_monotone_add (b k : Nat) (s : Pair)
    (hb : excluded b s=true) : excluded (b+k) s=true := by
  apply (excluded_open_duality (b+k) s).mpr
  intro ho
  exact ((excluded_open_duality b s).mp hb)
    (BB6.Agent21Dyadic.OpenMonotone.open_at_down_add _ _ b k ho)

theorem excluded_monotone_le (b c : Nat) (hbc : b≤c) (s : Pair)
    (hb : excluded b s=true) : excluded c s=true := by
  have h := excluded_monotone_add b (c-b) s hb
  have hsum : b+(c-b)=c := by omega
  rwa [hsum] at h

/-- Existing finite checker certificates survive BOTH increasing precision
    and passing to an arbitrary congruent signed descendant cylinder. -/
theorem excluded_monotone_congr (b c : Nat) (hbc : b≤c)
    (s t : Pair)
    (hx : Cong b s.x t.x) (hy : Cong b s.y t.y)
    (hb : excluded b s=true) : excluded c t=true := by
  have hs : residue b s=residue b t := by
    cases s with
    | mk sx sy =>
      cases t with
      | mk tx ty =>
        simp only [residue]
        rw [cong_mod hx,cong_mod hy]
  have heq : excluded b s=excluded b t := by
    unfold excluded
    rw [hs]
  have ht : excluded b t=true := by
    rw [←heq]
    exact hb
  exact excluded_monotone_le b c hbc t ht

#print axioms excluded_monotone_precision
#print axioms excluded_monotone_le
#print axioms excluded_monotone_congr
end BB6.Agent21Duality
