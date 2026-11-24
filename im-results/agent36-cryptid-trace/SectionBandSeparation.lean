import GrowthBands
import Lean.Elab.Tactic.Omega

namespace BB6.Agent36.SectionBandSeparation

open BB6.Agent26.GrowthBands

/-- The global source-return estimate has additive constant 135, rather than
the regular-model constant 40. This wider upper band still separates the
four established arithmetic anchors. -/
def upper135 (c : Section) : Nat := 5 * (c.n + c.tailLen) + 135

/-- A source-return edge supplied by the arbitrary-suffix section theorem:
the same lower estimate and the widened upper estimate. -/
structure Edge135 (c d : Section) : Prop where
  live : 5 ≤ c.n
  lowerBound : 8 * c.n ≤ 3 * d.n + 23
  upperBound : 3 * (d.n + d.tailLen) ≤ 8 * (c.n + c.tailLen) + 135

theorem edge_live {c d : Section} (e : Edge135 c d) : 5 ≤ d.n := by
  have := e.live
  have := e.lowerBound
  omega

theorem edge_increases {c d : Section} (e : Edge135 c d) : c.n < d.n := by
  have := e.live
  have := e.lowerBound
  omega

theorem lower_step {c d : Section} (e : Edge135 c d) :
    8 * lower c ≤ 3 * lower d := by
  have := e.live
  have := e.lowerBound
  simp [lower]
  omega

theorem upper_step {c d : Section} (e : Edge135 c d) :
    3 * upper135 d ≤ 8 * upper135 c := by
  have := e.upperBound
  simp [upper135]
  omega

theorem lower_le_n (c : Section) : lower c ≤ 5 * c.n := by
  unfold lower
  omega

theorem n_le_upper135 (c : Section) : 5 * c.n ≤ upper135 c := by
  unfold upper135
  omega

inductive Path135 : Nat → Section → Section → Prop where
  | nil (c : Section) : Path135 0 c c
  | cons {k : Nat} {c d e : Section} :
      Edge135 c d → Path135 k d e → Path135 (k + 1) c e

theorem path_n_mono {k : Nat} {c d : Section} (p : Path135 k c d) :
    c.n ≤ d.n := by
  induction p with
  | nil => exact Nat.le_refl _
  | cons e _ ih => exact Nat.le_trans (Nat.le_of_lt (edge_increases e)) ih

theorem path_strict {k : Nat} {c d : Section} (p : Path135 (k + 1) c d) :
    c.n < d.n := by
  cases p with
  | cons e p =>
    exact Nat.lt_of_lt_of_le (edge_increases e) (path_n_mono p)

/-- Equal-length paths preserve strict separation of their widened bands. -/
theorem sync_gap {k : Nat} {a b x y : Section}
    (p : Path135 k a x) (q : Path135 k b y)
    (gap : upper135 a < lower b) : upper135 x < lower y := by
  induction p generalizing b y with
  | nil a =>
    cases q
    exact gap
  | cons e p ih =>
    cases q with
    | cons f q =>
      apply ih q
      have := upper_step e
      have := lower_step f
      omega

theorem gap_n {a b : Section} (gap : upper135 a < lower b) : a.n < b.n := by
  have := n_le_upper135 a
  have := lower_le_n b
  omega

theorem sync_order {k : Nat} {a b x y : Section}
    (p : Path135 k a x) (q : Path135 k b y)
    (gap : upper135 a < lower b) : x.n < y.n :=
  gap_n (sync_gap p q gap)

theorem split_path {i j : Nat} {a z : Section}
    (p : Path135 (i + j) a z) :
    ∃ b, Path135 i a b ∧ Path135 j b z := by
  induction i generalizing a with
  | zero =>
    exact ⟨a, Path135.nil a, by simpa using p⟩
  | succ i ih =>
    rw [show i + 1 + j = i + j + 1 by omega] at p
    cases p with
    | cons e p =>
      obtain ⟨b, hb, hz⟩ := ih p
      exact ⟨b, Path135.cons e hb, hz⟩

/-- Strict order when one path has more returns, with a cross-band gap. -/
theorem offset_order {i j : Nat} {a b x y : Section}
    (p : Path135 i a x) (q : Path135 j b y) (ij : i < j)
    (gap : 3 * upper135 a < 8 * lower b) : x.n < y.n := by
  obtain ⟨k, hk⟩ : ∃ k, j = 1 + i + k := ⟨j - i - 1, by omega⟩
  subst j
  rw [show 1 + i + k = (i + k) + 1 by omega] at q
  cases q with
  | @cons _ _ d _ e q =>
    have hh := lower_step e
    have gap' : upper135 a < lower d := by omega
    obtain ⟨z, pz, qz⟩ := split_path q
    exact Nat.lt_of_lt_of_le (sync_order p pz gap') (path_n_mono qz)

/-- The wider 135-band retains the strict gaps between the four published
arithmetic anchor sections. -/
theorem base_gap135 : ∀ a b : Fin 4, a < b →
    upper135 (base a) < lower (base b) := by
  decide

theorem base_cross135 : ∀ a b : Fin 4,
    3 * upper135 (base a) < 8 * lower (base b) := by
  decide

/-- All finite paths from the four anchor sections are strictly ordered by
return count first and anchor ordinal second. -/
theorem ordered_paths {a b : Fin 4} {i j : Nat} {x y : Section}
    (p : Path135 i (base a) x) (q : Path135 j (base b) y)
    (h : i < j ∨ (i = j ∧ a < b)) : x.n < y.n := by
  rcases h with hij | ⟨hij, hab⟩
  · exact offset_order p q hij (base_cross135 a b)
  · subst j
    exact sync_order p q (base_gap135 a b hab)

theorem disjoint_paths {a b : Fin 4} {i j : Nat} {x y : Section}
    (p : Path135 i (base a) x) (q : Path135 j (base b) y)
    (h : a ≠ b ∨ i ≠ j) : x.n ≠ y.n := by
  rcases Nat.lt_trichotomy i j with hlt | heq | hgt
  · exact Nat.ne_of_lt (ordered_paths p q (Or.inl hlt))
  · have hab : a ≠ b := by
      rcases h with h | h
      · exact h
      · exact False.elim (h heq)
    have hv : a.val ≠ b.val := fun hv => hab (Fin.ext hv)
    rcases Nat.lt_or_gt_of_ne hv with hlt | hgt
    · exact Nat.ne_of_lt (ordered_paths p q (Or.inr ⟨heq, hlt⟩))
    · exact Ne.symm (Nat.ne_of_lt (ordered_paths q p (Or.inr ⟨heq.symm, hgt⟩)))
  · exact Ne.symm (Nat.ne_of_lt (ordered_paths q p (Or.inl hgt)))

#print axioms edge_live
#print axioms edge_increases
#print axioms lower_step
#print axioms upper_step
#print axioms sync_gap
#print axioms offset_order
#print axioms base_gap135
#print axioms base_cross135
#print axioms ordered_paths
#print axioms disjoint_paths

end BB6.Agent36.SectionBandSeparation
