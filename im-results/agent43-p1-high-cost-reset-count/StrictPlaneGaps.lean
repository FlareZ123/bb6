import Lean
namespace BB6.Agent43StrictPlane

def first (M W : Nat) : Nat := W/M+1
def last (M q W : Nat) := (W+q-3)/M

/-- The strict predecessor guard is exactly a closed terminal interval. -/
theorem strict_interval_iff (M q W z : Nat) (hM : 0<M) (hq : 3≤q) :
    (∃ c, 1≤c ∧ c+3≤q ∧ M*z=W+c) ↔ first M W≤z ∧ z≤last M q W := by
  unfold first last
  constructor
  · rintro ⟨c,hc,hc',he⟩
    have hlo : W<M*z := by omega
    have hhi : M*z≤W+q-3 := by omega
    have hlo' := (Nat.div_lt_iff_lt_mul hM).2 (by simpa [Nat.mul_comm] using hlo : W<z*M)
    have hhi' := (Nat.le_div_iff_mul_le hM).2 (by simpa [Nat.mul_comm] using hhi : z*M≤W+q-3)
    omega
  · rintro ⟨hlo,hhi⟩
    have hlo' := (Nat.div_lt_iff_lt_mul hM).1 (show W/M<z by omega)
    have hhi' := (Nat.le_div_iff_mul_le hM).1 hhi
    rw [Nat.mul_comm z M] at hlo' hhi'
    exact ⟨M*z-W,by omega,by omega,by omega⟩

/-- Ordered weight intervals cannot overlap, even after terminal clipping. -/
theorem interval_order (M q W V : Nat) (hM : 0<M) (h : W+q≤V) :
    last M q W < first M V := by
  unfold first last
  have hd := Nat.div_le_div_right (show W+q-3≤V by omega) (c:=M)
  omega

abbrev Range := Nat × Nat

def InRanges (z : Nat) (xs : List Range) : Prop := ∃ r∈xs, r.1≤z ∧ z≤r.2

/-- Each interval is nonempty, in bounds, and separated from all earlier
    intervals. The cursor is the first position not yet visited. -/
inductive OrderedFrom (top : Nat) : Nat → List Range → Prop where
  | nil (cursor : Nat) : OrderedFrom top cursor []
  | cons (cursor lo hi : Nat) (xs : List Range)
      (hl : cursor≤lo) (hm : lo≤hi) (hh : hi≤top)
      (ht : OrderedFrom top (hi+1) xs) : OrderedFrom top cursor ((lo,hi)::xs)

def gaps (cursor top : Nat) : List Range → List Range
  | [] => [(cursor,top)]
  | (lo,hi)::xs => (cursor,lo-1)::gaps (hi+1) top xs

theorem in_ordered_bounds {top cursor z : Nat} {xs : List Range}
    (ho : OrderedFrom top cursor xs) (hz : InRanges z xs) : cursor≤z ∧ z≤top := by
  induction ho with
  | nil => simp [InRanges] at hz
  | cons cursor lo hi xs hl hm hh ht ih =>
    obtain ⟨r,hr,hlo,hhi⟩ := hz
    simp only [List.mem_cons] at hr
    rcases hr with rfl|hr
    · exact ⟨by omega,by omega⟩
    · obtain ⟨h1,h2⟩ := ih ⟨r,hr,hlo,hhi⟩
      exact ⟨by omega,h2⟩

/-- A single ordered interval sweep enumerates precisely the complement of
    the legal terminal intervals, without scanning live legal endpoints. -/
theorem in_gaps_iff {top cursor z : Nat} {xs : List Range}
    (ho : OrderedFrom top cursor xs) (hc : 0<cursor) :
    InRanges z (gaps cursor top xs) ↔ cursor≤z ∧ z≤top ∧ ¬ InRanges z xs := by
  induction ho with
  | nil => simp [gaps,InRanges]
  | cons cursor lo hi xs hl hm hh ht ih =>
    have htail := ih (by omega : 0<hi+1)
    have hmem : InRanges z ((lo,hi)::xs) ↔ (lo≤z ∧ z≤hi) ∨ InRanges z xs := by
      unfold InRanges
      simp only [List.mem_cons]
      constructor
      · rintro ⟨r,(rfl|hr),ha,hb⟩
        · exact Or.inl ⟨ha,hb⟩
        · exact Or.inr ⟨r,hr,ha,hb⟩
      · rintro (⟨ha,hb⟩|⟨r,hr,ha,hb⟩)
        · exact ⟨(lo,hi),Or.inl rfl,ha,hb⟩
        · exact ⟨r,Or.inr hr,ha,hb⟩
    have hgap : InRanges z (gaps cursor top ((lo,hi)::xs)) ↔
        (cursor≤z ∧ z≤lo-1) ∨ InRanges z (gaps (hi+1) top xs) := by
      simp only [gaps,InRanges,List.mem_cons]
      constructor
      · rintro ⟨r,(rfl|hr),ha,hb⟩
        · exact Or.inl ⟨ha,hb⟩
        · exact Or.inr ⟨r,hr,ha,hb⟩
      · rintro (⟨ha,hb⟩|⟨r,hr,ha,hb⟩)
        · exact ⟨(cursor,lo-1),Or.inl rfl,ha,hb⟩
        · exact ⟨r,Or.inr hr,ha,hb⟩
    rw [hgap,htail,hmem]
    constructor
    · rintro (⟨h1,h2⟩|⟨h1,h2,h3⟩)
      · refine ⟨h1,by omega,?_⟩
        rintro (⟨h3,h4⟩|h3)
        · omega
        · have h4 := in_ordered_bounds ht h3; omega
      · exact ⟨by omega,h2,by rintro (⟨h4,h5⟩|h4); omega; exact h3 h4⟩
    · rintro ⟨h1,h2,h3⟩
      by_cases h : z<lo
      · exact Or.inl ⟨h1,by omega⟩
      · have hhi : hi<z := by
          by_cases hhi : hi<z
          · exact hhi
          · exact False.elim (h3 (Or.inl ⟨by omega,by omega⟩))
        exact Or.inr ⟨by omega,h2,fun h => h3 (Or.inr h)⟩

#print axioms strict_interval_iff
#print axioms interval_order
#print axioms in_ordered_bounds
#print axioms in_gaps_iff
end BB6.Agent43StrictPlane
