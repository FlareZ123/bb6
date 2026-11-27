import StrictWord64
namespace BB6.Agent43StrictWord
open BB6.Agent9BatchCarry (Interior Walk)
open BB6.Agent9FoldedProbe
open BB6.Agent43StrictPlane

/-- Same ordered interval enumeration as dense_birthloc.cpp; the C++
    early break when first>top is merely an optimization of empty tails. -/
def wordRanges (q k top : Nat) (B : Nat) : Nat → List Range
  | 0 => []
  | m+1 =>
    let W := q*B+dw64 B
    let lo := first (2^k) W
    let hi := min top (last (2^k) q W)
    if lo≤hi then (lo,hi)::wordRanges q k top (B+1) m
    else wordRanges q k top (B+1) m

theorem mem_wordRanges (q k top B m z : Nat) (hk : k≤64) (hb : B+m≤2^k) :
    InRanges z (wordRanges q k top B m) ↔
    z≤top ∧ ∃ D, B≤D ∧ D<B+m ∧
      first (2^k) (weight q k D)≤z ∧ z≤last (2^k) q (weight q k D) := by
  induction m generalizing B with
  | zero => simp [wordRanges,InRanges]; omega
  | succ m ih =>
    have hB : B<2^k := by omega
    have htail := ih (B+1) (by omega)
    rw [wordRanges, ←weight_fast q k B hk hB]
    split <;> rename_i he
    · have hh : InRanges z ((first (2^k) (weight q k B),min top (last (2^k) q (weight q k B))) :: wordRanges q k top (B+1) m) ↔
        (first (2^k) (weight q k B)≤z ∧ z≤min top (last (2^k) q (weight q k B))) ∨ InRanges z (wordRanges q k top (B+1) m) := by
        simp only [InRanges,List.mem_cons]
        constructor
        · rintro ⟨r,(rfl|hr),hlo,hhi⟩
          · exact Or.inl ⟨hlo,hhi⟩
          · exact Or.inr ⟨r,hr,hlo,hhi⟩
        · rintro (⟨hlo,hhi⟩|⟨r,hr,hlo,hhi⟩)
          · exact ⟨_,Or.inl rfl,hlo,hhi⟩
          · exact ⟨r,Or.inr hr,hlo,hhi⟩
      rw [hh,htail]
      constructor
      · rintro (⟨hlo,hhi⟩|⟨ht,D,hD,hDm,hlo,hhi⟩)
        · exact ⟨Nat.le_trans hhi (Nat.min_le_left _ _), B,by omega,by omega,hlo,Nat.le_trans hhi (Nat.min_le_right _ _)⟩
        · exact ⟨ht,D,by omega,by omega,hlo,hhi⟩
      · rintro ⟨ht,D,hD,hDm,hlo,hhi⟩
        by_cases hDB : D=B
        · subst D
          exact Or.inl ⟨hlo,Nat.le_min.mpr ⟨ht,hhi⟩⟩
        · exact Or.inr ⟨ht,D,by omega,by omega,hlo,hhi⟩
    · rw [htail]
      constructor
      · rintro ⟨ht,D,hD,hDm,hlo,hhi⟩
        exact ⟨ht,D,by omega,by omega,hlo,hhi⟩
      · rintro ⟨ht,D,hD,hDm,hlo,hhi⟩
        have hDB : D≠B := by
          intro h; subst D
          exact he (Nat.le_trans hlo (Nat.le_min.mpr ⟨ht,hhi⟩))
        exact ⟨ht,D,by omega,by omega,hlo,hhi⟩

theorem ordered_wordRanges (q k top B m cursor : Nat) (hk : k≤64) (hb : B+m≤2^k)
    (hc : ∀ D, B≤D → D<B+m → cursor≤first (2^k) (weight q k D)) :
    OrderedFrom top cursor (wordRanges q k top B m) := by
  induction m generalizing B cursor with
  | zero => exact OrderedFrom.nil cursor
  | succ m ih =>
    rw [wordRanges,←weight_fast q k B hk (by omega)]
    split <;> rename_i he
    · apply OrderedFrom.cons cursor _ _ _ (hc B (by omega) (by omega)) he (Nat.min_le_left _ _)
      apply ih (B+1) _ (by omega)
      intro D hD hDm
      have hsep := weight_separate q k B D (by omega) (by omega)
      have hord := interval_order (2^k) q (weight q k B) (weight q k D) (Nat.two_pow_pos _) hsep
      exact Nat.le_trans (Nat.succ_le_succ (Nat.min_le_right _ _)) hord
    · exact ih (B+1) cursor (by omega) (fun D hD hDm => hc D (by omega) (by omega))

def allRanges (q k : Nat) : List Range := wordRanges q k ((q+k-2)/2) 0 (2^k)

theorem canon_le_top {q z : Nat} (hz : Canon q z) : z≤(q-2)/2 := by
  have h := hz.2
  unfold fold complement at h
  have hi := Nat.min_le_right z (q-2-z)
  rw [h] at hi
  omega

/-- The gaps emitted by the dense sweep are exactly the endpoints with
    no strict folded parent. This binds the interval algorithm to the
    actual source Walk, rather than a numerical approximation. -/
theorem gap_iff_no_parent (q k z : Nat) (hq : 3≤q) (hk : k≤64)
    (hz : Canon (q+k) z) :
    InRanges z (gaps 1 ((q+k-2)/2) (allRanges q k)) ↔ ¬ ∃ a, FoldedWalk q a k z := by
  have ho : OrderedFrom ((q+k-2)/2) 1 (allRanges q k) := by
    unfold allRanges
    apply ordered_wordRanges _ _ _ _ _ _ hk (by omega)
    intro D _ _
    unfold first
    exact Nat.succ_le_succ (Nat.zero_le _)
  rw [in_gaps_iff ho (by decide)]
  have hzt := canon_le_top hz
  have hz1 := hz.1.1
  rw [folded_walk_iff_interval q k z hq hz]
  unfold allRanges
  rw [mem_wordRanges _ _ _ _ _ _ hk (by omega)]
  simp [hzt,hz1]

/-- A selected interval supplies the actual folded source predecessor. -/
theorem interval_parent (q k B z : Nat) (hq : 3≤q) (hk : k≤64) (hB : B<2^k)
    (hz : Canon (q+k) z) (hl : first (2^k) (q*B+dw64 B)≤z)
    (hh : z≤last (2^k) q (q*B+dw64 B)) :
    FoldedWalk q (fold q (2^k*z-(q*B+dw64 B))) k z := by
  have h := (strict_interval_iff (2^k) q (q*B+dw64 B) z (Nat.two_pow_pos _) hq).2 ⟨hl,hh⟩
  obtain ⟨c,hc,hcq,he⟩ := h
  have he' : c+weight q k B=2^k*z := by rw [weight_fast q k B hk hB]; omega
  have hw := walk_of_word q c k z B ⟨hc,hcq⟩ he'
  exact ⟨c,z,hw,congrArg (fold q) (by omega),hz.2⟩

#print axioms mem_wordRanges
#print axioms ordered_wordRanges
#print axioms gap_iff_no_parent
#print axioms interval_parent
end BB6.Agent43StrictWord
