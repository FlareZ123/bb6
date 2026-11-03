import ReverseResidue
import TerminalExit

namespace CascadeGapJoin

/-- Uniform elimination of both scalar inverse-image mechanisms at the final
    terminal height, using the independent odd-residue and even-gap lemmas. -/
theorem no_reset_image_at_exit (n : Nat) (hn : 10 ≤ n)
    (hc : n%6=0 ∨ n%6=1 ∨ n%6=2 ∨ n%6=3) :
    ∃ i,
      (8*2^(n-1)+n-1-(2*n+3)*2^(i+1))%3 ≠ 2 ∧
      ∀ m, ¬ (6*2^m-1 ≤ (8*2^(n-1)+n-1-(2*n+3)*2^(i+1)) ∧
        (8*2^(n-1)+n-1-(2*n+3)*2^(i+1)) ≤ 8*2^m-3) := by
  obtain ⟨i, hstay, hexit⟩ := TerminalExit.exact_exit_exists n hn
  obtain ⟨hlow, hhigh⟩ := TerminalExit.terminal_exit_band n i hn hstay hexit
  have htpos : 0 < 8*2^(n-1)+n-1-(2*n+3)*2^(i+1) := by omega
  have hle : (2*n+3)*2^(i+1) ≤ 8*2^(n-1)+n-1 := by omega
  have hpos : CascadeOdd.ancestor (2^(n-1)) n (i+1) +
      (2*n+3)*2^(i+1) = 8*2^(n-1)+n-1 := by
    simp only [CascadeOdd.ancestor]
    exact Nat.sub_add_cancel hle
  have hodd := ReverseResidue.mod3_ancestor n (i+1) (by omega) hc hpos
  change (8*2^(n-1)+n-1-(2*n+3)*2^(i+1))%3 ≠ 2 at hodd
  exact ⟨i, hodd, fun m => TerminalExit.no_even_band n m _ (by omega) hlow hhigh⟩

#print axioms no_reset_image_at_exit

/-- The four remaining small dyadic exits, n=6,7,8,9, have the same
    non-image property. They require direct arithmetic because n<10. -/
theorem small_exit_6 :
    ∃ i,
      (8*2^(6-1)+6-1-(2*6+3)*2^(i+1))%3 ≠ 2 ∧
      ∀ m, ¬ (6*2^m-1 ≤ (8*2^(6-1)+6-1-(2*6+3)*2^(i+1)) ∧
        (8*2^(6-1)+6-1-(2*6+3)*2^(i+1)) ≤ 8*2^m-3) := by
  refine ⟨2, by decide, ?_⟩
  intro m
  exact TerminalExit.no_even_band 6 m _ (by decide) (by decide) (by decide)

theorem small_exit_7 :
    ∃ i,
      (8*2^(7-1)+7-1-(2*7+3)*2^(i+1))%3 ≠ 2 ∧
      ∀ m, ¬ (6*2^m-1 ≤ (8*2^(7-1)+7-1-(2*7+3)*2^(i+1)) ∧
        (8*2^(7-1)+7-1-(2*7+3)*2^(i+1)) ≤ 8*2^m-3) := by
  refine ⟨2, by decide, ?_⟩
  intro m
  exact TerminalExit.no_even_band 7 m _ (by decide) (by decide) (by decide)

theorem small_exit_8 :
    ∃ i,
      (8*2^(8-1)+8-1-(2*8+3)*2^(i+1))%3 ≠ 2 ∧
      ∀ m, ¬ (6*2^m-1 ≤ (8*2^(8-1)+8-1-(2*8+3)*2^(i+1)) ∧
        (8*2^(8-1)+8-1-(2*8+3)*2^(i+1)) ≤ 8*2^m-3) := by
  refine ⟨3, by decide, ?_⟩
  intro m
  exact TerminalExit.no_even_band 8 m _ (by decide) (by decide) (by decide)

theorem small_exit_9 :
    ∃ i,
      (8*2^(9-1)+9-1-(2*9+3)*2^(i+1))%3 ≠ 2 ∧
      ∀ m, ¬ (6*2^m-1 ≤ (8*2^(9-1)+9-1-(2*9+3)*2^(i+1)) ∧
        (8*2^(9-1)+9-1-(2*9+3)*2^(i+1)) ≤ 8*2^m-3) := by
  refine ⟨4, by decide, ?_⟩
  intro m
  exact TerminalExit.no_even_band 9 m _ (by decide) (by decide) (by decide)

/-- Every index from n=6 onward in the four excluded residue classes has
    a certified arithmetic terminal height outside both reset-image families. -/
theorem all_excluded_residue_gate (n : Nat) (hn : 6 ≤ n)
    (hc : n%6=0 ∨ n%6=1 ∨ n%6=2 ∨ n%6=3) :
    ∃ i,
      (8*2^(n-1)+n-1-(2*n+3)*2^(i+1))%3 ≠ 2 ∧
      ∀ m, ¬ (6*2^m-1 ≤ (8*2^(n-1)+n-1-(2*n+3)*2^(i+1)) ∧
        (8*2^(n-1)+n-1-(2*n+3)*2^(i+1)) ≤ 8*2^m-3) := by
  by_cases h10 : 10 ≤ n
  · exact no_reset_image_at_exit n h10 hc
  have hsmall : n=6 ∨ n=7 ∨ n=8 ∨ n=9 := by omega
  rcases hsmall with h|h|h|h
  · subst n; exact small_exit_6
  · subst n; exact small_exit_7
  · subst n; exact small_exit_8
  · subst n; exact small_exit_9

#print axioms all_excluded_residue_gate
end CascadeGapJoin
