import TM63DirectRootComposition
namespace BB6.Agent26F412Graft
open BB6ChampionArithmetic BB6Coverage.Agent48DirectRoot
private theorem bound_pow (b : Nat) : b ≤ 2^b := by
  induction b with
  | zero => simp
  | succ b ih =>
    have hp : 0 < 2^b := Nat.pow_pos (by decide)
    rw [Nat.pow_succ]
    omega
theorem increment_ge_pow (m n a b : Nat) : 2^b ≤ proposedIncrementCost m n a b := by
  have hb := bound_pow b
  unfold proposedIncrementCost
  omega
theorem second_increment_le_section (n m a b : Nat) :
    proposedIncrementCost (nextMarker m % 3) (n+1) (nextExponent m a b) (nextRight b) ≤
      (sectionResult (n+2) m a b).cost := by
  simp only [sectionResult]
  omega
private theorem sum_bound (a b c d e f g : Nat) : b ≤ a+b+c+d+e+f+g+7 := by omega
theorem section_two_bound (n m a b : Nat) (hsmall : 200 ≤ nextRight b) :
    2^200 ≤ (sectionResult (n+2) m a b).cost := by
  have hp : 2^200 ≤ 2^(nextRight b) := Nat.pow_le_pow_right (by decide) hsmall
  exact Nat.le_trans hp (Nat.le_trans (increment_ge_pow (nextMarker m % 3) (n+1)
    (nextExponent m a b) (nextRight b)) (second_increment_le_section n m a b))
theorem threeSection_ge_first (rootSteps L n a b : Nat) :
    (sectionResult n 2 a b).cost ≤ threeSectionMoves rootSteps L n a b + 7 := by
  unfold threeSectionMoves
  dsimp only
  exact sum_bound _ _ _ _ _ _ _
theorem section_two_bound' (n m a b : Nat) (hn : 2 ≤ n) (hb : 200 ≤ nextRight b) :
    2^200 ≤ (sectionResult n m a b).cost := by
  obtain ⟨k, hk⟩ : ∃ k, n = k+2 := ⟨n-2, by omega⟩
  rw [hk]
  exact section_two_bound k m a b hb
theorem score_ge_pow200 (rootSteps L n a b : Nat) (hn : 2 ≤ n)
    (hb : 200 ≤ nextRight b) :
    2^200 ≤ threeSectionMoves rootSteps L n a b + 7 :=
  Nat.le_trans (section_two_bound' n 2 a b hn hb) (threeSection_ge_first rootSteps L n a b)
/-- Equality transport prevents kernel evaluation of gigantic powers. -/
theorem champion_ge_pow200 : 2^200 ≤ proposedTM63Moves + 7 :=
  Eq.mp (congrArg (fun n : Nat => 2^200 ≤ n+7) threeSectionMoves_root)
    (score_ge_pow200 27959 3 7 6 63 (by decide) (by decide))
theorem f412_le_champion : 9217091204829760959746640857348768637582783 ≤ proposedTM63Moves+7 := by
  exact Nat.le_trans (by decide : 9217091204829760959746640857348768637582783 ≤ 2^200) champion_ge_pow200
#print axioms champion_ge_pow200
#print axioms f412_le_champion
end BB6.Agent26F412Graft
