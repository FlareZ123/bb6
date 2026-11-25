import F412ChampionBound

namespace BB6.Agent2Raw124ChampionBound

open BB6ChampionArithmetic

/-- The existing F412 symbolic champion bound, reused without expanding
its enormous primitive-step recurrence. -/
theorem champion_ge_two_million :
    2_000_000 ≤ proposedTM63Moves+7 :=
  Nat.le_trans (by decide : 2_000_000 ≤ 2^200)
    BB6.Agent26F412Graft.champion_ge_pow200

/-- Any branch certificate at or below two million lifts to the attained
champion score by weighted-bound monotonicity's numeric premise. -/
theorem branch_bound_le_champion (B : Nat) (hB : B ≤ 2_000_000) :
    B ≤ proposedTM63Moves+7 :=
  Nat.le_trans hB champion_ge_two_million

#print axioms champion_ge_two_million
#print axioms branch_bound_le_champion

end BB6.Agent2Raw124ChampionBound
