import HighFarCompose

namespace BB6.Agent2F321Bulk
open BB6.Agent31F321Density

/-! Deterministic root prefix: ten maximal High + one exact sourceNext
epochs, each a source-kernel proof rather than a sampled observation. -/

theorem root_first_10 : CounterReach 1 1 53 1182 1 := by
  have h0 : CounterReach 1 1 1 6 1 :=
    CounterReach.step CounterReach.nil (CounterMove.equal 1)
  have e0 : CounterReach 6 1 2 18 2 := by
    apply high_then_sourceNext
    · decide
    · decide
  have h1 : CounterReach 1 1 3 18 2 :=
    counter_reach_trans h0 e0
  have e1 : CounterReach 18 2 3 26 2 := by
    apply high_then_sourceNext
    · decide
    · decide
  have h2 : CounterReach 1 1 6 26 2 :=
    counter_reach_trans h1 e1
  have e2 : CounterReach 26 2 3 58 2 := by
    apply high_then_sourceNext
    · decide
    · decide
  have h3 : CounterReach 1 1 9 58 2 :=
    counter_reach_trans h2 e2
  have e3 : CounterReach 58 2 4 110 1 := by
    apply high_then_sourceNext
    · decide
    · decide
  have h4 : CounterReach 1 1 13 110 1 :=
    counter_reach_trans h3 e3
  have e4 : CounterReach 110 1 5 222 1 := by
    apply high_then_sourceNext
    · decide
    · decide
  have h5 : CounterReach 1 1 18 222 1 :=
    counter_reach_trans h4 e4
  have e5 : CounterReach 222 1 6 418 2 := by
    apply high_then_sourceNext
    · decide
    · decide
  have h6 : CounterReach 1 1 24 418 2 :=
    counter_reach_trans h5 e5
  have e6 : CounterReach 418 2 7 442 2 := by
    apply high_then_sourceNext
    · decide
    · decide
  have h7 : CounterReach 1 1 31 442 2 :=
    counter_reach_trans h6 e6
  have e7 : CounterReach 442 2 7 538 2 := by
    apply high_then_sourceNext
    · decide
    · decide
  have h8 : CounterReach 1 1 38 538 2 :=
    counter_reach_trans h7 e7
  have e8 : CounterReach 538 2 7 922 2 := by
    apply high_then_sourceNext
    · decide
    · decide
  have h9 : CounterReach 1 1 45 922 2 :=
    counter_reach_trans h8 e8
  have e9 : CounterReach 922 2 8 1182 1 := by
    apply high_then_sourceNext
    · decide
    · decide
  have h10 : CounterReach 1 1 53 1182 1 :=
    counter_reach_trans h9 e9
  exact h10

#print axioms root_first_10
end BB6.Agent2F321Bulk
