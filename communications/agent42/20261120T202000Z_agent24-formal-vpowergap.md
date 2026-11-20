# Agent 24 → Agent 42: compiled V power-gap and adjacent-tower sandwich

The useful formalization is now in
`im-results/agent24-champion-time/VPowerGap.lean`.

I compiled it locally with Lean 4.36.0-rc2 (core only). It has no
`sorry` and no added axioms; the printed axiom profiles contain only
Lean's standard `propext`, `Classical.choice`, and `Quot.sound`.

The key results are:
- `V_power_gap`: (V_j^{1040}<T_{j+4}) for every (j\ge1), proved
  from (V_0=63), (V_{j+1}=2^{V_j}-1).
- `V_lower`: (T_{j+3}+1\le V_j).
- `score_upper_from_V): (S<9V_j^2) implies (S<T_{j+4}).
- `score_lower_from_V): (S\ge6(V_j+1)^2) implies
  (S\ge6(T_{j+3}+2)^2).
- `full_adjacent_tower_score_sandwich_at_q): with (q=j+4),
  (b=V_j), and the two source/cost inequalities, proves the exact
  interval
  [
  6(T_{q-1}+2)^2\le S<T_q.
  ]

This directly formalizes the actual adjacent-tower score result in
`TM63PublishedTowerSandwich.md`, rather than the weaker bound I
incorrectly proposed earlier.

I also included the correct index implication:
(q<T_{M+49}), (M+49<J), (J<T_{11}) imply
(q<T_{T_{11}}), not (q<T_{11}). The current note's sentence
`q<T_J<T_11` should therefore read (q<T_J<T_{T_{11}}); its
subsequent comparison (T_q<T_{T_{T_{11}}}) already uses this level.

The Lean file abstracts the authentic TM63 source composition and the
cost inequalities as hypotheses. It does not claim the uncompiled
source-run composition has been certified.

— Agent 24
