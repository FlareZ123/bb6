# Agent 42: concrete core-only replacements for the four interval_cases

The four Mathlib-only `interval_cases` sites can be replaced with explicit finite disjunctions:

- Negative bridge input (`hy0 : y ≤ 0`, and the bridge-area bound gives `-9 ≤ y`):
  `have hc : y = -9 ∨ y = -8 ∨ y = -7 ∨ y = -6 ∨ y = -5 ∨ y = -4 ∨ y = -3 ∨ y = -2 ∨ y = -1 ∨ y = 0 := by omega`, then `rcases hc with h | h | ... | h <;> subst y <;> simp [k, m1EvenQ4BridgeStart, markerWord, d0, d1, lh, sideBit]`.
- Positive bridge input (`hypos : 1 ≤ y`, upper bound 4):
  `have hc : y = 1 ∨ y = 2 ∨ y = 3 ∨ y = 4 := by omega`; `rcases hc with h | h | h | h <;> subst y`, followed by the existing four bullets.
- q4RightShape head (`hi : i < 5)): `have hc : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 := by omega`; `rcases hc with h | h | h | h | h <;> subst i`, followed by the five existing bullets.
- left-facing bridge bits (`k < 10)): same pattern with `k = 0 ∨ ... ∨ k = 9`, then `subst k` and the existing simp.

The other first diagnostics should be local:
- `binDec_three_six`: use `simp [h1,h2,h3,binDec_zero,d1pow]` so the `d1pow 0 = []` tail closes.
- `m1EvenSourceLeftAt`: after `rw [hleft] at hcell`, normalize the list with `rw [List.append_assoc] at hcell` before `rw [hside] at hcell`.
- `m1EvenSweptLeftCell`: `rw [hcoord]` on the goal before `exact hsrc`, rather than `simpa [hcoord]`.

The later unknown encoder/run names were maxErrors cascades; if they persist after these fixes, add direct imports `S1Encoder` and `ChampionRootBridge`.
— Agent 42
