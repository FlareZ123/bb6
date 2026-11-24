# Endpoint-independent cost bounds from the P1 carry obstruction

**Strongest claim.** For a critical-root CountCone history with index n≥14, if the Boolean carry prefix of length K≤n is impossible, then every such history has total cost m<K, irrespective of its endpoint. The arithmetic core of this implication is locally kernel-checked with Lean 4.36.0-rc2 in [WallListCore.lean](WallListCore.lean); the original-source lift and exact carry composition in [WallListSource.lean](WallListSource.lean) require the full source dependency check. Four restart-family cylinders are immediate corollaries once the source wrapper is accepted. No whole-P1 or BB(6) decision is claimed.

## Why the wall hypothesis disappears

For a critical CountCone history the witnesses form a duplicate-free list A of all edge-start costs, each below the cumulative cost m, containing 0 whenever m>0. The step is governed by the exact source equation
```
(d-1)+14*2^n = 2^e*(D-1)+2*(m+n+3), e=t+1>0.
```
The invariant is
```
2+14*2^n*Σ_{s∈A}2^s = 2^m*(d-1)+2*Σ_{s∈A}(n+3+s)*2^s.
```
The root right counter is 3 and each child has odd right counter c+4. Thus d-1=2v for a natural v. Divide the identity by two:
```
1+7*2^n*Σ_{s∈A}2^s = 2^m*v+Σ_{s∈A}(n+3+s)*2^s.
```
For 1≤K≤min(n,m), reduction modulo 2^K gives precisely the characteristic-list constraint
```
Σ_{s∈A, s<K}(n+3+s)*2^s ≡ 1 (mod 2^K).
```
Agent50's [characteristic-list bridge](../agent50-p1-dyadic-width/WallPrefixListBridge.lean) translates this to Boolean selection bits with x_0=1. An impossible prefix therefore forbids ANY critical-root history with m≥K, without a shifted-wall assumption, high-depth restart analysis, or a known terminal offset.

## Consequence for two fourth-edge restart families

The family equations and four carry exclusions are in [Agent50's certificate](../agent50-p1-dyadic-width/wall_prefix_carry_cylinders.md). The restart cost is m_R=14u-2n-3, while the wall cost after the suffix is m_R+n+9 (see Agent9's PR #109). The older wall-only wrapper used m_R as the wall cost, which was incorrect as an application to those suffixes; the new endpoint-independent theorem removes that mismatch entirely. Agent50's already checked terminal-cost inequalities give n≤m_R; hence the four prefix exclusions directly rule out the actual restart endpoint and every later endpoint of those histories, provided the source lift passes. This does not cover the rest of the two progressions or other P1 branches.

## Evidence and next step

- `witness_root`: [propext, Classical.choice, Quot.sound].
- `witness_step`, `wall_from_witness`, `witness_mod_prefix`: [propext, Quot.sound].
- All four were compiled locally with Lean 4.36.0-rc2, without sorryAx or native_decide. The generic arithmetic statement is stronger than the earlier wall-only list bridge; it does not rely on a prepared endpoint.
- Original-source `source_cost_witness`, `source_countcone_cost_lt` and the four `source_no_restart_family*` theorems await exact source-dependency closure and axiom audit. The exact GitHub checkout is unavailable locally (DNS failure); the existing manual targeted wall-telescoping workflow compiles the new modules. Run 45345687040 tests the older wall-specific wrapper at b60725b; its result cannot certify the new endpoint-independent theorem.
- Agent9's PR #109 independently composed the wall-specific list identity on the older branch; do not duplicate that route. The next useful task is to exploit the stronger all-endpoint cost cap for uncovered parameters, with a validated source bridge.
