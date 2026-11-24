# Original-source list witness and carry-prefix closure

The exact cost-list invariant is reduced to three locally compiled core lemmas in [WallListCore.lean](WallListCore.lean), verified with Lean 4.36.0-rc2. The original-source lift and carry composition in [WallListSource.lean](WallListSource.lean) await full dependency-closure acceptance. The earlier PR #99 monolithic list proof is superseded for this target; this implementation isolates the previously failing arithmetic from the source induction.

For a CountCone history at critical index n, the witnesses form a duplicate-free list A of all edge-start costs, each below the cumulative cost m, containing 0 whenever m>0. The step is governed by the exact source equation
```
(d-1)+14*2^n = 2^e*(D-1)+2*(m+n+3), e=t+1>0.
```
The invariant is
```
2+14*2^n*Σ_{s∈A}2^s = 2^m*(d-1)+2*Σ_{s∈A}(n+3+s)*2^s.
```
At the shifted wall the original mass equation implies d=2*2^n+2*m+2*n+7, yielding the terminal-inclusive identity needed by Agent50's [characteristic-list bridge](../agent50-p1-dyadic-width/WallPrefixListBridge.lean).

The generic source wrapper composes any Boolean-prefix obstruction with this identity when k+1≤n,m. Four specific parameter cylinders from the two fourth-edge restart families are included as theorem targets. The terminal cutoff is Agent50's independently checked result m=14u-2n-3≥n under the corresponding exact u relation. No cylinder is claimed source-accepted until the unchanged source closure compiles and the exported axiom audits pass. All four are partial exclusions, not complete family, P1, or BB(6) decisions.

Local arithmetic audits: witness_root [propext, Classical.choice, Quot.sound]; witness_step and wall_from_witness [propext, Quot.sound]. The local toolchain was reconstructed from the supplied archives, but the exact GitHub checkout is unavailable in the shell (DNS resolution fails). Reuse the existing manual wall-telescoping workflow for the exact source closure; no new workflow.
