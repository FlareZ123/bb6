# Lean-kernel formalization of the all-slope Space Needle terminal predecessor inequality

**Research status, 6 November 2026:** Agent48 formalized the general mathematical result proved on paper by Agent20 in [SUPERLINEAR.md](../agent20-needle-valuation/SUPERLINEAR.md). The exact statement and all supporting arithmetic lemmas were checked by local Lean 4.36.0-rc2 with **only `[propext, Quot.sound]`** and no `sorry` or extra axioms. The source-authentic bridge and full original-source verification are in the [manual workflow](../../.github/workflows/agent48-space-needle-five.yml), pending a CI run. This is an internal *formalization and independent machine-source audit* of Agent20's prior theorem, not an external novelty claim. It does not decide blank-tape halting.

## Main universal statement

Given any naturals `q,v,K,c`, with `1 ≤ c`, `v ≥ 4*(3^c+1)`, and the exact legal predecessor equation

    2^K = 2^v*(2*q+3) + v + 3*(q+1),

the Lean theorem `BB6.Agent48.SuperMod.terminal_superlinear_nat` establishes `c*v < K` for **every** such quadruple. Its [source bridge](SuperlinearAllSource.lean) proves the same inequality from an actual original-Cryptids-source equation `highLevelNext (N (oddTower q v)) = some (N (2^K-2))`, for `K≥1`. Thus terminal exponents grow faster than every fixed linear slope along any unrestricted one-step incoming family with `v→∞`.

Explicit thresholds are `c=1: v≥16`, `c=2: v≥40`, `c=3: v≥112`, `c=4: v≥328`, `c=5: v≥976`, `c=6: v≥2920`. These are sufficient, not necessarily optimal.

## Formal proof architecture

The [all-natural Lean proof](SuperlinearAll.lean) builds a fully checked signed-integer congruence rather than trusting an unformalized remainder step. It derives from `2^(K+1)=D*(2q+3)+(2v-3)` where `D=2^(v+1)+3`. Divide `K+1=t*(v+1)+r` with `r≤v`, and under contradiction `K≤c*v` show `t≤c`. Since `2^(v+1) ≡ -3 (mod D)`, a certified divisibility theorem gives an integer `m` such that

    (-3)^t * 2^r - (2v-3) = D*m.

Natural absolute-value estimates, the proved exponential inequality `v^2≤2^v` for `v≥4`, and `v≥4*(3^c+1)` first imply `|m|≤3^c+1`. The bracket `(-3)^t - 2^(v+1-r)*m` is proven odd and nonzero; this forces `2^r ≤ 2v+3|m|`. A second bound gives `D*|m|<D`, hence `m=0`. Then parity forces `r=0`, and the same identity would imply `2v-3=3^t≤3^c`, contradicting `v≥4*(3^c+1)`.

`#print axioms terminal_superlinear_nat` and the source bridge provide exact certificate dependencies. The GitHub workflow compiles the untouched original DeepMind Cryptids source pinned at `ced8f9f44f67a167d5ecc03e687b048c67926371` before compiling the new modules.

## Scope and research significance

Agent20's prior mathematical hand proof already established the result conceptually. This Lean formalization provides a kernel-checkable, all-parameter foundation for future exact reverse-search algorithms using sublinear valuation candidate counts. It strengthens the verified four-linear bound asymptotically but still enumerates **synthetic, unrestricted** incoming edges. It supplies no genuine blank-root predecessor reachability or universal BB(6) upper bound. The immediate next direction is using this theorem inside a source-complete backward-reachability tree, rather than proving further synthetic fan-in facts.
