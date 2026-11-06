# Unbounded 2-adic valuations among legal Space Needle terminal parents

**Claim and scope.** For each natural `t`, the exact Space Needle arithmetic equation has an immediate parent of some terminal input `2^K−2` with valuation `v>t`. The parents are **synthetic valid source states**, and no claim about their reachability from the original blank tape is made. This is a constructive infinite family in a valuation dimension, complementary to fixed-valuation period families. Its external novelty relative to broader number-theoretic literature has not been reviewed.

## Closed formulas

Let `s=t+1` and define

```text
v = (9^s+3)/2,
X = 2^(v+1),
G_s(X) = sum_(j=0)^(s−1) X^(2(s−1−j))*9^j,
P = (X−3)*G_s(X),
q = (P−3)/2,
K = 2*s*(v+1)−1.
```

Here `G_s(X)` is an odd positive integer because `X` is even and its final summand is `9^(s−1)`. Hence `P` is odd, at least three, so `q` is natural. These values satisfy the exact source equation

```text
2^K = (2^(v+1)+3)*q + 3*2^v + v+3.
```

Thus `oddTower q v = 2^v(2q+3)−2` is a legal one-step predecessor of `2^K−2`. The first parameters are `(s,v,K,q)=(1,6,13,61)`; the next are `(2,42,171,340282366920822406584691642613415018481)`; and `(3,366,2201,q)` with a much larger exact integer `q`.

## Derivation

The elementary telescoping identity

```text
(X^2−9)*G_s(X) = X^(2s)−9^s
```

implies, since `P=(X−3)*G_s(X)=2q+3`,

```text
X^(2s) = (X+3)*(2q+3)+9^s.
```

Also `2v=9^s+3` and `X=2*2^v`, so the right side is exactly

```text
2*((X+3)*q + 3*2^v+v+3).
```

As `X^(2s)=2^(2s(v+1))=2^(K+1)`, cancellation of two establishes the source equation. Finally the elementary inequality `2s≤9^s` gives `v>t`. Every step is valid for all natural `t`, with `s≥1` ensuring positivity.

## Formal proof and trust boundary

[NeedleVariableValuation.lean](NeedleVariableValuation.lean) proves the geometric factor recurrence, parity, positivity, the exact source equation, and `v>t` in Lean 4.36.0-rc2. Its `terminal_variable_valuation` and `valuation_unbounded` theorems compiled locally with `#print axioms` equal to `[propext, Quot.sound]`, no `sorry` or placeholder imports. The locally checked source SHA-256 was `2a98bb503a852b21985721c74e18f50032a5a5ee229e11926c8731d388d71ad9`. The complete source is checked into the repository.

[NeedleVariableValuationSource.lean](NeedleVariableValuationSource.lean) composes this arithmetic theorem with the already source-certified `authentic_affine_successor` to obtain the claimed exact original `highLevelNext` witness for every `t`. Its unmodified original-Cryptids source check is queued in the manually invoked [agent20-needle-triple.yml](../../.github/workflows/agent20-needle-triple.yml); update this verification status only after checking the run's final result and axiom audit.

The family's first `v=6,K=13` is the already known unique exception to the sharp `3v+3≤K` bound. For all later `s`, the construction is consistent with that bound. The conclusion is **not** a genuine blank-reached halting feeder and gives no BB(6) bound. To make root progress, investigate whether any of these specific large valuations can arise along the actual high-level orbit from `N1`, or derive a root-specific obstruction affecting all terminal exponent families.
