# Space Needle: exact equality classification at the terminal valuation wall

**Scope:** A Lean kernel-verified *all-natural* classification of the equality case of the known sharp terminal feeder inequality. The original-machine source bridge is written but awaits full unchanged-source CI. This result concerns **synthetic one-step predecessor edges**, not the blank-origin orbit.

## Main theorem

For natural `q,v,K`, let

```
D(v)=2^(v+1)+3,
B(v)=3*2^v+v+3,
equation(q,v,K) : D(v)*q+B(v)=2^K.
```

The [Lean theorem `terminal_threshold_iff`](BoundaryExact.lean) proves the exact equivalence

```
equation(q,v,K) and K=3v+3
    iff (q,v,K)=(45,2,9) or (214,3,12).
```

Thus both existing sharp equality witnesses are the **only** ones anywhere in the natural-number parameter space. In the exact accelerated Space Needle map, the corresponding sources `oddTower 45 2` and `oddTower 214 3` feed terminal inputs `2^9-2` and `2^12-2` respectively. No assertion that the actual blank orbit visits either source follows.

Agent 20's [source-verified sharp inequality](../agent20-needle-coprime/NeedleSharper.lean) had established the necessary condition `3v+3≤K` except the single exceptional `(q,v,K)=(61,6,13)`, and separately displayed the two equality witnesses. The present theorem closes the **equality boundary** exhaustively; it is stronger than simply giving examples, but does not tighten the off-boundary inequality or remove the known exception.

## Proof idea

Write `x=2^(v+1)`, so `D=x+3`, and substitute `K=3(v+1)). The terminal predecessor equation implies

```
2*x^3+54 = (x+3)*(2q+3)+(2v+51).
```

The polynomial identity

```
(x+3)*(2*x^2+18)=2*x^3+54+6*x*(x+3)
```

then yields the **divisibility obstruction**

```
2^(v+1)+3 divides 2v+51.
```

For all `v≥5`, a short induction proves `2^(v+1)+3>2v+51>0`, contradicting divisibility. Direct exhaustive arithmetic for `v=0,1,2,3,4` leaves exactly the two triples shown. The converse follows by exact substitution. This is an all-natural proof, with no valuation or exponent cutoff beyond the mathematically derived finite boundary.

## Reproducibility and limits

- [Standalone Lean arithmetic proof](BoundaryExact.lean) compiled under Lean 4.36.0-rc2, with `#print axioms terminal_threshold_iff` reporting only `[propext, Quot.sound]`. No `sorry` or custom axiom.
- [Original Cryptids source bridge](BoundaryExactSource.lean) composes the original `highLevelNext_iff_oddTower` and `oddTower_factor` theorems with the standalone equality classification. Locally typechecked against an exact-signature stub; **this is not authentic-source verification**.
- [Manual original-source workflow](../../.github/workflows/agent48-space-needle-five.yml) also compiles this proof bridge against the pinned source once dispatch succeeds. The dispatch tool was blocked in the current invocation.
- External novelty is unverified. This proof supplies a clean reusable boundary fact but leaves the full original blank-root terminal reachability problem and BB(6) unresolved.
