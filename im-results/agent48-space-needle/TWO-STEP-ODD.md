# Exact two-step odd-terminal inverse grammar for Space Needle

**Agent 48, 2026-11-04. Scope: original pinned high-level Space Needle source, all natural parameters. Verified as an intermediate technique; no resolved blank-root halt or BB(6) bound.**

## Exact theorem

The pinned original Google DeepMind Cryptids six-state Space Needle machine is
`1RB1LA_1LC0RE_1LF1LD_0RB0LA_1RC1RE_---0LD`. The high-level blank start is `N 1`, and `highLevelNext` is source-defined. Put

```
source d = oddTower q v
d+2 = 2^v*(2q+3)
Y(q,v) = (2^(v+1)+3)*q + 3*2^v + v+3.
M(v) = 5*(2^(v+1)+3)
B(v) = 15*2^v+5*v+12.
```

For all `q,v,K:Nat` with `K>0`, the following are **equivalent**:

1. A first successful original high-level transition from `N (oddTower q v)` reaches an **odd** counter `e`, and its very next high-level transition reaches the **terminal counter** `2^K-2`.
2. `2^(K+1) = M(v)*q+B(v)`.

This is [`NeedleTwoStepOddSource.original_two_step_odd_iff`](NeedleTwoStepOddSource.lean), proved directly using the original source's `scan_oddTower`, the source-connected [odd branch theorem](SpaceNeedleOddBlocksSource.lean), and the independent all-natural affine [arithmetic equivalence](NeedleTwoStepOdd.lean). The next high-level call *from* `2^K-2` is the terminal halt. Each fixed `(K,v)` permits at most one `q`; all such pairs satisfy `v<K`. Therefore this conditional two-step branch has a finite, exact valuation enumeration for every fixed K.

The intermediate counter obeys `e+2=Y(q,v)=2a+1`; the odd step sends `e=2a-1` to `5a-1`. Substitution gives `2^(K+1)+3=5Y(q,v)` and then the displayed affine equation. The Lean theorem establishes both directions, including natural-number underflow boundary handling and `K>0`.

Small reproducible examples of legal **synthetic** two-step paths:
- `K=20,v=0` (the familiar two-odd-block case).
- `K=24,v=3`.
- `K=88,v=6`.
Other K may have *direct* nonodd terminal predecessors and the absence of an odd-intermediate predecessor never proves terminal unreachability from the blank tape.

## Verification and novelty boundaries

The all-natural arithmetic proof and complete conditional original transition theorem compiled locally under Lean **4.36.0-rc2** with `#print axioms` limited to standard `propext`, `Classical.choice`, and `Quot.sound`; no `sorryAx`. The original-source-checked manual GitHub Actions [run 41931806607](https://github.com/FlareZ123/bb6/actions/runs/41931806607) **succeeded** on 2026-11-04 23:14 UTC, building unmodified `google-deepmind/cryptids@ced8f9f44f67a167d5ecc03e687b048c67926371` under the original Lean 4.35.0-rc4 toolchain and compiling the new original-source theorem after [`SpaceNeedleClosed.lean`](SpaceNeedleClosed.lean). Final source prints only standard Lean axioms.

**Relation to previous work:** Agent20's [complete one-step original inverse](../agent20-needle-coprime/NeedleGeneralInverseSource.lean) could be composed twice to classify all two-step histories. This new iff algebraically eliminates the odd intermediate and yields one affine congruence per source valuation. It has a narrower conditional scope, so we make no independent external novelty claim and place it in `im-results/`.

The actual blank-start orbit must be shown to reach one of these possible source states, or to avoid **every** terminal feeder including nonodd alternatives. No such reachability result follows here. The immediate next test is to combine exact inverse enumeration with a genuine all-time forward blank-orbit invariant rather than counting additional synthetic residue families. All six-state Busy Beaver classifications and exact BB(6) remain open.
