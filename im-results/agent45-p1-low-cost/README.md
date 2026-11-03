# Agent 45: low-inverse-cost arithmetic rigidity of the P1 two-feeder obstruction

**Research status:** independent reproduction of an already existing stronger result, **not new mathematical progress**. Agent9's source-certified [DichotomyOriginal.lean](../agent9-p1-logcost/DichotomyOriginal.lean), [CI 41554472589](https://github.com/FlareZ123/bb6/actions/runs/41554472589), proves the same exact affine wall with a **stronger 8P** low-cost threshold; the file here only proves a weaker 7P implication. Locally kernel-checked with Lean 4.36.0-rc2 on 2026-11-03; **original-source bridge also certified** by manual CI [41556866983](https://github.com/FlareZ123/bb6/actions/runs/41556866983), commit `c337df4f91a9adc86cbca34ffec8133d9004ffa7`. The redundant specialization remains non-novel. No P1 halting decision, BB(6) bound or external novelty claim. Issue: [R002](../../research/issues/R002.md). Evidence and hypotheses must not be confused with blank reachability.

## The new checked statement

See [LowCostPower.lean](LowCostPower.lean), theorem
`BB6.Agent45LowCost.low_cost_power_leaf_shape`. Let `q>=1`,
`P=2^(16q)`, and `e in {3,5}`. Suppose an arbitrary odd-cone hub
`(b,d)` with cumulative inverse mass cost `m` and even-right predecessor
`(2k-4,c+4)` satisfies all of:

```text
b+d+2m+32q+24 = 56P+e
b>=8, b mod 4=0, d mod 2=1, c mod 2=0
d+b/2+3 = 2^t*(c+3)
t<=16q+4
2k+c+2t+1=b+d
2k+8=14*2^j
m<=7P.
```

Then **necessarily**

```text
j=16q+1, t=1, and
e=5 => b=4m+64q+12,
e=3 => b=4m+64q+16.
```

All statements are over natural numbers, with natural division. The polynomial power-leaf conditions and mass identities match the upstream exact `OddCone`, `inverseAt_iff_power_mass`, source `inverse_depth_le` and `even_left_power_shape` lemmas, but **this standalone file assumes them explicitly**. That avoids overstating the original-source integration.

**Reproduction:** reconstruct Lean 4.36.0-rc2 from the supplied archive, run `lean LowCostPower.lean` from this directory (with `Std` on its library path). Local check succeeded. The final `#print axioms` reported exactly `[propext, Quot.sound]`, and no `sorryAx`. The checked local file had SHA-256 `01a0e37ce9471a505d0f03b1ba96cd088d4bb2bba832d32ef606032c18b7dd03`.

## Genuine-source verification

[`LowCostSource.lean`](LowCostSource.lean) derives `BB6.Agent45LowCost.source_low_cost_even_target` for every authentic `OddCone`, every exact original `inverseAt` to an even-right source, and any originally blank-reachable even terminal input, under the extra `m<=7P` hypothesis. It is source-compilable against **unmodified** Agent1/47/45/50 modules. In successful existing manual CI 41556866983 (job `125657780653`), `#print axioms` was `[propext, Classical.choice, Quot.sound]` (no `sorryAx`). The earlier Agent9 theorem is stronger (`m<8P`) and was built in the same run.

## Significance and restrictions

The two genuine n=16q+2 feeder hubs established in Agent45's [earlier original-source iff](../agent45-p1-deep-two/README.md) have initial mass `8u+5` and `8u+3`, respectively, where `u=7P-4q-3`. Agent1's [inverse characterization](../agent1-p1-quarter/InverseIff.lean) and [all-depth small-left theorem](../agent1-p1-quarter/UniversalSmallLeft.lean) provide the displayed premises along any qualifying even-right inverse leaf. Agent9's earlier theorem has already established a *strictly stronger* source-connected version. This standalone proof adds no known exclusion or novel method. The theorem therefore reduces all **low-cost** potential power-compatible leaves to one specific exponent, one depth, and one affine target line per root:

- L0/e=5: `b-4m=64q+12`.
- L1/e=3: `b-4m=64q+16`.

The bound `m<=7P` is large compared with all sampled cone costs, but there is **no universal source theorem** that every inverse cone stays under it. Nothing yet excludes an odd cone from meeting the affine line at small cost, and large-cost branches remain open. The stand-alone arithmetic result is a reduced obligation, not a negative reachability theorem.

## Finite exact experiments

`probe.py` implements the known exact `inverseAt` integer recurrence on both roots, distinguished by `e`. It checks exceptional small predecessors, power-of-two `c=1` tests, the stronger leaf gap `28P < x+12 < 56P`, and the new low-cost affine target. It is a bounded, trusted-code experiment without a Lean source-connected graph-exhaustiveness proof.

With a per-q limit of 500,000 distinct odd hubs:

| q | Exhausted odd hubs | Even-right leaves | Max cumulative m | Max inverse depth | Exceptions |
|---:|---:|---:|---:|---:|---|
| 1 | 50 | 24 | 10 | 5 | 0 |
| 38 | 13,438 | 6,817 | 249 | 10 | 0 |
| 101 | 59,738 | 29,828 | 769 | 12 | 0 |
| 294 | 321,678 | 160,863 | 2,515 | 13 | 0 |

The q=38,101,294 cases had been among the 13 **capped** at 10,000 hubs in Agent1's earlier [band experiment](../agent1-p1-quarter/BAND-HEURISTIC.md); these larger finite computations close their scanned trees. Each remains a fixed-index finite computation, not a statement covering arbitrary q.

## Next decisive tasks

1. **Completed:** built and source-checked `LowCostSource.lean`; independent repeat confirms consistency with Agent9's stronger original-source proof. No further effort on reproducing the same dichotomy is warranted.
2. Prove or falsify an **all-q** barrier excluding the two small-cost affine odd-cone lines, while explicitly accounting for arbitrarily deep synthetic inverse paths. This is a weaker necessary goal than claiming every odd hub has exponential first counter.
3. Establish a uniform inverse-cost limit `m<=7P` or handle the high-cost remainder without presuming finite sample closure. Test any proposal against q=294's 321,678-node cone and the existing Agent45/27 deep synthetic witnesses.

External novelty has not been assessed. Do not promote this directory into `results/` without independent source/relevance/prior-art review.
