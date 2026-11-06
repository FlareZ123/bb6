# Space Needle: an infinite five-source terminal predecessor family

**Mathematical scope:** Original-machine high-level transition arithmetic, with a kernel-checked proof of five distinct *synthetic* one-step predecessors for every terminal destination in an infinite arithmetic progression. This **does not** prove any of the predecessors lies on the actual blank-tape orbit, nor that the machine halts, nor a BB(6) bound.

## Machine and exact inverse equation

For the DeepMind Cryptids Space Needle machine
`1RB1LA_1LC0RE_1LF1LD_0RB0LA_1RC1RE_---0LD`, pinned at
`google-deepmind/cryptids@ced8f9f44f67a167d5ecc03e687b048c67926371`, the source-checked accelerated map has states `N d` and exact source representation

```
d + 2 = 2^v (2q+3),  q,v natural.
```

Its one-step successor is `N(2^K-2)`, a halting-input counter at the *next* high-level evaluation, precisely if

```
2^K = D(v)*q + B(v),
D(v) = 2^(v+1)+3,
B(v) = 3*2^v + v+3.
```

The source equations follow directly from [Agent 48's exact source high-level theorem](SpaceNeedleClosed.lean) and [Agent 20's complete general inverse](../agent20-needle-coprime/NeedleGeneralInverse.lean), with bridge [NeedleTerminalAffineSource.lean](../agent20-needle-coprime/NeedleTerminalAffineSource.lean).

## A certified infinite construction

Let
```
K(t) = 115559872543250362436240044170777864346536
     + 136996046966732361806630100489564981018852 * t
```
for `t ≥ 0`. For *every* `t`, `N(2^K(t)-2)` has at least **five distinct one-step predecessors**, whose shifted counters have exact 2-adic valuations **0, 3, 20, 38, 83**. The table gives denominator `D(v)`, bias `B(v)`, and the required `2^K mod D(v)`.

| v | D(v) | B(v) | required residue |
|---:|---:|---:|---:|
| 0 | 5 | 6 | 1 |
| 3 | 19 | 30 | 11 |
| 20 | 2097155 | 3145751 | 1048596 |
| 38 | 549755813891 | 824633720873 | 274877906982 |
| 83 | 19342813113834066795298819 | 29014219670751100192948310 | 9671406556917033397649491 |

The [Lean source](FiveTerminal.lean) kernel-checks both congruences for the base exponent `K(0)` and periodicity under its common period. Its `five_moduli` theorem inducts over all `t` using the product formula for powers; `five_equations` then supplies five *nonnegative* integer quotients, without computing astronomical natural powers at each `t`. The sources are distinct because `v₂(d+2)` is precisely the listed `v`. This gives an all-natural theorem rather than finite computational sampling.

**Reproducibility and current trust boundary:** `FiveTerminal.lean` compiled locally under Lean **4.36.0-rc2**, no `sorry` or new axioms; `#print axioms` gave the standard `propext`, `Quot.sound` and, for source distinctness, `Classical.choice` only. [FiveTerminalSource.lean](FiveTerminalSource.lean) was locally compiled against a type-matched *test interface stub* for the original source, so its local result does **not** yet authenticate the upstream connection. The repository's [manual-only original-source workflow](../../.github/workflows/agent48-space-needle-five.yml) is prepared for pinned-source compilation. Its dispatch was blocked by available tool safety checks during this invocation; **no successful original-source CI is claimed here**.

Prior work by Agent 20 constructed a source-certified three-predecessor progression using `v=0,3,20` in [NeedleThreeTerminalSource.lean](../agent20-needle-coprime/NeedleThreeTerminalSource.lean), CI [42107688083](https://github.com/FlareZ123/bb6/actions/runs/42107688083). Agent 20 also supplied a paper proof of unbounded indegree for arbitrary **nonterminal** synthetic destinations ([UnboundedFanin.md](../agent20-needle-coprime/UnboundedFanin.md)). The present five-source construction extends a *terminal power-of-two* family. Its external originality and relevance to the rooted decision remain undetermined.

## Decisive unresolved condition

This construction exhibits infinitely many *legal incoming high-level edges*, but is neutral about their membership in the deterministic orbit from original blank state `N 1`. Any attempt to prove or refute Space Needle halting must establish that orbit's actual reachability or avoidance of the terminal predecessor set. A source-only indegree result never resolves the blank-start existential; the machine's halt/nonhalt status and the exact BB(6) maximum remain open.
