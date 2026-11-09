# Space Needle: five source-genuine cancellation predecessors and a uniform valuation sieve

**Agent 47, 9 November 2026.** The new all-index arithmetic, five distinct incoming high-level edges, and uniform valuation exclusions have passed the **complete pinned original Cryptids source Lean check** in [manual run 42722455551](https://github.com/FlareZ123/bb6/actions/runs/42722455551). These are intermediate mathematical results about *arbitrary-source predecessors*. The existence or nonexistence of an authentic blank-start route into any target in this family remains open. No BB(6) machine decision or global bound is claimed.

## Original transition and cancellation family

In the pinned original six-state Space Needle high-level source, a nonterminal counter of the form

`oddTower(q,w)+2=2^w(2q+3)`

has a successor whose shifted counter is

`(2^(w+1)+3)q + (3*2^w+w+3)`.

Thus an incoming edge at valuation `w` to shifted target `B` is characterized by

`B=D_w*q+C_w`, where `D_w=2^(w+1)+3`, `C_w=3*2^w+w+3`, and `q>=0`.

Use Agent 20's existing all-positive-index cancellation terminal-feeder construction:

- `v_r=(9^r+3)/2`, `A_r=2^(v_r+1)`;
- `P_r(A)=(A-3)*sum_(i=0)^(r-1) A^(2(r-1-i))*9^i`;
- `B_r=2^v_r*P_r(A_r)`.

The original-source `sourceB_is_original_feeder` theorem identifies `B_r-2` with the genuine **prepared-input terminal feeder** `oddTower(feederQ r,feederV r)`. Prepared-input status alone does not imply membership in the true blank-start orbit.

## Five distinct incoming predecessors: infinite progression

For every `t>=0`, let

`r_t = 4152608179 + 35697042810*t`.

The theorem [`infinite_five_predecessors`](CancellationElevenSource.lean) constructs five pairwise different source counters `oddTower(q_w,w)`, one at each

`w in {3,4,5,6,11}`,

with **exactly the same original `highLevelNext` target**, the cancellation feeder at index `r_t`. Pairwise distinction follows directly from the odd factor in `oddTower(q,w)+2=2^w(2q+3)`; it is proved in Lean as ten explicit inequalities.

This extends Agent 46's original-source [three-predecessor construction](../agent46-needle-three/README.md), previously valid on `r=214+495t`, and Agent 47's original-source [valuation-four iff](NeedleCancellationFour.lean) for `r%3=1`.

The two new valuation arms are mathematically explicit:

1. **Valuation 6.** For `r=64069+1685970t`, [`CancellationSix.sourceB_mod131`](CancellationSixArithmetic.lean) proves `B_r%131=70`. Since `D_6=131`, `C_6=201` and `B_r>=8000`, this yields `q_6=(B_r-201)/131`. This progression is a subfamily of the original valuation-3/4/5 family: `r=214+495(129+3406t)`. [`CancellationSixSource.lean`](CancellationSixSource.lean) constructs all four distinct original-source edges.

2. **Valuation 11.** The finer progression above satisfies `r_t=64069+1685970(2463+21173t)`. [`CancellationEleven.sourceB_mod4099`](CancellationElevenArithmetic.lean) proves `B_(r_t)%4099=2059`, exactly `C_11%4099`, where `D_11=4099` and `C_11=6158`. Therefore `q_11=(B_(r_t)-6158)/4099` is an integer. The original-source [`CancellationElevenSource.lean`](CancellationElevenSource.lean) constructs the fifth edge and proves its distinctness from the prior four.

The valuation-eleven proof uses genuinely unbounded modular exponent arguments, rather than a table of sample indices. Its input index obeys `r%31=17` and `r%2049=280`. These imply `9^r%8196=4125`, `v_r%4098=2064`, `A_r%4099=48`, `(A_r^2)^r%4099=2719`, and `9^r%4099=2955`. The elementary exact identity

`(a-9)*geo(a,9,r)+9^r=a^r`

then determines `geo(A_r^2,9,r)%4099=909`, yielding `B_r%4099=2059`. The proof uses efficient `Nat.powMod` certificates for fixed large exponents and ordinary kernel checking.

## Uniform no-parent valuation sieve

A separate, independent result excludes entire **valuation positions**, uniformly over *every* positive cancellation index `r`, regardless of whether the target is reachable from blank:

- [`no_cancellation_parent_mod5`](CancellationSieveSource.lean): no incoming valuation `w` with `w%20 in {0,8,12,16}`.
- [`no_cancellation_parent_mod7`](CancellationSieveSource.lean): no incoming valuation `w` with `w%21 in {1,7,10,16}`.

The first follows from the already-proved `B_r%5=0`: if `w%4=0`, then `5|D_w` and `C_w%5=(w+1)%5`; equality requires `w%5=4`. The second uses the exact established cancellation residue cycle `B_r%7 in {0,1,6}`: for `w%3=1`, `7|D_w`, and `C_w%7=(w+2)%7`. Hence `w%7` must be 4, 5, or 6.

Over the common period `lcm(20,21)=420`, the forbidden sets contain 84 and 80 residue classes, with 16 in their intersection. The union has exactly **148/420 = 37/105** of all valuation residue classes. This is a mathematical density of forbidden *candidate indices* in the inverse grammar, not a proportion of actual orbit events or reachable states.

The arithmetic proofs are in [`CancellationValuationSieve.lean`](CancellationValuationSieve.lean), and the source-connected bridge is in [`CancellationSieveSource.lean`](CancellationSieveSource.lean).

## Proof verification and scope

The reused manual [original-source CI workflow](../../.github/workflows/agent46-needle-three.yml) compiled the **unchanged pinned original Cryptids Space Needle high-level module** plus the checked-in Agent 20, Agent 46, and Agent 47 dependencies. [Run 42722455551](https://github.com/FlareZ123/bb6/actions/runs/42722455551) **passed**, including the fifth-parent source proof and valuation-sieve source proofs. The final axiom audits show only ordinary Lean logical axioms, without `sorryAx`; the standalone large-power arithmetic theorem has just `propext` and `Quot.sound`.

The original raw-machine-to-high-level semantics were established by the existing Space Needle raw bridge in [Agent 48's dossier](../agent48-space-needle/README.md). This investigation uses that unchanged high-level transition semantics. It proves multiple *legally incoming* edges, and gives no argument that any of their sources is reached along the single genuine blank-start orbit.

The root-level decisive obligation remains: decide whether `ReachN` ever contains a terminal feeder. A complete backward-root closure, a true blank-root terminal witness, or a global nonhalting invariant would advance the BB(6) decision. The inverse-fan-in examples show why treating a cancellation feeder as possessing one or a bounded-by-four immediate synthetic predecessor is unsound.
