# A 228-digit exact first-query certificate for a six-state Turing machine

**Status, 28 November 2026:** Original-source Lean proof of the exact
first undefined transition and its universally weighted all-completion Cover
**accepted** by [CI run 46149478884](https://github.com/FlareZ123/bb6/actions/runs/46149478884).
This is a theorem about one specified one-hole six-state cylinder, **not**
a proof of BB(6) or the entire Raw139 parent.

## The exact result

Consider the six-state, two-symbol, blank-tape machine with one undefined
transition, encoded using the repository's original 24-ordinary-move plus
halting convention as

```text
[7,20,11,1,14,11,22,16,24,13,2,12]
1RB0LF_1RC0RA_1LD1RC_1LF0LE_---0RD_1LA0LD
```

The sole undefined entry is **(state E, scanned symbol 0)**, i.e.
`(4,false)`. Let `p` be this partial machine, and let `m` be an arbitrary
six-state completion of `p`. Write `run m n blank` for exactly `n`
successful primitive transitions, with the first subsequent undefined
query representing a halt. Define the following **228-digit** natural
number `N`:

```text
808309055302710301732399105636921133919495108874980019743107699471600464749233442847378894817095810992429166948707568686931771651390236209884096433253525595914426390935828906878170789519869183115472163083845213146412559801558627
```

The formalized first-query theorem gives:

1. For **every** compatible completion `m`,
   `run m N blank = some c` for some `c` with
   `readSlot c = (4,false)`. Thus no completion executes an undefined
   transition during its first `N` successful moves.
2. If the E0 transition of `m` is undefined, then
   `HaltsAfter m N`: exactly `N` successful moves and the
   `(N+1)`-st halting query.
3. If the E0 transition is ordinary, `m` is everywhere defined
   (the other eleven transitions were already ordinary) and
   `NeverHalts m`.
4. Consequently `Cover (WeightedBound (N+6)) p`, accounting for
   the standard up-to-five first-one blank-delay overhead.

Items 1–4 are proved against the *original physical-head* semantics, not
only against a detached arithmetic recurrence. The original-source Lean
gate is [run 46149478884](https://github.com/FlareZ123/bb6/actions/runs/46149478884)
at source commit `a2f5b84c0999985856f83711f4ad316d58d2c51a`,
including the complete upstream source closure and printed-axiom audit.
The key exports are
`BB6.Agent3Leaf2265Bridge.reached` and
`BB6.Agent3Leaf2265Bridge.weighted`.

The explicit completion `closingMachine s := (p s).getD none` realizes
the finite halting score `N+1`. The generic construction and exact
attainment lemma `attainable_of_source` separately passed original-source
Lean CI [46150512653](https://github.com/FlareZ123/bb6/actions/runs/46150512653).
The specialized instance `BB6.Agent3Leaf2265Bridge.exact_attainable` is
also **source accepted** in [CI 46150812333](https://github.com/FlareZ123/bb6/actions/runs/46150812333),
with standard Lean axioms: the concrete six-state machine really attains
exact primitive halt-query score `N+1`.

## Source proof mechanism

Define `P=01` and `G=1100` on the tape's right-infinite ray, with
`S(k,w)` a blank-left head at state A with right ray `P^k w`.
The original blank run reaches `S(3,blank)` after **13** primitive moves.
Source-proved parameter-uniform sweep and return lemmas give counted
transitions `S(k,w) → S(k',w')` across the five nonterminal suffix classes.
The terminal suffix class reaches state E scanning zero with a separately
counted terminal cost.

Starting from `S(3,blank)`, the explicit integer recurrence has **435**
successive normalized return sections, followed by its terminal section.
The 435 chosen instances are *not axioms*: the generated Lean proof gives
each exact input configuration, output configuration and move count, then
chains 44 grouped chunk theorems into the giant `N`-step `terminalRun`.
Eleven independent trace modules (`Leaf2265TracePart00.lean` through
`Leaf2265TracePart10.lean`) keep elaboration finite, and bounded-size
rewrites deliberately avoid expansion of astronomical repeated tape blocks.

`Leaf2265BridgeCore.lean` establishes the all-parameter observational
bisimulation between these two-ray source transitions and the repo's
original `Config`, `rawStep`, and `run`. Its independent
[CI run 46147749118](https://github.com/FlareZ123/bb6/actions/runs/46147749118)
source-accepted `reached_of_source` and `weighted_of_source`.
A second reusable transport
`OneHoleFirstQuery.cover_of_uniform_first_query` source-accepted
[run 46148561454](https://github.com/FlareZ123/bb6/actions/runs/46148561454).
Thus the theorem is not extrapolated from a finite simulation or based
on an untrusted program's declaration of the runtime.

## Relation to the attained champion and remaining parent

A separate source-certified arithmetic inequality
`BB6.Agent3ChampionPow1024.champion_score_ge_pow_of_le` states

```text
∀ e ≤ 2^63 − 1,  2^e ≤ proposedTM63Moves + 7.
```

It passed original-source [CI 46150315226](https://github.com/FlareZ123/bb6/actions/runs/46150315226).
The proof uses the **second** counted increment
`proposedIncrementCost 1 6 71 (2^63−1)` and an all-parameter
first-section containment lemma. It avoids evaluating
`4^(2^63−1)`; the source expression's separate *attainment* is
established by the champion project. Since the literal `N+6 ≤ 2^1024`, the entire one-hole cylinder
is **source-certified at the attained champion score** by
`BB6.Agent3Leaf2265ChampionCompare.one_hole_cover_at_champion`,
[CI 46151036404](https://github.com/FlareZ123/bb6/actions/runs/46151036404).
The mixed finite/astronomical transport to `2^32768` is separately
**source accepted** in [CI 46151039892](https://github.com/FlareZ123/bb6/actions/runs/46151039892),
under the reusable `TwoBoundAudit` checker.

The original parent `Raw139 E1=0RD/D0=1LF` has **4,875** open
cutoff-100 children: **4,873** ordinary resolved recipes and the two
exceptional one-hole children **2265** (this result) and **3506**
(F067, separate ongoing proof program). The parent query tree, F067
certificate, and a common source-checked final Cover are still required
before any global canonical-roster hypothesis can be discharged.
Nothing here establishes a universal six-state upper bound or an exact
Busy Beaver value.

## Reproducibility and source map

- [First-query mathematical derivation](../im-results/agent3-raw139-e1-zeroRD/Leaf2265.md).
- [Original machine and sweep lemmas](../im-results/agent3-raw139-e1-zeroRD/Leaf2265Core.lean), [compressed macro rules](../im-results/agent3-raw139-e1-zeroRD/Leaf2265MacroAll.lean).
- [Exact source trace and terminal count](../im-results/agent3-raw139-e1-zeroRD/Leaf2265Trace.lean), [deterministic generator](../im-results/agent3-raw139-e1-zeroRD/emit-leaf2265-trace.cjs).
- [Original raw semantics bridge](../im-results/agent3-raw139-e1-zeroRD/Leaf2265BridgeCore.lean), [concrete bounded cylinder](../im-results/agent3-raw139-e1-zeroRD/Leaf2265Bridge.lean).
- [Symbolic attained-champion threshold](../im-results/agent3-raw139-e1-zeroRD/ChampionPow1024.lean), [direct threshold consumer](../im-results/agent3-raw139-e1-zeroRD/Leaf2265ChampionCompare.lean).
- [Hybrid finite/astronomical audit construction](../im-results/agent3-raw139-e1-zeroRD/TwoBoundAudit.lean) and [saved parent census](../im-results/agent3-raw139-e1-zeroRD/census-d0lf1.json).

Every concrete theorem stated above has now passed its cited complete
original-source Lean closure and axiom audit. The still-open obligations are
the 3506 F067 source proof and the finite whole-parent query-tree Cover;
no conclusion about BB(6) maximality follows from one child.
