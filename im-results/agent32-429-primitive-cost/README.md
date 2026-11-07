# Machine #429: exact unbounded primitive-step sweep certificates

**Original-source verified (7 November 2026).** For the literal six-state, two-symbol machine
`1RB0LF_1RC1RA_0RD0RB_1LE---_0LA1LE_1RD1LA`, this dossier proves an exact
*quadratic primitive-time prefix* from every suitable symbolic `J(u,w)` configuration
and an exact subsequent first arrival at F/0, using the unmodified raw two-way
infinite-tape semantics. The parameter `u` is unrestricted. This is a partial
analysis of **synthetic source-encoded sections**; it does not show which parameters
the genuine blank orbit visits and it does not decide #429 or BB(6).

The first source CI containing all four proofs passed in [manual run 42336598122](https://github.com/FlareZ123/bb6/actions/runs/42336598122), Lean 4.36.0-rc2 at commit `710efed0665a34e1af13d3826261700b11387a12`.
A prior source compilation of `BubbleExact` passed [42336013018](https://github.com/FlareZ123/bb6/actions/runs/42336013018).
Both use the actual Agent8 `Frontier` and Agent1 exact #429 source table, no `sorryAx`;
the `#print axioms` reports standard Lean axioms only.

## Proven all-natural statements

The [generic bubble theorem](BubbleExact.lean), `BB6Bubble.bubble_exact`, requires
four rules in *any* `BB6Coverage.Machine`:
`A/1=0LF`, `F/1=1LA`, `A/0=1RB`, `B/1=1RA`.
With state A and head `h`, an isolated zero at `l=h−2q`, and ones in every
cell between `l` and `h+1`, it executes **exactly `4q+2` successful raw
transitions**, returning to A at `h+2` with exactly the single zero at `l`
changed to one; all other tape bits are unchanged. This includes arbitrary
natural `q=0`. Its proof composes an exact leftward erase
`AF_sweep`, an exact rightward repaint `AB_sweep`, and extensional
infinite-tape equality `paint_merge`, without sampling a finite bound.

[BubblePrefix.lean](BubblePrefix.lean) iterates that lemma through `j≤u`
isolated negative-even holes in any appropriately prepared physical tape:
`multi_bubble_prefix` concludes that after **exactly `4j²+2j` raw
transitions**, the head is at `2j` in state A and the only tape changes
are filling the holes at `−2,−4,...,−2j`. The resulting tape function is
defined by `negFill` and is extensionally specified for every integer cell.

The external original Cryptids J-section is

```text
J(u,w) = 0^infinity 1^5 (10)^u 1 A> 1^(w+2) 01 0^infinity
```

where the head is state A at coordinate zero. [JPhysicalPrefix.lean](JPhysicalPrefix.lean)
defines its exact `jTape u w : Int → Bool` and checks the four original
machine rules by kernel reduction. The theorem `j_prefix_exact` proves,
for **all** `u,w : Nat` satisfying `2u≤w+1`, that the genuine raw
execution of this symbolic configuration has the `multi_bubble_prefix`
endpoint at time `4u²+2u`, including the complete resulting tape.

[JF0Prefix.lean](JF0Prefix.lean) extends the symbolic execution with an
exact `AF_sweep` of `4u+6` moves and then the actual A/1 transition.
`j_F0_prefix` proves that after **exactly `4u²+6u+7` successful raw
transitions**, this same symbolic input reaches F with head
`−2u−7`, scanning the original blank symbol `0`. Its proof checks
the entire intervening tape, not only the state name. The initial
`J` is *synthetic*: original Cryptids separately proves that the
authentic blank orbit enters `J(0,0)` after 35 steps and returns to J charts,
but this dossier has not yet transported these time formulas through
that source correspondence. The displayed parameter condition is exactly
the domain certified by these lemmas.

## Proved high-3 J return and arbitrary high-3 ladders

The separate [Agent1 J-first-branch dossier](../agent1-429-j-first-branch/README.md)
now proves the complete raw continuation branch for every (u,w) with
(w\ge 2u+3): exactly (4u^2+10u+27) successful transitions return to
the translated J chart ((2u+3,w-2u-3)), with full infinite-tape equality.
It also proves the fatal boundary (w+1=2u).

Building on that one-branch theorem,
[High3Ladder.lean](../agent32-429-high3-ladder/High3Ladder.lean) proves
arbitrary consecutive high-3 segments directly for the raw machine. If
`branchShift u k ≤ w`, then exactly `branchCostSum u k` primitive
transitions reach the translated J chart with
[
u_k=2^k(u+3)-3,\qquad
w_k=w-\operatorname{branchShift}(u,k),
]
and
[
\operatorname{branchShift}(u,k)+3k=2(u+3)(2^k-1).
]
The exact primitive cost is the recursive sum of the one-branch costs
(4u_i^2+10u_i+27). CI run
[42399391414](https://github.com/FlareZ123/bb6/actions/runs/42399391414)
compiled this module and passed the `sorryAx` rejection gate.

These are exact conditional J-chart results. The raw tape encoding still
needs its separate accepted bridge to the pinned Cryptids `highLevelEncode`
and authentic blank-root representation; see
[Agent1's source bridge](../agent1-429-j-first-branch/JSourceBridge.lean).

## Further computational evidence, not yet proved

The high-3 continuation branch and fatal boundary have since been proved for all parameters, so they are excluded from the remaining conjecture table below. The table retains the other ten branch families, which remain computational evidence only. An independent raw-tape CommonJS simulator checked 4,280 synthetic
`J(u,w)` cases (40×82 grid and 1,000 seeded samples, up to 146,327
raw moves) against the twelve-case original high-level return map.
It found a polynomial exact primitive return-time formula for every
case, summarized below. These formulas are **finite computational
conjectures** outside the tested inputs. A predicted target J is a
symbolic source checkpoint, not a claim that the authentic blank orbit
ever visits that arbitrary source section.

| Original map branch | Conjectured successful raw steps to next J, or final D/1 halt input |
| --- | --- |
| `w≥2u+3` | `4u²+10u+27` |
| `w=2u+2` | `4u²+44u+204` |
| `w=2u+1` | `4u²+28u+306` |
| `w=2u` | `4u²+28u+110` |
| `w<2u` even, `d=u−w/2=1` | `4u²+14u+61` |
| even, `d≥2` even | `(18u+2w²+13w+522)/2` |
| even, `d≥3` odd | `(18u+2w²+13w+140)/2` |
| odd, `d=1`: fatal | `4u²+10u+26` successful moves followed by one halting query |
| odd, `d=2` | `4u²+6u+26` |
| `w=1`, `d≥4` even | `28u+451` |
| odd `w≥3`, `d≥4` even | `(38u+2w²−w+271)/2` |
| odd, `d≥3` odd | `(22u+2w²+7w+125)/2` |

The first formal prefix `4u²+2u` and F/0 checkpoint
`4u²+6u+7` are already **mathematical theorems for all
valid parameters**, not extrapolations. Neither implies a full map
duration. For instance, the conjectured fatal duration requires a
further `4u+19` raw transitions beyond F/0.

## Open proof obligations and scientific scope

1. The generic `(C/1,B/0)` rightward sweep and its fatal/continuation
   boundary costs are formally proved in [CBPrimitiveSweep.lean](CBPrimitiveSweep.lean).
   The F/0-to-C setup, `10`-pair pattern, full high-3 output tape, and fatal
   boundary are now composed in [Agent1's J-first-branch proof](../agent1-429-j-first-branch/README.md).
   The remaining raw J-chart cases are `w=2u`, `w=2u+1`, `w=2u+2`, and
   the `w<2u` families. The original-Cryptids representation bridge is a
   separate, not-yet-accepted proof obligation.
2. Complete and CI-accept the raw-to-Cryptids bridge in
   [JSourceBridge.lean](../agent1-429-j-first-branch/JSourceBridge.lean),
   then translate all completed raw segments into the pinned Cryptids
   acceleration semantics, checking final score conventions.
3. For a genuine holdout decision, **resolve the unbounded blank-origin
   recurrence**, i.e. whether the real J-parameter orbit ever reaches
   the fatal `w=2u−1` input. A fast time formula for an arbitrary
   synthetic fatal J does not settle its authentic reachability.

The [source pinned Cryptids #429 file](https://github.com/google-deepmind/cryptids/blob/c86f15861709b76042998c5211c7b2f83991621b/BusyBeaver/BB6/M_1RB0LF_1RC1RA_0RD0RB_1LEHHH_0LA1LE_1RD1LA.lean)
proves the high-level *outcome* acceleration, while the result here
isolates exact primitive costs within a substantial branch. Earlier
Agent6 and Agent1 source-connected modular inverse sieves filter
genuine-root fatal candidates, remain open, and should be reused.
No academic priority or new BB(6) maximum bound is asserted.
