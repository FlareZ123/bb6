# An unbounded marker-gap recurrence proves nonhalting of the q0-148 F1-open child cylinder

**Theorem (Agent5 and Agent39).** Every completion of the six-state, two-symbol partial table

```
1RB1LC_1RC0RE_0LA0LD_1LA0RF_1RB1RD_0RC---
```

is nonhalting from the blank tape. In particular its undefined F1 instruction is never queried. **Scope:** this is the one-hole F1-open child cylinder beneath the seven-hole Raw11 q0-148 parent, not a Cover of that entire seven-hole parent. The original-table theorem `BB6.Agent5Q0148NeverCover.never_cover : Cover NeverHalts p` is kernel accepted in Lean 4.36.0-rc2 in the pinned [source CI 46178357131](https://github.com/FlareZ123/bb6/actions/runs/46178357131), source revision [4051a6e314624eb7276766ceb40daba45b643c84](https://github.com/FlareZ123/bb6/commit/4051a6e314624eb7276766ceb40daba45b643c84), artifact `15276228192`, with axioms precisely `[propext, Classical.choice, Quot.sound]` and no `sorryAx`. Earlier source acceptance is also recorded in [CI 46117258887](https://github.com/FlareZ123/bb6/actions/runs/46117258887). The all-threshold weighted adapter `Q0148WeightedCover.lean` imports this theorem and is wired as the exact external region cut in `generate-coarse-parent-shards.cjs`; its dedicated source audit [46179174488](https://github.com/FlareZ123/bb6/actions/runs/46179174488) is in progress. The seven-hole q0-148 parent still needs its other branches and final source join.

## A growing, nonperiodic-shaped region

Let A=10, M=110, and write a physical boundary tape as

    A^a M A^g1 M ... M A^g(m-1) M A^4

with exterior zeros, head E on the third A of the terminal four, m odd ≥3, a∈{1,3}, interior gi odd ≥3, consecutive interior differences 0 or 2, and g(m−1)∈{3,5}. Impose g1∈{m+a−3,m+a−1}. The actual packed blank execution reaches (a;g1,g2;4)=(3;3,3;4) after **695 primitive transitions**, a kernel-decided equality of original-source configurations.

Use b=(a−1)/2, r=(m−1)/2, xs=[(g1−1)/2,...,(g(m−1)−1)/2]. This gives the invariant `Good b r xs`: b≤1, r≥1, |xs|=2r, neighboring parameters descend by 0 or1 to a terminal 1 or2, and r+b=xs[0] or xs[0]+1. Define

    r' = r+b
    b' = 1 if xs[0] = r+b, else 0
    xs' = map (+1) (tail xs) ++ (if b=0 then [2] else [2,1,1]).

This explicitly updates every tape gap and allows arbitrary marker count. No finite radius, simulation limit, repeating global configuration, or fixed-length word assumption is used.

The new tail is again a descending-by-0/1 chain terminating at 1 or2. Its length is 2(r+b); the head parameter condition follows from the old head condition and the adjacent 0/1 difference. This proves the exact arithmetic induction, formalized in `Q0148GapInvariant.good_next`.

## Exact source return

The machine's original partial zipper semantics is used throughout. Its source leftward and rightward sweeps are expressed as alternating chunks and a separated marker chunk 11010. Arbitrary untouched tape tails are quantified in the finite primitive-transition gadgets and their list induction. There is a three-state carry transducer with bit residues 11, 1101 and 1. The old a=1 boundary resets to the first marker train after two blank turns; a=3 requires three cycles as encoded by the separate carry outputs.

The future right-marker parameter list is

    future = map (2*) (tail xs) ++ (if b=0 then [2,0] else [2,0,0,0]).

The exact list identity `future_eq` gives future = map (u ↦ 2(u−1)) xs' ++ [0]. With j=2 xs[0]+1 and H=|future|, the old invariant gives j=H in the high branch and j+2=H in the low branch. Agent39's ordinary marker-hop source theorem decreases the far-left debt by one and prepends the crossed marker index. The arbitrarily long high train has exactly the available debt. The low train executes all ordinary hops, then two exact exceptional gap-two/gap-one splices, ending without reading F1. Both are universally quantified source-run equalities, including the unbounded gap lengths and number of markers.

The canonical head-relative packed encoding removes redundant exterior blank zeros, so the terminal high/low source frames denote precisely the boundary of (b',r',xs'). The theorem `Q0148EpochConnect.packedEpoch` instantiates the return using original source-reset and marker-train lemmas. In `Q0148NeverCover` all four source hypotheses are discharged from the actual imported source modules. The verified relation is a **positive defined return**, not a theorem that this is the *least* positive return. Least return is unnecessary: every valid configuration has a finite nonempty defined run to another valid configuration. Induction gives arbitrarily long defined prefixes, and compatibility transfers them to every total completion. This is the unconditional blank-root nonhalting theorem.

## Source and scope

- [Arithmetic invariant](../im-results/agent5-weighted-tnf-queue/Q0148GapInvariant.lean), [packed blank bridge and generic Cover](../im-results/agent5-weighted-tnf-queue/Q0148PackedBoundary.lean), [exact tape algebra](../im-results/agent5-weighted-tnf-queue/Q0148BoundaryAlgebra.lean), [epoch composition](../im-results/agent5-weighted-tnf-queue/Q0148EpochConnect.lean), [unconditional Cover](../im-results/agent5-weighted-tnf-queue/Q0148NeverCover.lean), [weighted Cover](../im-results/agent5-weighted-tnf-queue/Q0148WeightedCover.lean).
- [Original transition sweep gadgets](../im-results/agent5-weighted-tnf-queue/Q0148BoundarySweep.lean) and [Agent39's reset and marker-train source construction](../im-results/agent39-q0148-carry/README.md). Agent5 derived the boundary grammar, arithmetic closure, authentic packed base and packed splice; Agent39 derived the parametric source carry and high/low marker trains; Agent5 repaired and compiled the full chain against the original source.
- Reproduce at the pinned revision using the existing grammar-epoch workflow or `tools/lean_compile_closure.py im-results/agent5-weighted-tnf-queue/Q0148NeverCover.lean` after unpacking the repository coverage core. The CI source audit is the primary external reproduction.

This discharges the last **hard** exception of the frozen q0-148 parent `1RB1LC_1RC---_0LA0LD_------_------_------` (4,789,377-node discovery tree; [run 46057416175](https://github.com/FlareZ123/bb6/actions/runs/46057416175)). Another independent [glider cylinder](../im-results/agent5-weighted-tnf-queue/q0-148-right-glider.md) is source accepted; the remaining 22 exceptions have finite first-hole witnesses ≤6158 transitions. The exact original-source weighted parent proof and global roster consumer are distinct remaining acceptance edges. No universal BB(6) upper bound follows from this cylinder alone.
