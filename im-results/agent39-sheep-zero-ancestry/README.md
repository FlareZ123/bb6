# Agent 39: exact 3-adic inverse corridors in the Sheep return graph

**Classification:** intermediate, rigorously Lean-checked, no unresolved-holdout decision and no BB(6) bound. Original six-state machine: `1RB1LA_0LC0RC_1LE1RD_1RE1RC_1LF0LA_---1LE`. Its published machine-certified section starts from `t=5` and halts iff an iterate reaches a power of two. The source-level TM/counter correspondence was already established independently by Agent 22 in [CI 41390686337](https://github.com/FlareZ123/bb6/actions/runs/41390686337). All this development concerns exact *generic valuation-zero* branches of the return graph; it does not decide the blank-entry orbit.

## Exact inverse ancestor theorem

Let `Parent0(x,y)` mean `x>=5`, `x` odd, and `3*x=2*y+1`. This is literally the published generic section edge for `a=0`: `x -> (3*x-1)/2`. Let `Chain0(h,x,y)` mean precisely `h` consecutive Parent0 edges (with `Chain0(0,x,x)`).

The fully quantified theorem `chain_target_iff_divisible` proves, for **every** `h` and target `y>=5`,

```
(∃ x, Chain0 h x y)  ↔  3^h ∣ (y-1).
```

When an ancestor exists it is **unique**, and its explicit value is

```
y = 1 + 3^h*m,       x = 1 + 2^h*m.
```

The proof uses exact multiplicative displacement `3^h*(x-1)=2^h*(y-1)`, coprimality of `2^h` and `3^h`, and a constructive all-depth chain. The target threshold `y>=5` is essential: `y=4,h=1` would have the invalid predecessor `x=3`.

The [source-level counter bridge](./ZeroAncestryBridge.lean) proves that **every** such `Parent0` is the actual `SheepBridge.SectionNext.general 0` relation in Agent 14's unmodified `CounterBridge.lean`. Every finite chain therefore expands to genuine finite Sheep counter transitions. It is strictly a local inverse-corridor theorem and says nothing about reachability of these predecessors from `t=5`.

## Sharp characterization for power-of-two halting targets

The standalone arithmetic file [ThreeAdicOrder.lean](./ThreeAdicOrder.lean) proves, with no Mathlib dependency, that the *exact* multiplicative order of `2` modulo `3^(k+1)` is `2*3^k`:

```
(∃ m, 2^j = 1+3^(k+1)*m)  ↔  2*3^k ∣ j.
```

Its proof develops a cubic-lifting sequence `Q(k)`, proves `Q(k)%3=1`, a quotient-of-powers recurrence `W` with `W(d,q,n)%3=(n*q)%3` when `3|d`, and performs induction on the modulus exponent. Unlike merely proving a sufficient exponent family, this establishes the **necessary** period as well.

Combining that exact order with the inverse corridor theorem, [PowerCorridor.lean](./PowerCorridor.lean) establishes for every `j>=3` and `k>=0`:

```
(∃ x, Chain0 (k+1) x (2^j))  ↔  2*3^k ∣ j.
```

The ancestor `x` is unique at every permitted depth. These are real inverse paths, but the actual blank orbit might never enter their initial vertices.

## A uniform finite-depth obstruction in 100 residue classes

[ResidueCorridor.lean](./ResidueCorridor.lean) strengthens Agent 22's known zero-residue construction: **all 100 classes** `r ≡ 0 (mod 54)` among `0,...,5399 (mod 5400)` contain targets with genuine zero-valuation ancestors of every prescribed depth.

Explicit construction: for `s>=1`, `k>=0`, put

```
j(s,k) = 54*s*3^(40*k).
```

Because `3^40 = 1 (mod 100)`, proved by Lean's exact arithmetic, `j(s,k) ≡ 54*s (mod 5400)`. And `2*3^k | j(s,k)`, so the sharp power corridor theorem supplies a chain of length `k+1` ending at `2^j(s,k)`. As `s=1,...,100` varies, these are exactly the 100 distinct multiples-of-54 classes, including zero at `s=100`. The [ActualResidue.lean](./ActualResidue.lean) module transfers every family to exact original Agent 14 counter-machine `Steps` through the already-certified bridge.

This creates a **mathematical barrier to uniform finite-depth inverse-tree certificates based only on predecessor exhaustion** for any of these 100 classes. It does **not** prevent proofs that use reachability invariants, forward dynamics, unbounded-depth induction, or target-specific bounds.

**Adversarial check:** independently reimplemented Agent 17's exact inverse-sieve recursion and checked these 100 classes; none were among the purported 3,544 excluded classes. This is consistent with the structural obstruction, and no contradiction in Agent 17's reporting was found. The full certification of Agent 17's 3,544 classes is a separate matter.

## Complete forward odd run

[ForwardBlock.lean](./ForwardBlock.lean) proves for every `u` odd and `x=1+2^h*u>=5` that

```
x  --[h consecutive zero-valuation Sheep returns]-->  1+3^h*u,
```

the endpoint is **even**, and no all-zero-valuation extension to length `h+1` exists. This is an exact symbolic compression of maximal odd runs, potentially useful for an alternative forward section accelerator.

## Verification and boundaries

- `ZeroAncestry.lean`: exact any-target criterion, source/target uniqueness.
- `ZeroAncestryBridge.lean`: identical, actual unmodified Agent 14 section transitions and counter `Steps`.
- `ThreeAdicOrder.lean`: standalone all-level multiplicative order.
- `PowerCorridor.lean`: exact target-power exponent criterion.
- `ForwardBlock.lean`: maximal odd-run accelerator.
- `ResidueCorridor.lean`, `ActualResidue.lean`: 100-class unbounded inverse-depth family and original-counter bridge.
- Manual-only, no push trigger: [agent39-sheep-zero-ancestry.yml](../../.github/workflows/agent39-sheep-zero-ancestry.yml), Lean 4.36.0-rc2. Successful original-counter source checks: [CI 41429875132](https://github.com/FlareZ123/bb6/actions/runs/41429875132), [CI 41430890380](https://github.com/FlareZ123/bb6/actions/runs/41430890380), [CI 41431688084](https://github.com/FlareZ123/bb6/actions/runs/41431688084). All displayed final proofs audit only usual logical axioms `propext`, `Classical.choice`, `Quot.sound` or subsets, no `sorryAx`.
- The latest `ActualResidue.lean` source-counter integration also passed complete CI [41431834393](https://github.com/FlareZ123/bb6/actions/runs/41431834393), including all modules and standard-only axiom audits.

Known mathematical background on orders modulo prime powers exists; no claim that those arithmetic identities are new to mathematics. The specific synthesis is a useful new verified research tool within this shared repository. Infinite reverse ancestry is **not evidence that any ancestor is reachable from the actual start**. None of these results establishes the Sheep holdout's nonhalting, a new six-state Busy Beaver bound, or BB(6)'s exact value.
