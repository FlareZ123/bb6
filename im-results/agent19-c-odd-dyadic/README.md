# Machine C: an unbounded alternating dyadic predecessor obstruction

**Agent 19, 2026-11-05.** Original Machine C:
`1RB1LC_1LC1RD_1LA0LB_0RB1RE_1RF0RA_---0RC`.
The authentic blank-section entry is `(5,1)`, with exact source map
`BB6.Agent46.secNext`. The exact value of BB(6), the behavior of
Machine C on its blank start, and the remaining original high stopping
families are all **undecided**.

This directory derives a new all-exponent family of configurations
excluded from the **actual blank-origin section**. The method composes
Agent 24's already source-certified six-residue even-right inverse
equivalence with Agent 3's previously source-certified odd-right image
invariant. It provides an explicit closed form across arbitrarily many
forced inverse edges, and yields a new high stopping-depth family whose
first counter is 3 modulo 8.

## The new all-depth theorem

For every `n,x,w : Nat` satisfying

- `7 ≤ w`, `w % 4 = 3`;
- if `n` is even, `x % 8 = 7`; if `n` is odd, `x % 8 = 3`;

the proposed authentic-source theorem is:

```lean
¬ BB6.Agent3.CReach x (2^(n+2)*w-2)
```

Here `CReach a k` means an **actual finite return time** of the
original Machine C blank-section orbit from `(5,1)`. In particular,
the theorem is independent of any simulation bound and quantifies over
every exponent `n`.

The abstract mathematical result `tower` in
[`OddTowerGeneric.lean`](./OddTowerGeneric.lean) compiled successfully
with local Lean **4.36.0-rc2**. Its axiom audit is exactly
`[propext, Quot.sound]`. The original-source adapter
[`OddTowerSource.lean`](./OddTowerSource.lean) invokes the published
genuine `six_even_right_blank_reach_iff` and
`blank_section_odd_image` theorems, without redefining either source
map or its reachability predicate. An original-source CI audit is
required before describing that adapter as fully verified.

### Proof structure

For the base exponent `n=0`, the candidate `(x,4w−2)`
(`x≡7 mod8`, `w≡3 mod4`) has two forced predecessors:

```text
(x, 4w−2)
  <- (x+4w−4, 2w−2)
  <- (x+6w−8, w−2).
```

The final predecessor has an odd second counter at least five and
coordinate sum `x+7w−10 ≡2 (mod4)`. That contradicts the genuine
blank-section odd-image theorem. For the induction, put
`q=2^n w≥7`. A candidate at exponent `n+1` has even second
counter `8q−2` and the unique predecessor
`(x+8q−4,4q−2)`. Its first coordinate moves by four modulo eight;
the parity-dependent first-counter condition flips exactly as needed.
The induction is valid for **all** `n`.

The deeper `n=1` cylinder is

```text
∀ u v, v≥1 -> ¬ CReach (8u+3) (32v+22).
```

For example, `(59,7894)` has the three mathematically forced
predecessors `(7951,3946)`, `(11895,1972)`, `(13865,985)`.
The terminal coordinate sum is 14850, congruent two modulo four, and
the terminal second coordinate is odd and greater than five. This
example only illustrates the general proof.

The `n=0` slice overlaps the previously certified Agent 15 / Agent
41 `(8u+7,16v+10)` cylinder, whereas the `n=1` slice has
`(a,k)≡(3,22)` modulo `(8,32)`. Explicit prior-art comparison is
still needed for the deeper cylinders, including previous source and
external machine C work.

## A new original high-halting-parameter family

Agent 15's original complete section stopping equation includes
`a=2j+3` with
`k+j+3m+5=2^(2m+2)(j+3)`. The separate
[`OddTowerArithmetic.lean`](./OddTowerArithmetic.lean) proves in local
Lean that, whenever `m≥3`, `j%4=0` and
`(j+3m+3)%32=8`, any such `k` satisfies:

```text
a=8u+3, k=32v+22, v≥1
```

for some natural `u,v`. In particular, these **eight distinct
congruence pairs modulo 32** are excluded from blank-origin halting
once the source connection is certified. The pairs `(j,m)%32` are:
`(0,23)`, `(4,11)`, `(8,31)`, `(12,19)`,
`(16,7)`, `(20,27)`, `(24,15)`, `(28,3)`.
They are disjoint in their `j%4=0` sector from the earlier Agent 24
high exclusions `j%4=1,3` and the imported M8 `j%4=2` family.

[`OddTowerResidual.lean`](./OddTowerResidual.lean) composes the
new obstruction with the existing exact original-source eight-part
halting iff. It preserves all remaining low- and high-family
possibilities. Nothing here establishes that Machine C never halts.

## Evidence and caveats

- Exact standalone Lean command: compile
  `OddTowerGeneric.lean` and `OddTowerArithmetic.lean` using
  Lean 4.36.0-rc2. Both succeeded locally with only
  `[propext, Quot.sound]`, no `sorry`, `admit`, or custom axiom.
- Source-dependent compilation: manually dispatch
  [`agent19-c-odd-dyadic.yml`](../../.github/workflows/agent19-c-odd-dyadic.yml).
  It reconstructs the original source chain and compiles the unchanged
  real Machine C map and all dependencies. Initial runs
  [42093811692](https://github.com/FlareZ123/bb6/actions/runs/42093811692)
  and [42094307213](https://github.com/FlareZ123/bb6/actions/runs/42094307213)
  **failed** at isolated numeral-normalization tactics, with the
  mathematical theorem bodies unaltered; the latest version replaces
  these gaps using independently compiled arithmetic.
- The source-specific final declarations and their final
  `#print axioms` must be checked in a **successful** manual run
  before any blanket source-certification claim.
- No global upper bound on BB(6) follows; the source-specific
  theorem is about one known unresolved machine. Novelty relative to
  published outside certificates has not been independently audited.

## Next direction

The all-exponent theorem suggests systematically reducing the high
halting locus using the 2-adic order of `k+2`, instead of accumulating
unrelated fixed-modulus cylinders. The most important continuation is
to characterize all high-gate parameters whose odd part of `k+2`
falls in this forbidden residue and find a uniform closure for the
remaining residue classes, including branches where the forced
predecessor mechanism stops at section sum residue seven modulo eight.
