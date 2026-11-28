# F321 reset-to-High tails converge to the exceptional 2-adic point -3

**Status: Lean-kernel accepted.**  The root-tail alignment theorem passed shared
source-closure CI run
[46139289738](https://github.com/FlareZ123/bb6/actions/runs/46139289738);
the exact bounded-sieve obstruction passed run
[46139762995](https://github.com/FlareZ123/bb6/actions/runs/46139762995).
Both compile against the exact repository `CounterMove` / `CounterReach`
development with no `sorryAx` or `native_decide`.

## 1. The two persistent inverse-search spines are the authentic root tails

For a root-reachable Middle-odd reset followed only by High steps to the terminal
gate, the existing root theorem gives

```text
D + 3 = 4·2^k,     k ≡ 4 (mod 8).
```

For sufficiently long tails write `k=10+2m`.  Then

```text
D = 12288 E_m + 4093,
E_0 = 0,
E_(m+1) = 4 E_m + 1,
m ≡ 1 (mod 4).
```

This is exactly the recurring threshold-sensitive Far-predecessor spine seen by
the symbolic affine-ray search.

For a root-reachable Middle-even reset followed only by High steps,

```text
D + 3 = 5·2^k.
```

Writing `k=15+4j` gives

```text
D = 12288 J_j + 4093,
J_0 = 13,
J_(j+1) = 16 J_j + 5.
```

The root mod-16 theorem excludes `j≡1 (mod4)`; the previously kernel-checked
valuation theorem further excludes the case where `j+5` has odd 2-adic
valuation.  This is the symbolic search's recurring unbounded Middle spine.

These identifications are formalized in
[`ObstructionAlignment.lean`](../im-results/agent2-f321-4093/ObstructionAlignment.lean).

## 2. Both authentic families converge 2-adically to -3

Define

```text
NearMinusThree(N,D)  :⇔  ∃q, D+3 = 2^N q.
```

Lean proves:

- every M1 terminal tail satisfies `NearMinusThree(N,D)` whenever
  `N ≤ k+2`;
- every M2 terminal tail satisfies `NearMinusThree(N,D)` whenever
  `N ≤ k`.

Hence for every fixed dyadic modulus `2^N`, all sufficiently long authentic
reset-to-High candidates satisfy

```text
D ≡ -3 (mod 2^N).
```

The long root tails therefore converge to the same exceptional 2-adic point
already visible in the generic inverse-word density theorem.

## 3. Exact limitation of every fixed-depth residue certificate

Let `farWord n` be the length-`n` formal inverse word consisting entirely of
Far letters.  The accepted Lean proof in
[`AllFarObstruction.lean`](../im-results/agent2-f321-4093/AllFarObstruction.lean)
derives exactly

```text
compile(farWord n).u     = 1,
compile(farWord n).shift = 2n,
compile(farWord n).v     = 3 - 2·4^n.
```

Consequently, if `D+3` is divisible by `4^n`, the all-F word has zero
residue modulo its required power of two.  In the terminology of the existing
density-one source theorem,

```text
NearMinusThree(2n,D)  ->  ¬ NoResidueWord n D.
```

The proof then composes this identity with the authentic M1 and M2 terminal
formulas:

- every sufficiently long authentic M1 reset-to-High candidate defeats the
  depth-`n` `NoResidueWord` premise;
- every sufficiently long authentic M2 reset-to-High candidate does the same.

This is a theorem about the **certificate premise**, not evidence that those
candidates are reachable.  It pinpoints a real method boundary: no fixed-depth
instance of the terminal-only inverse-residue sieve can eliminate the complete
long reset-to-High obstruction.  Raising a fixed terminal modulus merely pushes
the same `-3` cylinder deeper.

## Consequence for the F321 program

The unresolved proof obligation has moved upstream.  A complete F321 decision
must constrain the root-reachable reset/anchor predecessor, couple that state to
the subsequent High/Far inverse structure, or use an invariant that is not only
a fixed terminal dyadic suffix.  Continuing to accumulate fixed terminal
quotients cannot by itself close these authentic long tails.

This materially narrows the remaining mechanism but does not prove F321
nonhalting, Raw132 closure, or the BB(6) upper bound.
