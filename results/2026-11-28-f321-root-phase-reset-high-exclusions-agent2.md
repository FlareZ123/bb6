# F321 root phase invariants and reset-to-high terminal-family exclusions

**28 November 2026 — Agent 2.** This result gives root-specific, all-depth constraints for the exact F321 source-counter orbit from `(1,1)`. It strengthens the existing terminal-residue sieves in a different direction: rather than increasing a fixed finite modulus, it constrains entire variable-length high-run families following authentic middle resets.

All principal statements below are Lean 4 kernel checked against the exact published `CounterMove` source relation. GitHub Actions run [46128963897](https://github.com/FlareZ123/bb6/actions/runs/46128963897) completed successfully. The proof files are in [`im-results/agent2-f321-diagonal/`](../im-results/agent2-f321-diagonal/).

## Exact diagonal coordinates and bulk runs

Set

```text
X(a,d) = a+d+5
Y(d)   = 2(d+3).
```

Then the terminal condition `a=d+1` is exactly the diagonal `X=Y`. The live source branches admit the following exact coordinate descriptions:

- High: `Y<X`, with `(X,Y) -> (X+1,2Y)`.
- Equal: `Y=X+1`, with `(X,Y) -> (X+5,8)`.
- Far: in its exact guard region, `(X,Y) -> (X+6,4Y+12-6X)`.
- Middle-even and middle-odd reset `Y` to `10` and `8`, respectively; their parity guard is the parity of `X`.

[`DiagonalCoordinates.lean`](../im-results/agent2-f321-diagonal/DiagonalCoordinates.lean) proves these identities directly from `CounterMove`.

[`BulkRuns.lean`](../im-results/agent2-f321-diagonal/BulkRuns.lean) additionally proves arbitrary-length source-faithful High and Far accelerators. For a High run of length `n`,

```text
X_n = X_0+n,
Y_n = 2^n Y_0.
```

For a Far run of length `n` from `(a,d)` to `(A,D)`,

```text
A+2 = (a+2)4^n,
D + (a+2)(4^n-1) = d+6n.
```

This closes the previous gap between the paper/JavaScript bulk formula and a kernel theorem for arbitrary source-faithful run lengths.

## Root-specific phase invariants

[`Phase6.lean`](../im-results/agent2-f321-diagonal/Phase6.lean) proves that every positive-time source state reachable from `(1,1)` lies in exactly one of the three allowed structural classes

```text
(a mod 2, d mod 6) in {(0,1),(0,2),(1,5)}.
```

This is an inductive all-depth invariant, not an observed prefix property. In particular, every reachable middle-odd predecessor has `a` even and `d ≡ 1 (mod 6)`.

[`Phase12.lean`](../im-results/agent2-f321-diagonal/Phase12.lean) proves the sharper invariant

```text
(a odd  and d ≡ 5 mod 12)
or
(a ≡ 0 mod 4 and d ≡ 1 mod 6)
or
(a ≡ 2 mod 4 and d ≡ 1 or 2 mod 6).
```

For a reachable middle-even predecessor this collapses to only

```text
(a odd and d ≡ 5 mod 12)
or
(a ≡ 2 mod 4 and d ≡ 2 mod 6).
```

[`Phase6Bridge.lean`](../im-results/agent2-f321-diagonal/Phase6Bridge.lean) transports the root invariant to the repository's canonical `CounterReach 1 1` relation used by the F321 source/physical bridge.

## Two infinite reset-family exclusions

Let a reachable middle-odd predecessor take its reset branch to `(4a+6,1)`, and suppose the source then takes exactly `k` consecutive High branches and lands on a terminal gate. [`ResetHigh.lean`](../im-results/agent2-f321-diagonal/ResetHigh.lean) proves

```text
k ≡ 4 (mod 8),
D+3 = 4*2^k.
```

The generic reset arithmetic only gives `k ≡ 0 (mod 4)`; the authentic root invariant therefore eliminates the entire complementary infinite family `k ≡ 0 (mod 8)`.

For a reachable middle-even predecessor resetting to `(4a+6,2)`, [`ResetEven.lean`](../im-results/agent2-f321-diagonal/ResetEven.lean) proves

```text
k mod 16 in {7,11,15},
D+3 = 5*2^k.
```

The generic branch arithmetic gives only `k ≡ 3 (mod 4)`. Thus the root-specific Phase12 invariant eliminates the entire `k ≡ 3 (mod 16)` subfamily.

These are infinite variable-run restrictions. They are qualitatively different from excluding a fixed collection of terminal residues.

## Shared long-tail target

A direct arithmetic consequence of the two proved terminal formulas is that every sufficiently long terminal gate whose last non-High step is one of the two Middle resets lies in one common arithmetic ray:

```text
D ≡ 4093 (mod 12288).
```

More precisely:

- middle-odd: the only exceptional allowed length below the stable tail is `k=4`, giving `D=61`; every allowed `k>=12` gives `D ≡4093 (mod12288)`;
- middle-even: the exceptional allowed lengths below the stable tail are `k=7` and `k=11`, giving `D=637` and `D=10237`; every allowed `k>=15` gives `D ≡4093 (mod12288)`.

The congruence calculation in this subsection is a paper corollary of the Lean-proved run-length and parameter formulas. The existing affine-ray proof generator does **not** currently certify the `4093 mod 12288` ray: its uniform inverse search reaches a boundary ray with base first coordinate `2`, where the Far inverse exists only for positive progression parameter. This identifies a concrete proof-engineering target: split that threshold case instead of enlarging the terminal modulus again.

## Scope

This result does **not** prove F321 nonhalting, close the Raw132 parent, or establish the BB(6) upper bound. A last non-High transition may also be Far or Equal, and the `4093 mod 12288` ray remains unexcluded. The advance is an exact root-specific restriction on two complete infinite terminal mechanisms plus kernel-certified arbitrary-length High/Far acceleration, providing a smaller and more structured frontier for the remaining F321 proof.
