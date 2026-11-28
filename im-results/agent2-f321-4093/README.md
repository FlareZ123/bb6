# F321 4093-tail three-base-4-digit refinement

This directory targets the exact shared long-tail terminal family already derived from
the root-specific Middle-reset/High-run theorems:

```text
d ≡ 4093 (mod 12288).
```

That parent ray is not closed by the existing uniform affine predecessor generator.
The obstruction is threshold-sensitive: one inverse Far branch reaches a ray with
first coordinate base 2, so the Far inverse exists only when the progression
parameter is positive. Refining the parent parameter by three base-4 digits
(`k = 64t+s`) exposes finite predecessor-closed subrays.

## New candidate subrays

Exact symbolic inverse search with the repository's proof-producing
`affine_ray_generator.py` closes the following 12 values of `s mod 64`:

```text
s ∈ {10,16,18,19,24,28,42,48,50,51,56,60}.
```

Equivalently, with modulus `786432 = 12288*64`, the candidate terminal parameters are

```text
d ≡ 126973, 200701, 225277, 237565,
     299005, 348157, 520189, 593917,
     618493, 630781, 692221, 741373      (mod 786432).
```

These rays are pairwise disjoint and all lie inside `4093 mod 12288`. Therefore,
once source-kernel accepted, they remove exactly `12/64 = 3/16` of that shared
Middle-reset/High terminal tail. As a subset of all natural terminal parameters,
their density is `12/786432 = 1/65536`.

The exact candidate list and expected finite inverse-cone sizes are recorded in
[`refined-subrays.json`](refined-subrays.json). The manual workflow
`.github/workflows/agent2-f321-4093-subrays.yml` regenerates every Lean proof from
the unchanged exact `CounterMove` source relation, checks the expected cone size,
compiles all twelve files with Lean 4.36.0-rc2, prints each theorem's axiom profile,
and rejects `sorryAx` / `native_decide`.

## Evidence boundary

Before that workflow succeeds, this directory records an exact computational
discovery and a proof plan, not an established source theorem. A successful generated
proof has the form

```lean
¬ CounterReach 1 1 n (786432*k+r+1) (786432*k+r)
```

for arbitrary natural `k,n` and one of the twelve residues `r` above. The
generator proves predecessor closure symbolically for every parameter value; it is
not a bounded forward simulation.

The remaining 52 three-digit subrays are deliberately left open here. Their failures
are mostly symbolic parity/threshold branches, with the recurring threshold branch
reflecting a genuine 4-adic descent rather than a numerical cutoff.
