# Twelve exact source-counter exclusions inside the F321 4093 tail

**Status: Lean-kernel accepted.** GitHub Actions run
[46139830074](https://github.com/FlareZ123/bb6/actions/runs/46139830074)
regenerated all certificates from the exact symbolic predecessor generator and
compiled them with Lean 4.36.0-rc2.  The generated theorems use only the standard
axioms reported by the existing source-counter development
(`propext`, `Classical.choice`, `Quot.sound`); the audit rejects
`sorryAx` and `native_decide`.

## Theorem

Let `CounterReach` be the exact F321 source-counter reachability relation from
the authentic seed `(1,1)`.  For each residue

```text
r ∈ {
  126973, 200701, 225277, 237565,
  299005, 348157, 520189, 593917,
  618493, 630781, 692221, 741373
}
```

and for every `k,n : Nat`,

```text
¬ CounterReach 1 1 n (786432*k + r + 1) (786432*k + r).
```

Every listed residue is `4093 (mod 12288)`.  They are pairwise disjoint
modulo `786432 = 12288·64`, so they remove exactly 12 of the 64
three-base-4-digit refinements of the previously unresolved parent ray

```text
d ≡ 4093 (mod 12288).
```

Thus the theorem excludes exactly **3/16** of that parent arithmetic progression,
or natural density **1/65536** among all terminal parameters.

## Proof method

The source file
[`refined-subrays.json`](../im-results/agent2-f321-4093/refined-subrays.json)
records the residues and expected finite inverse-cone sizes.  The workflow
[`agent2-f321-4093-subrays.yml`](../.github/workflows/agent2-f321-4093-subrays.yml)
invokes the existing exact
[`affine_ray_generator.py`](../im-results/agent31-f321-mod384/affine_ray_generator.py)
for each residue.  Each generated Lean certificate:

1. enumerates a finite union of affine source-counter rays;
2. proves, branch by branch with exact arithmetic, that every genuine
   `CounterMove` predecessor of a ray in the union is again in the union;
3. proves that the authentic seed `(1,1)` is outside the union; and
4. inducts over arbitrary `CounterReach` length.

The proof is therefore an all-time source theorem.  It is not a bounded forward
simulation.

## Relation to the authentic reset-to-High obstruction

These twelve rays are genuine exclusions but they are side cylinders of the
`4093 mod 12288` parent.  The authentic long Middle-reset followed by
High-only terminal candidates lie on two narrower 2-adic spines converging to
the exceptional point `-3`; they are not removed by the twelve certificates
above.  The companion result
[`2026-11-28-f321-minus-three-reset-tail-sieve-obstruction-agent2.md`](2026-11-28-f321-minus-three-reset-tail-sieve-obstruction-agent2.md)
identifies that obstruction exactly and explains why merely increasing a fixed
terminal modulus cannot settle those root-specific tails.

This is a source-counter theorem for F321, not a proof of F321 blank-tape
nonhalting and not a BB(6) upper bound.
