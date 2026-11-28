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


## Root-tail obstruction discovered after the refinement search

The 12 finite affine rays above are useful generic terminal-gate exclusions, but
they are **not** the authentic long reset-to-High candidates.  The root-specific
terminal equations identify two exceptional spines inside the parent
`4093 mod 12288` ray:

- M1 / middle-odd reset: `D+3 = 4*2^k`, and the root theorem forces
  `k % 8 = 4`.  Writing `k=10+2m`, the long candidates satisfy
  `D = 12288*E_m +4093`, where `E_0=0`,
  `E_(m+1)=4*E_m+1`, and the root restriction becomes `m%4=1`.
- M2 / middle-even reset: `D+3 = 5*2^k`.  Writing `k=15+4j`,
  the long candidates satisfy `D = 12288*J_j+4093`, where
  `J_0=13`, `J_(j+1)=16*J_j+5`.  The root mod-16 theorem excludes
  `j%4=1`, and the existing valuation theorem further excludes odd
  2-adic valuation of `j+5`.

These are exactly the two structured failure spines encountered by the symbolic
inverse search: the recurring Far-threshold branch and the unbounded middle
branch.  The identification is formalized in
[`ObstructionAlignment.lean`](ObstructionAlignment.lean).

More importantly, both authentic terminal families converge 2-adically to
`-3`: for every fixed `N`, once the High length is large enough,
`D+3` is divisible by `2^N`.  This is the same exceptional 2-adic point
already visible in the generic density-one inverse sieve through its all-F word.

[`AllFarObstruction.lean`](AllFarObstruction.lean) makes the limitation exact.
If `D+3` is divisible by `4^n`, the length-`n` all-F inverse word has
zero residue, hence `NoResidueWord n D` is false.  Therefore every sufficiently
long authentic M1 or M2 reset-to-terminal High tail defeats the generic
depth-`n` modular-exclusion premise for that fixed `n`.

This changes the research priority: increasing a fixed terminal modulus can keep
certifying side rays, but it cannot resolve the authentic long reset tails.
The next decisive invariant must constrain the **root-reachable reset
predecessor** (or couple the reset state to deeper inverse structure), rather than
only the terminal parameter modulo a larger power of two.
