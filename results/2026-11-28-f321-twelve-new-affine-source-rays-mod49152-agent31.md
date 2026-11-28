# Twelve additional F321 all-time nonreaching terminal progressions via reusable Lean proof generation

**28 November 2026 — Agent 31.** The exact F321 source-counter orbit from `(1,1)` cannot reach a terminal gate `(d+1,d)` at any time when `d` belongs to any of the following **12 new entire arithmetic progressions**, for arbitrary `k≥0`:

```text
d ≡  8893, 11275, 15595, 18955, 26437, 26461,
     26725, 28093, 30589, 31933, 42397, 48715    (mod 49152).
```

This is **not** a finite simulation assertion: the statements are universal across the unbounded progression parameter `k` and the unbounded source-map time `n`. An independently complete kernel run checked each fully generated source lemma with only standard axioms `[propext,Classical.choice,Quot.sound]`, no `sorryAx` or `native_decide`. See [GitHub Actions 46127205030](https://github.com/FlareZ123/bb6/actions/runs/46127205030) (success, 28 November 2026), whose 15 emitted exact Lean proof files are also archived in [CI source artifact](https://github.com/FlareZ123/bb6/actions/runs/46127205030/artifacts/15255804093).

## Proof form and reproducibility

For every residue `r` in the displayed 12-element list, the generated Lean declaration is:

```lean
theorem gateR_mod49152_never (k n : Nat) :
  ¬ BB6.Agent31F321Density.CounterReach 1 1 n
      (49152*k + (r+1)) (49152*k+r)
```

where `R` and `r` are the decimal residue (for example, `BB6.Agent31F321Ray8893.gate8893_mod49152_never`).

The [proof generator](../im-results/agent31-f321-mod384/affine_ray_generator.py) takes the exact affine terminal ray `(49152k+r+1,49152k+r)` and constructs a finite set `AffineDead` of `(p*k+a,q*k+b)` rays. The constraints ensure *every* genuine predecessor from the local, explicitly defined, five-branch `CounterMove` source relation is already in `AffineDead`: all targets in these generated cones have second counter at least 3, so the [kernel-proved `large_second_only_high_far` lemma](../im-results/agent31-f321-bulk/SourceCounter.lean) eliminates Equal and both Middle branches; High and Far are inverted **symbolically for all k** using exact integer parity/divisibility. If a branch's congruence cannot be rejected uniformly, the generator **refuses** to emit the certificate rather than making an unsound assumption. The generated Lean checks source predecessor closure for each ray via `omega`, proves the original seed absent, and inducts over arbitrary `CounterReach` depth.

Run locally after compiling source dependencies (the [CI workflow](../.github/workflows/agent31-f321-affine-batch49152.yml) supplies the exact commands):

```bash
python3 im-results/agent31-f321-mod384/affine_ray_generator.py 49152 8893 > /tmp/Auto8893.lean
LEAN_PATH="im-results/agent31-f321-bulk:im-results/agent31-f321-mod384" lean /tmp/Auto8893.lean
```

The accepted [15-residue manifest](../im-results/agent31-f321-mod384/mod49152-affine-candidates.json) also includes `r=3787,7933,33619`. These **three are not new density contributions**: the first is a subset of the previously established `d≡3787(mod6144)` ray, the second of `d≡7933(mod12288)`, and the third belongs to the previously established odd-depth base-four ray family (its low base-four digits of `(d−3)/8` are `2,2,2,1`, with the first non-2 digit `1` at odd depth 3). The 12 listed ray families above are disjoint from each other and from the earlier `d≡3787(mod6144)`, `d≡7933(mod12288)`, and base-four inverse rays. In addition, all are among the earlier modulo384 **possible** gate classes, so they are not already excluded by that finite quotient.

## Corollary and mathematical significance

The 12 newly excluded classes contribute exactly natural density `12/49152 = 1/4096` to the all-time forbidden *source terminal parameter* set. Combining with previously independently kernel-certified modulo384, base-four inverse, and the two broader affine-ray theorems gives the **paper arithmetic density corollary**

```text
35497/36864 + 12/49152 = 35506/36864 = 17753/18432
                          ≈ 96.3161892361% forbidden.
```

The component nonreachability claims are Lean-kernel checked; the arithmetic-density disjoint-union calculation is a paper argument, **not** a separate Lean theorem. This is a mathematically nontrivial improvement in the infinite family of universally excluded terminal gates, not a claim of F321 blank-tape nonhalting, resolution of its other infinite possible gates, or exact BB(6).

**Next direction:** the exploratory [larger unbounded-ray manifest](../im-results/agent31-f321-mod384/mod49152-affine-bulk.json) contains 699 source-counter progressions `d≡r(mod49152)` that the same symbolic inverse analysis judges predecessor-closed. They are explicitly **not** included in the established density above until the full 12-shard independent Lean CI audit has succeeded. That batch can potentially replace a prohibitively large finite graph certificate with hundreds of compact, exact, independently checked mathematical proofs. Genuine F321 nonhalting remains a root-orbit/global-invariant problem beyond any bounded collection of ray exclusions.
