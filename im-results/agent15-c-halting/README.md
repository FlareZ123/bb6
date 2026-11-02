# Exact all-depth halting locus of the Machine C arithmetic section (Agent 15)

**Status:** mathematical intermediate result, *not* a Machine C or BB(6) decision. All statements concern the genuine blank-origin accelerated Machine C map once combined with the already verified source bridge. No upper bound on BB(6) or machine-wide halting claim is established.

## Source and theorem chain

This work imports Agent 46's unchanged **total** arithmetic two-counter zero-high section interpreter `BB6.Agent46.secNext`, whose semantic equivalence to the original Machine C accelerated map is already certified in `Agent46CBridge.lean`. Its true blank-origin section starts at `(5,1)`; `BB6.CReachBridge.RunHalts` denotes the source-connected accelerator stopping predicate. The Machine C raw Turing machine is
`1RB1LC_1LC1RD_1LA0LB_0RB1RE_1RF0RA_---0RC`.

The exact recursive interpreter `bounce(k,c)` from `BounceCalc.lean` has an intricate stopping branch: `k` even and `c=5` at some recursive depth, while the other branches either return a successful section state or recurse with a new parameter. Define, for all `k,n : Nat`,

```text
H(k,0)   = 5
H(k,n+1) = H(2k+4,n) + 2k+5
```

The new Lean theorem `BB6.Agent15.bounce_halts_iff_seed` establishes the **complete necessary and sufficient** stopping criterion for `c≥4`:

```text
bounce(k,c).2 = none  ↔  k%2=0 and there exists n with c=H(k,n).
```

Its proof uses strong induction on the decreasing height `c` for the converse and ordinary induction on `n` for the construction. The odd-`k` recursion can never halt for `c≥4`. The exact closed dyadic identity `seed_power_equation` is

```text
H(k,n)+3n+2(k+4) = 2^(n+1)(k+4)+5 .
```

The theorem `bounce_halts_iff_power` therefore eliminates the recursively defined seed, giving an equivalent single-exponential Diophantine equation.

The new theorem `BB6.Agent15.section_halts_iff_diophantine` in `SectionPower.lean` classifies **all input pairs `(a,k)`**, with no finite search cutoff:

```text
secNext(a,k)=none  ↔
  (a=0 and k=0)
  or (a=1 and k≥4 and exists n,
      2k+3n+8 = 2^(n+4))
  or (a≥2 and k≥1 and a<2k and a odd and exists n,
      2k+a+3n+4 = 2^(n+1)(a+3)).
```

The first two low-counter exceptional cases and the general `a≥2` case are all source cases, so this is globally exhaustive for `secNext`. In the latter clause `a` must be odd, reflecting the even middle-counter requirement for the halting bounce.

The strongest theorem `BB6.Agent15.blank_halts_iff_diophantine_gateway` in `BlankHalting.lean` proves

```text
CReachBridge.RunHalts  ↔
  exists m,a,k,
    run secNext m (some(5,1)) = some(a,k)
    and one of the three clauses above holds.
```

It composes the existing exact machine-section halting bridge with a new general theorem characterizing eventual `none` as reachability of an immediate stopping input. The right side is an all-time **blank-orbit reachability** obligation for a precisely specified Diophantine locus. No claim has been made that the orbit reaches or avoids the locus.

## Evidence and reproduction

- `BounceHalting.lean`: strict total recursion, odd-bounce no-halt, two-sided infinite seed characterization and closed power identity.
- `SectionHalting.lean`: complete 3-case source section stopping condition in terms of `H(k,n)`.
- `SectionPower.lean`: exact Diophantine section criterion.
- `BlankHalting.lean`: full blank-section stopping iff-reduction.
- `.github/workflows/agent15-c-halting.yml`: **manually dispatched only**; compiles the unmodified original `CLine`, original C source bridge, Agent46 section proof chain and new Lean sources under pinned Lean 4.36.0-rc2. A prior source-level [run 41463374307](https://github.com/FlareZ123/bb6/actions/runs/41463374307) succeeded on the first two source files, and [run 41463770180](https://github.com/FlareZ123/bb6/actions/runs/41463770180) succeeded including the Diophantine section theorem. Full original-source blank-origin extension [CI run 41464333988](https://github.com/FlareZ123/bb6/actions/runs/41464333988) **SUCCEEDED**, certifying the final theorem against the unmodified source semantics.

All three constituent source-level successes contain only standard Lean axioms in `#print axioms`; local `BlankHalting.lean` also compiled with only those axioms, but the full unchanged-source CI is the authoritative verifier. None uses `sorry`, `admit`, `native_decide`, or a new axiom.

## Mathematical limitations and next move

This improves the exact representation of the possible **immediate stopping section inputs**, replacing a recursive bounce test with one exponential equation. This is useful for a uniform reverse-reachability investigation, but it **does not** by itself reduce the undecidable blank-orbit existence question to a decidable one: both `m` and `n` range over all naturals. Agent3, Agent6, Agent38 and Agent46 already provide a collection of all-time blank-section modular restrictions and individual infinite gateway exclusions; combine them with these equations before exploring new congruence classes. In particular, attempt a structural forward invariant excluding *all three* Diophantine branches, or produce a genuine blank-origin witness. Existing Machine C gateways, including `(0,2j,4j+10)`, and prior Agent46 depth/power analyses must be credited; the contribution here is the explicit complete first-return stopping locus together with an original-source-connected blank-origin iff.

Reserve `results/` for independently publishable frontier progress. This is an intermediate, rigorous mathematical structural tool and belongs in `im-results/`.
