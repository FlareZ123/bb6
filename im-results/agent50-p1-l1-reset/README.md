# P1 L1 entire one-positive-reset exclusion (Agent 50, 2026-11-03)

**Status: source-certified all-natural theorem.** This is an intermediate proof on the authentic P1 inverse grammar. Neither P1 nonhalting nor BB(6) is decided. No claim of independent external academic novelty.

## Main result

Fix any natural `q ≥ 1` and `u = 7*2^(16*q) - 4*q - 3`. The authenticated n=16q+2 second critical feeder is

```
L1 = (6*u-2, 2*u+5).
```

Consider any exact `BB6.Agent47P1.inverseAt` odd-sector inverse history from this feeder with **exactly one positive-depth** (`t ≥ 1`) edge and any finite number of **depth-zero** (`t=0`) edges before and after it. There is **no** such history ending at the L1 affine halting wall

```
b = 4*m + 64*q + 16,
```

where `m` is the total inverse cost. The prefix and suffix may have arbitrary natural lengths, and q is not restricted to a residue class. The source theorem is `BB6.Agent50L1All.l1_one_reset_cone_no_wall` in [L1AllPrefixBridge.lean](./L1AllPrefixBridge.lean); its hypotheses spell out the complete `UpperTail` prefix, actual source `inverseAt` positive edge, complete `UpperTail` suffix, and original target wall.

**Full original-source verification:** Lean 4.36.0-rc2, manual [GitHub Actions run 41579639239](https://github.com/FlareZ123/bb6/actions/runs/41579639239), `source-certify` job 125731197687, **SUCCESS** on commit `5cb1ef9b067e99ae6a72b579b1ec8e59e5200631`. Unmodified upstream `GParity, GInverse, P1FiniteInverse, MassInverse, OddConeMass, UpperTail, P1TwoRoot, RootWallArithmetic, P1InverseLog` are compiled by the manual-only `.github/workflows/agent1-p1-quarter.yml`, followed by the new files. The final `#print axioms` is exactly `[propext, Classical.choice, Quot.sound]`, no `sorryAx`. A prior failed attempt 41579461391 found a missing namespace import, which was corrected; later successful CI confirms source connectivity.

### Proof architecture

The all-q proof decomposes into reusable kernel-checked components:

1. [L1UpperMass.lean](./L1UpperMass.lean) supplies mass preservation on an arbitrary authentic upper tail.
2. [L1UpperPrefix.lean](./L1UpperPrefix.lean) proves `2^r ≤ 6*q+2` whenever an L1-root upper prefix of length r ends in the positive inverse sector `bp%4=0`.
3. [L1ScaledIdent.lean](./L1ScaledIdent.lean) derives the exact source mass-power identity for a positive inverse after that prefix.
4. [L1AllPrefixArithmetic.lean](./L1AllPrefixArithmetic.lean) proves a fully parameter-uniform 2-adic obstruction, including `65536*q^4 ≤ 2^(16*q)`, odd-residue exponent bound, and source wall conflict.
5. [L1AllPrefixBridge.lean](./L1AllPrefixBridge.lean) applies the arithmetic directly to the original source definitions, without a fabricated inverse relation.

Write `P=2^(16q)`, prefix length r and reset depth t≥1, with `X=2^r`, `Y=2^t`. Define `J=(32q+12+2r)X-(12q+4)` and odd `V=56X-21`. The exact inverse power/mass equations give `XY(c+3)+J=VP` with `0<J<P`. Since V is odd, this forces `r+t≤16q`, so `Z=2^(r+t)` divides J and `Z≤608q²`. With `Q=P/Z`, `H=J/Z`, and `K=32q+12+2r+2t-H`, the source relation becomes `B+K+VQ=56P` for `B=2k+8`, `0<K≤76q`. The fourth-power exponential bound yields `Z*K<P`, hence `K<Q`. The wall suffix forces `B=2^n[4(r+t+1+n)+64q+28]`; dyadic divisibility then gives `2^n≤K≤76q` and `B≤17024q²`. Yet the mass relation implies `B+K≥28P`, contradicting `65536q^4≤P`. These are *all-natural* Lean-proved inequalities, not sample observations.

## Earlier direct-reset subtheorem

The simpler `BB6.Agent50L1OneReset.l1_first_reset_no_wall` in [L1OneResetBridge.lean](./L1OneResetBridge.lean), with pure arithmetic [L1OneResetArithmetic.lean](./L1OneResetArithmetic.lean), already excludes one L1 reset **directly at the feeder** and an arbitrary upper suffix. Original-source [run 41577652633](https://github.com/FlareZ123/bb6/actions/runs/41577652633) succeeded, same standard axiom audit; its statement is a special case of the newer all-prefix theorem.

## Relation to existing P1 research

Existing source-verified Agent 1 [L0OneResetCoverage.lean](../agent1-p1-quarter/L0OneResetCoverage.lean) excludes **all** exactly-one-positive-reset paths with arbitrary upper prefix/suffix from feeder L0. Agent 1's [RootWallArithmetic.lean](../agent1-p1-quarter/RootWallArithmetic.lean) separately excludes upper-only (`zero` positive-reset) paths for both feeders. **Therefore each authentic cone wall history from either feeder necessarily contains at least two positive-depth inversions.** This combined statement is at present a mathematical composition of the named source-proved theorems; a standalone Lean source theorem about counted histories may be added.

Agent 9's [DichotomyOriginal.lean](../agent9-p1-logcost/DichotomyOriginal.lean) independently proves a necessary exponential inverse-cost OR affine-wall condition for a genuinely reachable even-right exit. The present result tightens the *affine-wall* branch without excluding histories with two or more positive resets, high-cost inverse cones, exceptional `c=1` exits, or the separate n≡14(mod16) critical family. Source `OddCone` includes synthetic ancestors; inverse feasibility is never equated to blank-origin reachability. These remain the essential gaps toward deciding P1 and BB(6).

## Reproduction and next direction

Use the repository's existing **manual** `.github/workflows/agent1-p1-quarter.yml` workflow at the pinned success revision; no per-commit CI is configured. The full theorem is source-connected and standard-axiom-only. The most promising follow-up is a parameter-uniform obstruction to a **second positive-depth** reset, or a precise authentic synthetic witness invalidating such an obstruction. Preserve finite probes as experiments unless transformed into uniform proof.
