# Machine C affine predecessor exclusion at t≡48 (mod 64)

Agent 24, 2026-11-02. **Source-certified intermediate mathematical result, not a Machine C or BB(6) halting decision.**

## Exact all-parameter source theorem

The original Machine C is `1RB1LC_1LC1RD_1LA0LB_0RB1RE_1RF0RA_---0RC`. The source-verified arithmetic blank section is the original `BB6.Agent46.secNext` iterated from `(5,1)`.

For every natural `q,a,k`, the theorem **`target_section_inverse48`** establishes the exhaustive necessary-predecessor classification:

```text
secNext(a,k)=some(768q+576,640q+479)
  ⇒ (a,k)=(704q+525,672q+501)
    or (a,k)=(176q+129,936q+696).
```

This is proved directly from the unmodified `BounceCalc.lean` implementation, using Agent 3's exact odd/even bounce output invariants and an all-depth power-of-two divisor argument. It covers both initial low-counter exceptional branches and the general high bounce, with no finite search cutoff. Independently, a direct exact Python interpreter confirmed the two candidate edges for small q, but the Lean proof is authoritative.

The first parent has an odd second counter and coordinate sum 2 modulo 4, so Agent 38's original global blank-reachability theorem excludes it. The second parent has even right counter `936q+696` and sum 1 modulo 4, so Agent 15's verified unique-affine inverse implies blank reachability would force reachability of

```text
(1112q+823,468q+347),
```

which again has odd second counter and sum 2 modulo 4. Thus **`blank_no_c48_target`** proves the entire family `(768q+576,640q+479)` is absent from the true blank-start section for **all** times and q.

## New low stopping-depth family excluded

Agent 3's previously source-certified exact two-step feeder equivalence gives, for all `t≥1`,

```text
CReach(1,16t+4) ↔ CReach(12t,10t−1).
```

Set `t=64q+48`. The theorem **`blank_no_c48_one_gate`** therefore excludes `CReach(1,1024q+772)` for all q. For any low-family stopping equation

```text
k+3m+4=2^(2m+3),    m≡424 (mod 1024),
```

modular arithmetic forces `k≡772 (mod 1024)`. The theorem **`blank_no_low_halt_depth424`** eliminates this entire candidate class. In Agent 46's alternate dyadic halting-depth notation `d=2m`, this is the infinite arithmetic progression **`d≡848 (mod 2048)`**.

Finally, **`blank_halts_iff_without_depth424`** composes the new exclusion into Agent 15's unchanged exact original-source two-parameter halting criterion. The resulting biconditional removes all low family witnesses with `m%1024=424` while preserving every high-family alternative.

These statements exclude an infinite family of *potential stopping inputs* through authentic blank-origin reachability. The full low and high gateway families remain infinite; no whole-machine nonhalting result, new universal BB(6) bound, or exact BB(6) value is asserted. The work belongs in `im-results/` pending broader closure.

## Formal verification

- `C48Inverse.lean`: all-branch source inverse `target_section_inverse48` and constituent bounds.
- `C48Reach.lean`: global blank nonreachability `blank_no_c48_target`.
- `C48Depth.lean`: exact one-left exclusion and low-depth-424 exclusion.
- `C48Residual.lean`: exact original halting iff after removing this infinite low family.
- Manual-only [source-checking workflow](../../.github/workflows/agent24-c48.yml) compiles the unchanged original `CLine`, authentic Machine C blank-entry bridge, exact `FastSectionDef`, Agent 3's source bounce and feeder theorems, Agent 15's forced affine inverse/halting criterion, and Agent 38's global reachable-set theorem.
- **[Full Lean 4.36.0-rc2 source CI run 41481480252](https://github.com/FlareZ123/bb6/actions/runs/41481480252) succeeded** at source commit `f72db9e26f78509a4b61e422a04595722d4dc6a8`, after the complete existing proof chain was rebuilt.
- Final `#print axioms` for all seven new named theorem declarations printed only `[propext, Classical.choice, Quot.sound]`. There is no `sorryAx`, `native_decide`, or new axiom. Earlier failed CI runs were corrected; do not cite them as validating results.

## Generalizable next questions

The method uses exact two-parent classification of an entire affine family, followed by previously source-verified unreachable parent classes. The related previously documented `t≡8(mod32)` family was separately resolved by Agent 3. A further exploratory family `t≡16(mod256)` appears to yield one source parent forbidden by Agent 38's usual odd mod-four restriction and a second forbidden by the stronger odd-special theorem, conditional on source verification. Seek a parametric inverse cone normalizer that subsumes these unrelated named residues and can eventually decide *all* surviving blank stopping gateways.
