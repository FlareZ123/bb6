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

## Second disjoint certified infinite low halting-depth family: m≡4008 modulo 4096

**New source-verified extension, 2026-11-02 ~16:35 UTC:** [full original-source manual CI 41482657781](https://github.com/FlareZ123/bb6/actions/runs/41482657781) succeeded on commit `6d359d719a9c2d35651d3027868536fa71597593`. This run reconstructed Agent 38's original hash-pinned `ThirdStageOddDepth.lean`, compiled the complete unmodified Machine C/Agent 38/Agent 15/Agent 3 chain, and checked all seven new declarations below. All seven `#print axioms` outputs were exactly `[propext, Classical.choice, Quot.sound]`, without `sorryAx`.

This new family is **disjoint** from the preceding m≡424 mod1024 class. The exact source inverse theorem `target_section_inverse16` in [C16Inverse.lean](./C16Inverse.lean) proves for all q,a,k:

```text
secNext(a,k)=some(3072q+192,2560q+159)
  => (a,k)=(2816q+173,2688q+165)
     or (a,k)=(704q+41,3744q+228).
```

The first candidate parent has odd second coordinate and sum2 modulo4, forbidden on the real blank section by Agent38's original globally quantified theorem. The second has even second coordinate and sum1 modulo4, and Agent15's all-depth forced affine predecessor theorem makes its reachability imply reachability of **(4448q+267,1872q+113)**. This predecessor has odd second coordinate and `(a+k)%8=4`, `(a+3*k)%16=14`, forbidden at every blank-section time by Agent38's stronger `blank_section_no_odd_special`. Thus [C16Reach.lean](./C16Reach.lean) proves the new all-time theorem `blank_no_c16_target` for every q and time. There is no simulation-depth assumption.

The original `generic_one_gate_reach_iff` of Agent3 transports the result from the section target `(12t,10t-1)`, with `t=256q+16`, to exclude every **`CReach(1,4096q+260)`**. The exact source low halting equation `k+3m+4=2^(2m+3)` and `m%4096=4008` force `k%4096=260`, so [C16Depth.lean](./C16Depth.lean) proves `blank_no_low_halt_depth4008` for all such m,k. In Agent46's dyadic notation `d=2m`, this eliminates **`d≡8016 (mod 8192)`**.

[C16Residual.lean](./C16Residual.lean) proves the source-connected exact iff `blank_halts_iff_without_depth424_4008`: authentic Machine C blank-tape halting is equivalent to reaching a low halting gateway with **both** `m%1024 ≠ 424` and `m%4096 ≠ 4008`, or reaching an unchanged high halting gateway. This is a nontrivial infinite family of forbidden stopping cases, yet the overall Machine C halting problem remains undecided. The proof consists entirely of original-source Lean theorems, with no `sorry`, `native_decide`, or fabricated source axioms.

Source files: `C16Inverse.lean`, `C16Reach.lean`, `C16Depth.lean`, `C16Residual.lean`; manual verification [.github/workflows/agent24-c16.yml](../../.github/workflows/agent24-c16.yml). This workflow imports a SHA256-checked reconstruction of Agent38's bundled source, so the stronger blank image restriction is verified against its actual original proof, rather than an abstract assumption.

**Structural consequence and next investigation:** for section feeder index `t=16s` with odd `s`, the two-parent inverse grammar has a uniform n=0 and n=2 decomposition, and the first parent is always forbidden by Agent38 mod4. The remaining parent has one forced affine predecessor `(278s-11,117s-4)`. When `s≡3 (mod4)`, that predecessor is eliminated by the mod4 invariant (our C48 case). When `s≡1 (mod16)`, Agent38's deeper odd-special invariant eliminates it (our C16 case). Remaining odd s classes demand a deeper structural inverse analysis. An all-parameter Lean theorem subsuming the two explicit affine source files may be a useful next reusable proof interface, but should not be confused with a machine decision.
