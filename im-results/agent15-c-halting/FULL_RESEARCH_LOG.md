# Historical full research log

**Unabridged snapshot of the former research README, 6 November 2026.** The original mathematical equations, source links, experiments, failed approaches, uncertainty, and chronological proof reports are preserved. Any “pending” or “current” claims below describe the old writing time. For current synthesis use the [maintained README](README.md).

---

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

## Stronger parity-normalized exact blank stopping gateway

`SectionParam.lean` establishes the fully normalized form of the section halting locus without a recursive seed and with two natural parameters:

```text
secNext(a,k)=none ↔
  (a=0 and k=0)
  or (a=1 and exists m, k+3m+4=2^(2m+3))
  or (exists j,m, a=2j+3 and k+j+3m+5=2^(2m+2)*(j+3)).
```

This follows from parity of powers of two: the earlier exponent n must be even in the `a=1` branch and odd in the general `a≥3` branch. Explicit inductive lower bounds on powers of two prove all the formerly required inequalities `k≥1`, `a<2k`, `k≥4` are automatic under the equations. `BlankParam.lean` composes this with Agent38's `blank_section_positive` to remove the impossible `(0,0)` branch from actual blank-orbit stopping. The result `blank_halts_iff_two_parametric_families` is a complete **two-family** reachability criterion quantifying over all times and both natural parameters, without a finite cutoff.

The complete unchanged-source [CI run 41466181340](https://github.com/FlareZ123/bb6/actions/runs/41466181340) checked all these theorems with standard Lean axioms only.

## A reusable inverse and genuinely infinite, arbitrary-depth reachability barriers

The new module `SectionAffineInverse.lean` proves the exact **all-input iff**

```text
y≥4, y even, (x+y)%4=1
  => (secNext(a,k)=some(x,y) ↔ a=x+y-2 and k=(y-2)/2).
```

Every corresponding output has precisely one incoming section step. This is a strict generalization of Agent3's earlier `section_one_four_exact` for targets `(1,4j)`: it applies to every possible `x,y` in the whole sum-one/even-high region. The proof uses Agent3's kernel-verified full bounce-image theorem to exclude *all* recursive bounce predecessors and classifies every low-counter exception explicitly.

The module `SectionMod8.lean` combines this unique-source principle with Agent38's true blank-section odd-counter sum-mod-four invariant. It proves for **all times** and natural `u,v`:

```text
run secNext time (some(5,1)) != some(4*u+1,8*(v+1)).
```

The unique candidate predecessor has counter residues `(3,3) mod 4`; its sum equals 2 mod 4 with odd right counter, which Agent38 proves impossible from the genuine blank entry. This generalizes Agent6's earlier exclusion of the narrower `(1,8t)` family.

The module `SectionDyadic.lean` establishes `section_right_two_source`: any input producing a section with second coordinate exactly two must itself have second coordinate zero. Agent38's global blank-section positivity therefore proves **no** right-two section is ever reached. Using this as the induction base, `blank_no_three_dyadic` proves for every `n,time,a`:

```text
a%4=3
  => run secNext time (some(5,1)) != some(a,2^(n+2)-2).
```

Its induction works through **arbitrarily long true reverse-affine section chains**, not fixed-depth inverse cones. The unique predecessor transforms `(a,2^(n+3)-2)` to `(a+2^(n+3)-4,2^(n+2)-2)`, preserving first-coordinate residue 3 modulo 4. This general parametric argument covers every natural exponent.

The [original unmodified-source CI run 41467008293](https://github.com/FlareZ123/bb6/actions/runs/41467008293) **SUCCEEDED**. It checks `SectionAffineInverse.lean`, `SectionMod8.lean`, `SectionDyadic.lean`, and all preceding Agent15 modules against source-original Agent3/38/46/21/11/8 Lean definitions. The final `#print axioms` reports standard axioms, no `sorryAx`. Local development temporarily used declaration-only stubs of previously proved Agent3/38 lemmas; the authoritative source CI used **original actual proofs** and replaces those stubs. No imported repository files were modified in this research.

**Limitations:** these powerful blank-reachable exclusions do not yet eliminate the entirety of the two-parameter **halting** locus. The dyadic-minus-two right-counter family does not automatically coincide with a halting family; it demonstrates a reusable all-depth inverse method. Test any stronger downstream halting exclusion against the exact equations, and avoid interpreting the ability to remove many residue classes as a machine-wide nonhalting proof.


## Total exact inverse normalizer, sound executable exclusion, normalized stopping gateway

`ReachAffine.lean` generalizes Agent3's special `(1,4j)` blank-reachability iff to all outputs `(x,y)` with y even ≥4 and (x+y)%4=1: true blank reachability is equivalent to reaching the unique affine predecessor `(x+y-2,(y-2)/2)`. The genuine initial state is handled separately. Source CI [41468452154](https://github.com/FlareZ123/bb6/actions/runs/41468452154) SUCCESS.

`AffineNormalize.lean` is a **total executable** function: whenever k≥4, k even and (a+k)%4=1, recursively replace (a,k) with `(a+k-2,(k-2)/2)`; otherwise return the current pair. Lean proves termination since k strictly decreases. The theorem `reach_iff_normalize` establishes for **every** natural a,k that the original (a,k) is blank-reachable iff the returned normalized pair is. This is a full, arbitrary-depth, no-branch backward preprocessing operation, not finite modular lookahead. Same source CI SUCCESS.

`AffineExclusion.lean` provides an executable filter `affineExcluded(a,k)`: normalize, then detect right counter 0 or 2, or odd right counter with sum ≡2 mod4 and pair distinct from the actual initial state (5,1). Source-certified `affineExcluded_sound` proves `affineExcluded(a,k)=true ⇒ (a,k) is not blank-reachable` using Agent38's original blank modular/positivity theorems and Agent15's right-two exclusion. False means **unknown**. The native evaluation examples `(3,1)→false`, `(7,70)→false`, `(9,16)→true` are checked. Original-source [CI run 41469262925](https://github.com/FlareZ123/bb6/actions/runs/41469262925) SUCCESS.

`NormalizedGateway.lean` states the exact final iff:

```text
CReachBridge.RunHalts iff
    (exists m,k, k+3m+4=2^(2m+3)
       and CReach(affineNormalize(1,k)))
 or (exists j,m,k, k+j+3m+5=2^(2m+2)*(j+3)
       and CReach(affineNormalize(2j+3,k))).
```

This composes `BlankParam.lean` with exact normalization, requiring real blank-orbit reachability of only *normalized* halting gateways. Local Lean checks with standard axiom audit; full source [CI run 41469599614](https://github.com/FlareZ123/bb6/actions/runs/41469599614), check success before independent verification claim.

**Open obstacle:** both normalized infinite parameter families remain globally unresolved. Further progress requires a uniform property of the stopped normal forms, possibly Agent3's full recursive bounce inverse grammar. Do not interpret normalization or sound exclusion as a general reachability decider.


## M8/M16 source-quotient composition and extended executable filter (pending combined CI)

`M8M16Composition.lean` composes Agent 15's exact section semantics with Agent 46's `section_exact` simulation into the original three-counter `BB6CLine.Reach` relation. The theorem `section_reach_embeds` transports every finite Agent 15 section run from the genuine blank-origin start `(5,1)` to an original CLine reachable state `(a,k,0)`. It then imports the source-verified M8 and M16 quotient exclusions through that bridge.

The intended CReach consequences are:
- M8 direct cylinder `(8u+7,8v+4)`;
- M8 affine predecessor cylinder `(8u+7,16v+10)`;
- M8 odd-first-counter halting parameters `(j mod 8,m mod 8)=(2,7)` or `(6,3)`;
- four additional M8 affine-preimage parameter classes `(j mod 16,m mod 16)=(2,5),(6,9),(10,13),(14,1)`;
- M16 even/odd classes `j mod 4=3` and `(m+1) mod 16=j mod 16`;
- M16 `(9,15)` classes `j mod 8=3` and `m mod 16=j mod 16`;
- M16 `(1,7)` classes `j mod 8=7` and `(m+8) mod 16=j mod 16`;
- M16 first-family classes `m mod 16=7 or 14`.

`AffineQuotientExclusion.lean` extends the previous `affineExcluded` filter. The new executable `affineQuotientExcluded(a,k)` first uses the complete affine normalizer, then checks the four source-certified quotient cylinders `(7,4) mod 8`, `(1,2) mod (8,16)`, `(9,15) mod 16`, and `(1,7) mod 16` (excluding the explicit base point `(1,7)`). Its intended theorem proves this filter sound for original blank-origin `CReach`; false remains inconclusive.

The same module derives an exact filtered version of `blank_halts_iff_normalized_families`: either original parametric halting family must have a normalized reachable gateway on which `affineQuotientExcluded` is false. It also derives a first-family exclusion for all eight residues `m mod 16 ∈ {1,4,5,7,9,12,13,14}`. Six are caught by the existing affine arithmetic filter after zero or one normalization step; residues 7 and 14 use the M16 quotient cylinders. The remaining first-family residues are not excluded by this theorem.

**Verification status:** local Lean scratch tests checked the generic section-run induction, the M8 affine arithmetic, the combined filter soundness shape, the filtered-family iff, and the eight-residue first-family proof. These checks used theorem-shaped stubs for imported source declarations and do not establish the repository result.

The first combined source CI run [41490760188](https://github.com/FlareZ123/bb6/actions/runs/41490760188) failed because the M8 and M16 archives both declared `CCert.reps` in the same Lean environment. This was a namespace collision, not a mathematical counterexample. The manual workflow now renames the M16 certificate namespace to `CCert16` during reconstruction, leaving M8 under `CCert`; M16 theorem references use `CCert16`.

The corrected full original-source CI is [41496155633](https://github.com/FlareZ123/bb6/actions/runs/41496155633), head commit `ac4058f89bc8e560f939f4bc4ce7134c85c67bf2`. It was running the M8/M16 source compilation step at the time this section was written. **Do not claim any new theorem above as source-verified until that run succeeds.** If it fails, inspect only the failed job log tail and correct the concrete failure.

These exclusions are infinite residue families within the exact Machine C stopping equations. They do not settle the remaining parameter classes, prove Machine C nonhalting, or determine `BB(6)`. Keep all material here in `im-results/`; it is not yet a standalone publishable solution.
### Exploratory residue scan (finite evidence only)

`residue_filter_explore.py` mirrors the executable filter and samples 16×16 lifts for each `(j mod 16,m mod 16)` pair in the second halting family (256 sampled pairs per residue class). In the sampled window it found 100 residue pairs rejected on every lift, 12 mixed pairs, and 144 pairs never rejected. For the first family it found eight of the sixteen `m mod 16` classes rejected on every sampled lift. This suggests the affine-normalized filter may expose a larger stable residue structure than the source cylinders alone.

These counts are **only finite computational observations**. The script does not establish periodicity or universal exclusion for any of the 100 pairs. A worthwhile next step is to prove a symbolic 2-adic description of the number of affine predecessor steps and then certify any stable classes in Lean. The 14 native-modulus second-family classes listed above remain the only parameter classes currently derived from source-cylinder theorems in this composition.
### 2-adic structure of affine normalization (derived; formalization pending)

For the affine predecessor `T(a,k)=(a+k-2,(k-2)/2)`, direct algebra gives the identities `a'+2k'+4=a+2k` and `k'+2=(k+2)/2`. After n successful steps, `a_n+2k_n+4n=a_0+2k_0` and `k_n+2=(k_0+2)/2^n`.

For odd `a_0`, write `C=a_0+2k_0`. Modulo 4, `a_n+k_n ≡ C-k_n`, so the normalizer's congruence guard is equivalent to `(k_0+2)/2^n ≡ C+1 (mod 4)`, together with `k_n≥4`. In Machine C's second halting family, `a_0=2j+3`, `C mod 4=3` for odd m and 1 for even m; `k_0+2=2^(2m+2)(j+3)-(j+3m+3)`. When `v₂(j+3m+3)<2m+2`, the valuation of `k_0+2` equals that of `j+3m+3`.

This recasts the number of affine predecessor steps as a 2-adic valuation problem and may explain the empirical mod-16 pattern. The one-step identities are exact algebraic derivations; the complete stopping-depth classification, including the `k_n≥4` cutoff and exceptional odd part, has not yet been formalized. This is a candidate direction for future work.
### 2026-11-02 Agent 15 continuation: finite- and arbitrary-depth 2-adic normalizer theorems

New intermediate Lean source modules:

- [AffineHaltOneStep.lean](./AffineHaltOneStep.lean) proves that if a second-family halting parameter `(j,m,k)` satisfies `k+j+3m+5=2^(2m+2)*(j+3)` and at least one of `j%2=1`, `m%2=0`, or `(j+m)%4=1`, its full affine normalizer is an explicit **zero- or one-step** expression. Hence possible multi-step normalization is confined to `j` even, `m` odd, and `(j+m)%4=3`, corresponding to two of sixteen pairs mod 4. This is a universal theorem about the exact normalizer, not a halting decision.
- [AffineParityDepth.lean](./AffineParityDepth.lean) defines `oddDepth k` and proves for all `a%4=3` the exact identities `x+2y+4*oddDepth(k)=a+2k` and `2^oddDepth(k)*(y+2)=k+2`, for `(x,y)=affineNormalize(a,k)`, together with the terminal test. It proves every initial forced-inverse state normalizes to right counter `2` or a multiple of `4`.
- [AffineParityReach.lean](./AffineParityReach.lean) combines these algebraic lemmas with the existing original-blank-origin reachability equivalence and exact theorem excluding right counter two. Every reachable `a%4=3` state with even `k≥2` therefore has normalized right counter divisible by four and an odd `q` satisfying `k+2=2^(oddDepth(k)+1)*(2q+1)`. This makes the power-of-two valuation precise without requiring a separate valuation library.

The three source files were locally checked with Lean 4.36.0-rc2 against the copied exact normalizer definition. The final reachability theorem was checked using explicit source-signature-shaped scratch axioms, so **its source-connected status is still pending**. All three modules have been added to the existing manually dispatched Agent 15 source workflow for genuine unmodified-source checking. Do not conflate local scratch compilation with an original-source certification.

The prior combined CI [41496155633](https://github.com/FlareZ123/bb6/actions/runs/41496155633) failed after successfully compiling M8/M16 quotient chains: an Agent 46 iterator and `Agent8Section.run` were not definitional equals in `M8M16Composition.lean:77`. This concrete source bridge has been corrected by rewriting with the already source-certified `BB6.Agent46.run_eq`; commit `8db9e24dc7a19e1747a1e3cece7b1b650bb40bf0`. Combined source replay [41500523568](https://github.com/FlareZ123/bb6/actions/runs/41500523568) was started at 18:26 UTC, pending at the time of this note. That run predates the three new modules and cannot certify them. No Machine C or BB(6) holdout decision has been obtained.
