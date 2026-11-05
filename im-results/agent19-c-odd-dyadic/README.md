# Machine C: an unbounded alternating dyadic predecessor obstruction

**Agent 19, 2026-11-05.** Original Machine C:
`1RB1LC_1LC1RD_1LA0LB_0RB1RE_1RF0RA_---0RC`.
The authentic blank-section entry is `(5,1)`, with exact source map
`BB6.Agent46.secNext`. The exact value of BB(6), the behavior of
Machine C on its blank start, and the remaining original high stopping
families are all **undecided**.

This directory derives a new all-exponent family of configurations
excluded from the **actual blank-origin section**. The method composes
Agent 24's already source-certified six-residue even-right inverse
equivalence with Agent 3's previously source-certified odd-right image
invariant. It provides an explicit closed form across arbitrarily many
forced inverse edges, and yields a new high stopping-depth family whose
first counter is 3 modulo 8.

## The new all-depth theorem

For every `n,x,w : Nat` satisfying

- `7 ≤ w`, `w % 4 = 3`;
- if `n` is even, `x % 8 = 7`; if `n` is odd, `x % 8 = 3`;

the proposed authentic-source theorem is:

```lean
¬ BB6.Agent3.CReach x (2^(n+2)*w-2)
```

Here `CReach a k` means an **actual finite return time** of the
original Machine C blank-section orbit from `(5,1)`. In particular,
the theorem is independent of any simulation bound and quantifies over
every exponent `n`.

The abstract mathematical result `tower` in
[`OddTowerGeneric.lean`](./OddTowerGeneric.lean) compiled successfully
with local Lean **4.36.0-rc2**. Its axiom audit is exactly
`[propext, Quot.sound]`. The original-source adapter
[`OddTowerSource.lean`](./OddTowerSource.lean) invokes the published
genuine `six_even_right_blank_reach_iff` and
`blank_section_odd_image` theorems, without redefining either source
map or its reachability predicate. An original-source CI audit is
required before describing that adapter as fully verified.

### Proof structure

For the base exponent `n=0`, the candidate `(x,4w−2)`
(`x≡7 mod8`, `w≡3 mod4`) has two forced predecessors:

```text
(x, 4w−2)
  <- (x+4w−4, 2w−2)
  <- (x+6w−8, w−2).
```

The final predecessor has an odd second counter at least five and
coordinate sum `x+7w−10 ≡2 (mod4)`. That contradicts the genuine
blank-section odd-image theorem. For the induction, put
`q=2^n w≥7`. A candidate at exponent `n+1` has even second
counter `8q−2` and the unique predecessor
`(x+8q−4,4q−2)`. Its first coordinate moves by four modulo eight;
the parity-dependent first-counter condition flips exactly as needed.
The induction is valid for **all** `n`.

The deeper `n=1` cylinder is

```text
∀ u v, v≥1 -> ¬ CReach (8u+3) (32v+22).
```

For example, `(59,7894)` has the three mathematically forced
predecessors `(7951,3946)`, `(11895,1972)`, `(13865,985)`.
The terminal coordinate sum is 14850, congruent two modulo four, and
the terminal second coordinate is odd and greater than five. This
example only illustrates the general proof.

The `n=0` slice overlaps the previously certified Agent 15 / Agent
41 `(8u+7,16v+10)` cylinder, whereas the `n=1` slice has
`(a,k)≡(3,22)` modulo `(8,32)`. Explicit prior-art comparison is
still needed for the deeper cylinders, including previous source and
external machine C work.

## A new original high-halting-parameter family

Agent 15's original complete section stopping equation includes
`a=2j+3` with
`k+j+3m+5=2^(2m+2)(j+3)`. The separate
[`OddTowerArithmetic.lean`](./OddTowerArithmetic.lean) proves in local
Lean that, whenever `m≥3`, `j%4=0` and
`(j+3m+3)%32=8`, any such `k` satisfies:

```text
a=8u+3, k=32v+22, v≥1
```

for some natural `u,v`. In particular, these **eight distinct
congruence pairs modulo 32** are excluded from blank-origin halting
once the source connection is certified. The pairs `(j,m)%32` are:
`(0,23)`, `(4,11)`, `(8,31)`, `(12,19)`,
`(16,7)`, `(20,27)`, `(24,15)`, `(28,3)`.
They are disjoint in their `j%4=0` sector from the earlier Agent 24
high exclusions `j%4=1,3` and the imported M8 `j%4=2` family.

[`OddTowerResidual.lean`](./OddTowerResidual.lean) composes the
new obstruction with the existing exact original-source eight-part
halting iff. It preserves all remaining low- and high-family
possibilities. Nothing here establishes that Machine C never halts.

## Evidence and caveats

- Exact standalone Lean command: compile
  `OddTowerGeneric.lean` and `OddTowerArithmetic.lean` using
  Lean 4.36.0-rc2. Both succeeded locally with only
  `[propext, Quot.sound]`, no `sorry`, `admit`, or custom axiom.
- Source-dependent compilation: manually dispatch
  [`agent19-c-odd-dyadic.yml`](../../.github/workflows/agent19-c-odd-dyadic.yml).
  It reconstructs the original source chain and compiles the unchanged
  real Machine C map and all dependencies. Initial runs
  [42093811692](https://github.com/FlareZ123/bb6/actions/runs/42093811692)
  and [42094307213](https://github.com/FlareZ123/bb6/actions/runs/42094307213)
  **failed** at isolated numeral-normalization tactics, with the
  mathematical theorem bodies unaltered; the latest version replaces
  these gaps using independently compiled arithmetic.
- The source-specific final declarations and their final
  `#print axioms` must be checked in a **successful** manual run
  before any blanket source-certification claim.
- No global upper bound on BB(6) follows; the source-specific
  theorem is about one known unresolved machine. Novelty relative to
  published outside certificates has not been independently audited.

## Next direction

The all-exponent theorem suggests systematically reducing the high
halting locus using the 2-adic order of `k+2`, instead of accumulating
unrelated fixed-modulus cylinders. The most important continuation is
to characterize all high-gate parameters whose odd part of `k+2`
falls in this forbidden residue and find a uniform closure for the
remaining residue classes, including branches where the forced
predecessor mechanism stops at section sum residue seven modulo eight.


## 2026-11-05 19:39 UTC: successful full original-source verification and all-exponent extension

**Source-verified.** [Full original-source Lean 4.36.0-rc2 CI run 42095680806](https://github.com/FlareZ123/bb6/actions/runs/42095680806), job 127484971442, completed successfully. It compiled the original Machine C `CLine`, unmodified Agent46 `secNext` and first-return bridge, Agent3 odd-image theorem, Agent24 exact even-right inverse, and all files in this directory. Axioms for final theorem `blank_halts_iff_all_dyadic_sieve` and `blank_no_high_stop_all_depth` are exactly `[propext, Classical.choice, Quot.sound]`; arithmetic theorem `high_all_depth_arithmetic` needs only `[propext, Quot.sound]`. No `sorryAx`. The earlier failed tactic-repair runs are superseded; [CI 42094740809](https://github.com/FlareZ123/bb6/actions/runs/42094740809) separately certified the fixed-modulus case.

The **stronger all-exponent** exact source theorem
[`OddTowerSource.lean`](./OddTowerSource.lean) is:

```text
∀ n j m k : Nat,
  n+4 ≤ 2*m+2
  ∧ (j+3*m+3) % 2^(n+4) = 2^(n+2)
  ∧ (2*j+3) % 8 = (if n%2=0 then 7 else 3)
  ∧ k+j+3*m+5 = 2^(2*m+2)*(j+3)
    ⇒ ¬ BB6.Agent3.CReach (2*j+3) k.
```

The separately compiled original-source arithmetic theorem [`high_all_depth_arithmetic`](./OddTowerGeneralHigh.lean) derives the exactly correct `k=2^(n+2)*w-2`, `7≤w`, `w%4=3` and allows the parameter-independent blank nonreachability theorem to apply. The [`OddTowerResidualAll.lean`](./OddTowerResidualAll.lean) theorem `blank_halts_iff_all_dyadic_sieve` is a **complete iff** for the actual original Machine C halting event after removing this all-exponent high-gate family, while preserving all other high and low possible witnesses. This is a strictly stronger high-gate filter than the fixed `n=1` result, and is the recommended entry point for later work.

The tower's finite base `n=0` is already subsumed by previous published Agent15/41 M8 certificates, but higher `n` sectors provide source-checked root constraints of a different dyadic depth. External prior-art novelty is unknown. The exact blank-run disposition remains unresolved, and **no universal BB(6) upper bound** is established.


## 2026-11-05 20:09 UTC: source-certified unified true-root criterion

The fully assembled [`JointAllRoot.lean`](./JointAllRoot.lean) passed original-source Lean 4.36.0-rc2 [CI run 42100159454](https://github.com/FlareZ123/bb6/actions/runs/42100159454), job 127500534459. Axiom audit of `BB6.Agent19Joint.blank_halts_iff_combined_parametric` is exactly `[propext, Classical.choice, Quot.sound]`. The job checks the untouched Machine C source and the Agent 3 exact time-free root oracle before combining the results; it uses no auxiliary assumptions or unproved shortcuts.

The precise theorem has the following shape, with all allowed predicates *defined in the actual Lean source*:

```text
BB6.CReachBridge.RunHalts ↔
  (∃m, BB6.Agent3.jointLowAllowed m
       ∧ BB6.Agent3.mixedFastRootDecision 1
            (2^(2*m+3)-(3*m+4))=true)
  ∨
  (∃j m, BB6.Agent19Joint.highAllowed j m
       ∧ BB6.Agent3.mixedFastRootDecision (2*j+3)
            (2^(2*m+2)*(j+3)-(j+3*m+5))=true).
```

`highAllowed` is the conjunction of (1) Agent 3's `jointHighRectAllowed` retaining Agent24's earlier two high exclusions, Agent 3's three further root exclusions, and the new Agent3 rectangle; (2) the **all-exponent** Agent19 dyadic complement; and (3) **four independently certified** odd-special high-gateway exclusions. The same theorem also retains Agent 3's seven low stopping-depth exclusions, notably `m%8≠4`, that were not previously present in Agent19's own source residuals. The time existential has vanished entirely. The unbounded machine-parameter existentials `∃m` and `∃j m` remain unsolved, and there is no general Machine C halting or nonhalting decision.

The four odd-special high-gateway exclusions and their exact halting `iff` residual `blank_halts_iff_dyadic_special_lift_sieve` passed a separate source build [CI 42098199948](https://github.com/FlareZ123/bb6/actions/runs/42098199948); final axiom audit ordinary only. They are, under the exact stopping equation `k+j+3*m+5=2^(2*m+2)*(j+3)`:

```text
m≥2, j%8=7, (j+3*m+15)%64=0;
m≥2, j%8=3, (j+3*m+47)%64=0;
m≥3, j%8=5, (j+3*m+27)%128=0;
m≥3, j%8=1, (j+3*m+91)%128=0.
```

The original source blank-return configurations forbidden by these four conditions are respectively

```text
(16u+1, 64v+10),   v≥1;
(16u+9, 64v+42),   u,v≥0;
(16u+13,128v+22),  v≥1;
(16u+5, 128v+86),  u,v≥0.
```

These new intermediate source-root restrictions rely on Agent 38's old odd-special image invariant and Agent 24's exact even-right predecessor equivalence. They are mathematically valid without a simulation cutoff. Whether their novelty extends beyond the shared repository's earlier certified source exclusions, or constitutes a publishable contribution, remains to be independently audited.

### Sum-seven escape under development

[`OddSevenAlgebra.lean`](./OddSevenAlgebra.lean), [`OddSevenInverse.lean`](./OddSevenInverse.lean), [`OddSevenReach.lean`](./OddSevenReach.lean), [`OddSevenHigh.lean`](./OddSevenHigh.lean), [`OddSevenResidual.lean`](./OddSevenResidual.lean) classify one family inside the previously nonunique `(x+y)%8=7` sector. The exact proposed two-parent grammar for target `(32u+1,256v+46)` with `v≥1` is:

```text
secNext(a,k)=some(32u+1,256v+46) ⇒
  (a,k)=(32u+256v+45,128v+22)
  or (a,k)=(8u+64v+9,12u+224v+37).
```

The first parent is in the already forbidden third special cylinder; the second has an odd right counter and forbidden sum-two-mod-four image. Its corresponding high stopper condition is `m≥3, j%16=15, (j+3*m+51)%256=0`. Source audit for the entire new chain and its generalized arbitrary-target inverse is run through [`agent19-c-odd-dyadic.yml`](../../.github/workflows/agent19-c-odd-dyadic.yml). Unlike the unified root theorem above, this sum-seven extension is not to be treated as verified until the final all-files source CI is green and its axiom output excludes `sorryAx`.
