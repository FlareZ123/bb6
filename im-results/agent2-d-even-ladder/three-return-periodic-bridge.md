# Stronger D regular-to-E bridge: **three** sections suffice for every ladder depth

**Agent 2, 2026-11-03.** Intermediate source-derived theorem (full original-source Lean composition pending), with exact independent raw-Turing-machine witnesses. This strengthens the [previous all-even four-section construction](README.md) by eliminating its fourth preliminary return. It combines with Agent 35's prior odd-depth theorem to give a **uniform three-section prefix** for every positive ladder depth. No authentic blank-root reachability or BB(6) decision follows.

## Existing authentic source ingredients

Original six-state two-symbol D-start machine:
`1RB0RE_1LC0RA_1LA1LD_1LC1LF_0LC0LB_1LE---`.
Notation: `I_n(s)` is state F scanning 0, all tape left of the head zero, with right physical tape `1^n s 0^∞`. `P_j=(01)^j`. The synthetic regular E entry `X(k,q)=I_(3k+4)(P_q1)` is in Agent37's proposed regular class.

Agent31's [third-return-classification](../agent31-d-exceptional/third-return-classification.md) gives, for every `v>=0,q>=3`, its t≡2 mod3 branch (`k=9v+7`), the **third** designated F/0 raw endpoint

```text
X(9v+7,q) -> I_(512v+434)(01 0 1^(2q-3) 0 1^6).
```

Here `01 0` is `P_1 0`. The primitive-step time for the third branch is `12K²+49K+40` with `K=64v+53`; the previous two source endpoints and their elapsed times are in Agent31's tables. The three identities are compositions of previously verified original-source macro theorems, but the combined statement is still awaiting an authentic whole-source Lean import/strict first-return audit.

Agent2's [original-source power ladder](../agent2-cryptid-continuity/ETripleLadderIndex.lean) states for every depth `m`, multiplier `U>=1`, alternating count `p` and suffix `ys`:

```text
I_(3^(m+1)*U+1)(P_p 0 1^(3m+3) 0 ys)
   ->[totalCost(m,U-1,p) primitive raw steps]
I_(3*8^m*U+1)(P_(p+2m) 0 1^3 0 ys).
```

The source-connected [strict E ladder](../agent2-cryptid-continuity/ETripleLadderSource.lean) additionally identifies every intervening genuine physical F/0 return at its explicit recursive time. Locally checked with standard Lean4.36 axioms; exact committed-byte original-source CI was still pending when this note was written.

## New even-depth theorem with only three preliminary sections

**Theorem (arithmetic and conditional machine-macro composition).** For every `r>=0`, put `m=2r`, `q=3r+3`. Define the positive odd integer `U_r` in `1..511` by

```text
U_0 = 315,
U_(r+1) = the least positive residue of 57*U_r modulo 512,
v_r = (3^(2r+1)*U_r - 433)/512,
k_r = 9*v_r + 7.
```

Then `v_r` is a nonnegative **integer** and the third D raw-source section endpoint is exactly the E-ladder input

```text
X(k_r,q)
  ->[three prior source-macro endpoints]
I_(3^(m+1)*U_r+1)(P_1 0 1^(3m+3) 0 1^6).
```

It then reaches, after `m` additional exact E source transformations,

```text
I_(3*8^m*U_r+1)(P_(2m+1) 0 1^3 0 1^6).
```

For m=0 the E stage is vacuous; m=2,4,... are the nontrivial even-depth cases.

**Complete number-theoretic proof.** The residue 57 is invertible modulo 512 because `9*57=513 ≡1(mod512)`. Start with `3*315=945 ≡433(mod512)`. By induction,

`3^(2r+1) U_r ≡433 (mod512)`.

Indeed the induction step multiplies the previous expression by `9*57≡1(mod512)`. Therefore `v_r` above is an integer. All `U_r` are positive odd residues at most 511. For r=0,1,2, the resulting `v_r` are `1,1,217`, respectively; for r>=3, `3^(2r+1)>=2187>433`, so the numerator defining v is positive. Thus `v_r>=0` for every r.

Set `q=3r+3`. Since `m=2r`, `2q-3=3m+3`. Moreover,
`512v_r+434 = 3^(m+1) U_r+1`, from the definition of v. Substituting both identities into Agent31's quantified *third*-endpoint template gives the claimed exact physical E-ladder input with `p=1` and `ys=1^6`. Applying the already established all-parameter E ladder source theorem gives the stated final endpoint and exact elapsed source primitive-step count. QED, subject only to the existing original-macro source/physical-padding contracts.

**Bounded periodic multiplier.** Repeated modular squaring gives `57^32 ≡257 (mod512)` and `57^64 ≡1 (mod512)`. Since `57^32 !=1 (mod512)`, 57 has exact multiplicative order 64. As U_0=315 is coprime with 512, `U_(r+64)=U_r` and its least positive period is 64. In particular the ladder multiplier is bounded by 511 and repeats as depth m increases by 128. The regular input indices nevertheless grow exponentially through the factor `3^(m+1)`.

**Exact E-ladder elapsed time:** the finite sum of original-source stage costs simplifies to

```text
108*U_r^2*(64^m-9^m)/55
 +15*U_r*(8^m-3^m)
 +6*m^2+21*m.
```

The stage-wise recursive total is original-source Lean verified; the rational closed expression has an independent arithmetic derivation in [Agent2's verification note](../agent2-cryptid-continuity/verification-note.md), and this specific closed expression has not yet been separately Lean imported.

### Comparison with the previously established odd-depth case

Agent35's [DETripleRegularBridge](../agent35-d-regular-certificate/README.md) handles `m=2r+1`, choosing `u=(3^(m+1)-1)/2`, `k=9u+4`, `q=(3m+9)/2`. After three source endpoints its unary length is `512u+257 = 3^(m+1)*256+1`, with suffix `P_4 0 1^(3m+3)0 1^6`. Thus it enters the same m-fold E ladder with multiplier 256 and initial pair count 4.

The odd and new even cases together yield **a three-macro-prefix input construction for every positive natural depth m**, with exactly m subsequent *source-verified strict* E-ladder returns. The first three source endpoints have not yet been proved universally free of earlier physical F/0 visits in one combined original-source theorem. No actual blank-run reachable invariant is supplied.

## Reproduction, including full primitive tape and head

The independent raw-machine simulator (literal 11 defined rules) generated these genuine **first** physical F/0 return times for `r=1, m=2, U=35, v=1, k=16, q=6`:

| Return index | Primitive time | Unary length | Canonical right suffix |
|---:|---:|---:|---|
| 1 | 3936 | 133 | `0 1^12 0 1^6` |
| 2 | 28289 | 353 | `P_2 0 1^9 0 1^6` |
| 3 | 198330 | 946 | `P_1 0 1^9 0 1^6` |
| 4 | 1396932 | 2521 | `P_3 0 1^6 0 1^6` |
| 5 | 9885171 | 6721 | `P_5 0 111 0 1^6` |

Each record was checked for zero scanned bit, F state, and an entirely blank left half-tape. The E portion took `9885171-198330=9686841` primitive steps; the closed cost formula at `m=2,U=35,p=1` gives exactly **9,686,841**. A deterministic single-file CommonJS test under this directory is being extended with this fixture. The experiment establishes only the displayed **finite instance**. The universal assertion follows from source-derived lemmas and number-theoretic induction.

Small constructive rows:

| m | q | U_r | v_r | k_r | Third unary length |
|---:|---:|---:|---:|---:|---:|
| 0 | 3 | 315 | 1 | 16 | 946 |
| 2 | 6 | 35 | 1 | 16 | 946 |
| 4 | 9 | 459 | 217 | 1960 | 111538 |
| 6 | 12 | 51 | 217 | 1960 | 111538 |
| 8 | 15 | 347 | 13339 | 120058 | 6830002 |
| 10 | 18 | 323 | 111754 | 1005793 | 57218482 |

Arithmetic was independently crosschecked via base-3 digit lifting on 41 even depths, in addition to the periodic formula.

## Scope and next proof edge

The input machines are *synthetic* F/0 configurations, not certified destinations of the original blank-tape root. The three preliminary checkpoints are source-derived from individual original source theorems; an imported monolithic primitive-run and physical-observation proof would strengthen this to a single formally certified theorem. The E stage already has an original-source local Lean strict first-return proof, pending exact committed-byte CI for some modules. Source provenance, source/CI status and external novelty must be re-assessed before academic promotion.

This structure shows how the current regular-language synthesis can require an **unbounded number of exceptional E returns** when extended across all synthetic regular entries. It establishes no obstruction to richer global invariant grammars or any BB(6) upper bound.

## Original local Lean 4.36.0-rc2 kernel certificate for parameter arithmetic

[**DEvenBridge.lean**](DEvenBridge.lean) now formally proves all-even parameter existence **for every natural r**, the positive bounded odd multiplier, the exact residue congruence, period 64, and the non-repetition of its initial value for every positive index below 64. Source theorem names: `even_bridge_parameters`, `multiplier_period64`, `multiplier_first_repeat_64`.

Reconstructed the user's pinned 4.36.0-rc2 archive locally, extracted its nested `lean-4.36.0-rc2-linux.tar.zst`, and compiled the **exact committed Lean source blob** successfully. The file's Git blob SHA is `c149efd88c0a7538c037ef56dd3941a3b5177e80`, independently equal to GitHub's returned blob SHA, and local SHA-256 is `33db47bcf6c76afa6087fb15f677ba3934db6d5fbf500ec17ea1a3a2a254e459`.

Axiom audit printed:

```text
'BB6.DPeriodicEvenBridge.even_bridge_parameters' depends on axioms: [propext, Quot.sound]
'BB6.DPeriodicEvenBridge.multiplier_period64' depends on axioms: [propext]
'BB6.DPeriodicEvenBridge.multiplier_first_repeat_64' does not depend on any axioms
```

This is **kernel-verified parameter arithmetic**, independent of any assumed D-machine macro theorem. The original-machine third-endpoint composition and the physical-padding source bridge remain separate proof obligations. It does not certify that any synthetic input is blank-reachable.

