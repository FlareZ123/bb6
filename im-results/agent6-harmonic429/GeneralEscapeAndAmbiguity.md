# Paired halting and nonhalting families for every first counter of BB429

**Agent 6, 2026-11-06, research intermediate.** This establishes a uniform all-parameter property of the source-transcribed twelve-branch accelerated machine #429. It does **not** decide whether its genuine blank-origin trajectory halts, and it does not determine BB(6).

## Source-certified result

The unchanged accelerated transition source [`BB429Rank.lean`](../agent5-429-rank/BB429Rank.lean), the pre-existing [`EscapeRay.lean`](EscapeRay.lean) and the new [`GeneralEscape.lean`](GeneralEscape.lean) and [`HaltVsEscape.lean`](HaltVsEscape.lean) were jointly compiled in **successful [manual source CI 42136119528](https://github.com/FlareZ123/bb6/actions/runs/42136119528)**. The preceding independent [CI 42135906667](https://github.com/FlareZ123/bb6/actions/runs/42135906667) compiled the all-counter escape module by itself. The CI workflow is [manual-only](../../.github/workflows/agent6-429-general-escape.yml), on Lean 4.36.0-rc2. The final theorem `BB429HaltVsEscape.incompatible_pair` reports standard axioms `[propext, Quot.sound]`, with no `sorryAx`, copied source definition, or premise asserting the desired nonhalting conclusion.

Let `R_u(0)=u`, `R_u(k+1)=2R_u(k)+3`, and `D_u(0)=0`, `D_u(k+1)=D_u(k)+R_u(k+1)`. Define the two natural second counters

```text
E(u,k) = D_u(k)+R_u(k)+8
H(u,k) = D_u(k)+(2R_u(k)-1).
```

**Verified theorem (full accelerated map).** For every `u≥0`, every `k≥3`, and every natural accelerated time `n`:

```text
BB429.run k (u,E(u,k)) = some (R_u(k),R_u(k)+8)
BB429.run n (u,E(u,k)) != none
BB429.run k (u,H(u,k)) = some (R_u(k),2R_u(k)-1)
BB429.run (k+1) (u,H(u,k)) = none
E(u,k) < H(u,k)
H(u,k)-E(u,k) = R_u(k)-9.
```

Both starts follow exactly `k` first-branch transitions (the `generic_ray_run` certificate). The nonhalting endpoint lies on Agent6's previously certified invariant four-step ray, while the halting endpoint satisfies the exact source halting line. The first counter at the shared depth is `R_u(k)=(u+3)2^k-3`. The escape seeds grow strictly with `k`, giving infinitely many distinct synthetic nonhalting starts **for every fixed exact first counter `u`**. The two older [`EscapeRoot.lean`](EscapeRoot.lean) families correspond to special choices `u=0` and `u=11`.

The Lean theorems express the exponential formulas without ambiguous natural subtraction:

```text
E(u,k)+2u+3k+1 = 3(u+3)2^k
H(u,k)+2u+3k+13 = 4(u+3)2^k.
```

## New two-sided modular-density corollary (paper combination)

Agent6's independently established [coprime-modulus surjectivity argument](../agent6-429-coprime-moduli/README.md) proves, by strong induction on `m`, that for any fixed integer `A≥0`, any `m≥1` coprime to three, any target residue `r`, and any cutoff `L`, some `k≥L` satisfies `A·2^k−3k≡r (mod m)`. Its mathematical mechanism has strong earlier precedent in Zhi-Wei Sun's 2014 modular-surjectivity theorem and has **not** been formalized in Lean at all moduli.

Apply that exact arithmetic lemma twice, with `A=3(u+3)` for `E`, and `A=4(u+3)` for `H`. For **every** fixed exact first counter `u`, every modulus `m` with `gcd(m,3)=1`, every second-counter residue `r` and every lower bound on `k`, there are:

1. A synthetically nonhalting state `(u,E(u,k_E))` with `E(u,k_E)≡r(mod m)`, `k_E` arbitrarily large.
2. A synthetically halting state `(u,H(u,k_H))` with `H(u,k_H)≡r(mod m)`, `k_H` arbitrarily large.

This is **two-sided arithmetic-density of opposite outcomes** in every coprime-to-three congruence cylinder even with the exact first counter fixed. It rules out classifying the complete source accelerator's global halt/nonhalt behavior from the exact first counter and the second counter modulo any such fixed `m`, regardless of the amount of finite data behind that classification. The logical application is a paper derivation from the existing all-moduli arithmetic lemma and newly source-certified trajectory families; **it is not a Lean kernel-certified theorem at arbitrary `m`**. It does not rule out blank-root-only, history-sensitive, or nonperiodic proofs.

## Relation to BB(6) and outstanding work

The real blank-origin accelerated start is exactly `(0,0)`. The constructed starts have generally very large second counters and have **no proved path from that blank seed**. No source theorem above asserts any blank-origin halt, blank-origin entry into the escape ray, or universal upper bound on all six-state machines.

The new source theorem generalizes Agent6's earlier two fixed-first-counter synthetic nonhalting rays and pairs them explicitly with the source halting family. The two-sided modular ambiguity goes beyond the previously recorded one-sided synthetic-halting saturation. Independent external novelty review remains necessary before promoting this intermediate to `results/`.

A separate exact 10-billion-macro-step C++ transcription from genuine blank `(0,0)` found no halt and no direct entry into the two certified near-diagonal escape-ray phases. This is finite experimental evidence only, omitted from formal claims and not a complete reachability test. Its source is currently local scratch and is not presented as a proof.

**Next genuine-root question:** Find a reachable all-time invariant that includes the blank seed and controls its post-reset ancestry, or prove the true blank orbit enters a certified nonhalting region. Two-sided synthetic saturation makes unconditioned fixed-modulus quotients especially unpromising for this machine.
