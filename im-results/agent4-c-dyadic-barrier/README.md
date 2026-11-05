# Machine C: dyadic immediate-halting saturation

**Agent 4, 2026-11-05. Intermediate theorem; BB(6) and Machine C remain undecided.**

The source-connected Machine C section map `BB6.Agent46.secNext` has a previously proved complete stopping equation in `im-results/agent1-c-unified-gateway/UnifiedGateway.lean`. For any odd first counter `a=2u+1` and any naturals `e,w`, the new Lean theorem `BB6CDyadicBarrier.every_odd_dyadic_class_has_immediate_halt` constructs a right counter `K` such that

```lean
K % (2^e) = w % (2^e) ∧
BB6.Agent46.secNext (2*u+1,K) = none
```

In particular, for **every** power-of-two modulus, there is a synthetic source input `(5,K)` in the same two-counter residue class as the authentic blank section seed `(5,1)` that halts **immediately**. This is a theorem about artificial inputs; it does not assert that the real blank orbit reaches them.

## Construction

Let `G(0)=0`, `G(e+1)=4G(e)+1`, `C=u+w+4`, `m=C*G(e)+(C+e+1)*4^e`, and `K=4^(m+1)*(u+2)-(u+3m+4)`. The proof establishes

```text
3*G(e)+1 = 4^e
3*m+C = (4*C+3e+3)*4^e
K+u+3*m+4 = 4^(m+1)*(u+2)
```

together with `m≥C+e+1`, `K≥w`, and `2^e ∣ K-w`. The last equation is the imported, pre-existing exact Machine C source stopping criterion for odd first counters.

## Implications and provenance

A pure dyadic two-counter residue abstraction cannot refute Machine C halting: its initial abstract state already admits an immediately stopping synthetic representative. Root-conditioned modular exclusions remain useful, and abstractions carrying other information can escape this limitation.

Lean source: [CDyadicImmediateHalts.lean](CDyadicImmediateHalts.lean). Its proof compiled locally in Lean 4.36.0-rc2 against a temporary declaration-only interface for the previously source-checked `source_section_halts_iff_one_equation`; **source-native CI remains separately required**. The interface was not committed, and this dossier does not claim a new blank-origin halt or a novel BB(6) bound. Keep intermediate pending independent mathematical novelty and source audit.


## Extension: mod 3 does not remove the blank-cylinder obstruction

The supplementary [CDyadicMod6.lean](CDyadicMod6.lean) proves for **all** `e:Nat` the stronger statement
```lean
∃ K : Nat, K % (3*(2^e)) = 1 % (3*(2^e)) ∧
  BB6.Agent46.secNext (5,K) = none
```
using the previous `2^e` construction, the existing *source-verified* `source_positive_stopping_right_mod3` theorem (`K%3=1` for any positive-left source stop), and elementary coprimality `Nat.Coprime 3 (2^e)`. Thus adjoining a *single factor of three* to an arbitrarily fine dyadic residue quotient still cannot decide actual blank-root nonhalting by classifying its initial cylinder. The claim is specifically for `3*2^e`; higher powers of 3 or arbitrary moduli are **not** covered by this theorem. The real blank origin is not asserted to halt.

Both modules have been checked locally against precisely matching, pre-existing theorem signatures, without `sorryAx`. A manual source CI run of both modules and the complete unchanged C source import chain is queued as [41970586436](https://github.com/FlareZ123/bb6/actions/runs/41970586436); an earlier run checking only the first module is [41970212167](https://github.com/FlareZ123/bb6/actions/runs/41970212167). Update this dossier if source CI succeeds or finds a mismatch.


## 2026-11-05 05:20 UTC: general all-positive-modulus paper theorem

The strongest new method obstruction is now [AllFiniteModuliBarrier.md](AllFiniteModuliBarrier.md), a complete elementary **paper proof for every positive finite modulus M**, including arbitrary prime factors ≥5. It asserts

```text
∀M≥1, ∃K≥1: K≡1 (modM) and secNext(5,K)=none.
```

The proof starts with the previous all-`2^e 3^j` CRT congruence and adjoins higher prime powers in **ascending prime order**. To adjoin `p^a` to `M0=2^eB` where all prime factors of `B` are below p, use the period `R=M0·φ(B)·ord_p(4)`, which is **coprime to p**. If `p^k | F(n)` for `F(n)=4^n−3n−1`, the shifts `n ↦ n+Rp^k z` preserve all earlier roots and yield `F(n+Rp^k z)≡F(n)−3Rp^k z (modp^(k+1))`. Choose z modp using the unit `3R`, then iterate. This is fully parameter-uniform mathematical reasoning and removes any restriction to particular prime factors. Full details and evidence limits are in the linked proof.

The executable independent [verify_all_moduli.py](verify_all_moduli.py) constructs exact modular witnesses for **1,302** deterministic finite cases (every `1≤M≤1000`, plus 300 seed-fixed random moduli below 10 million and two large products). It passed locally with Python, including independent checks after each lifting stage. These checks do not constitute a proof, and a uniformly quantified Lean proof for arbitrary M remains **unwritten**. The previously proved source stopping iff is authentically verified; the new full prime-lifting derivation uses standard number theory rather than a Lean kernel check.

A pure two-counter congruence quotient with any fixed positive modulus is thus intrinsically contaminated with synthetic immediate halts at the blank section's initial residue class. This does not say a **real blank run** halts. Other information such as exact inverse ancestry, source constraints, and nonperiodic invariants may still distinguish authentic reachability.


## 2026-11-05 05:23 UTC: complete original-source CI SUCCESS for both narrow Lean modules

**Authoritative source audit:** manual [GitHub Actions run 41970586436](https://github.com/FlareZ123/bb6/actions/runs/41970586436), job `127057644214`, head SHA `48c998da006f430e706e79f7d9c5a5a236621b49`, **SUCCESS** at 05:22:37 UTC. Lean 4.36.0-rc2 compiled the 26 unchanged Machine C source and gateway dependencies and the new `CDyadicImmediateHalts.lean` and `CDyadicMod6.lean` from the repository. The printed Lean kernel axiom lists for `every_odd_dyadic_class_has_immediate_halt`, `blank_class_has_synthetic_halt`, and `blank_mod_three_times_power_two_synthetic_stop` are **exactly** `[propext, Classical.choice, Quot.sound]` with no `sorryAx`. The earlier local theorem-signature-stub checks are superseded for these three theorems.

This authentication concerns the actual, unchanged **repository Machine C section source**. It does **not** kernel-check the later, stronger mathematical all-positive-modulus prime-lifting argument in [AllFiniteModuliBarrier.md](AllFiniteModuliBarrier.md). The all-M theorem is a fully worked **paper proof** with a separate 1,302-case reproducible exact-integer witness check. Do not conflate the two evidence grades.

The redundant earlier first-module-only queued CI run `41970212167` was cancelled before starting to conserve resources; the combined source run is the definitive evidence.
