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


## 2026-11-05 19:39 UTC: uniform odd-first extension

The newer [AllOddFirstModuliBarrier.md](AllOddFirstModuliBarrier.md) strengthens the paper-level all-positive-modulus result from the fixed blank-section first coordinate `a=5` to **every odd first coordinate `a=2u+1`**, all `u≥0`. For every positive modulus `M`, a synthetic input `(2u+1,K)` satisfies `K≡1 (mod M)` and `secNext(2u+1,K)=none`. The stopping formula uses `F_u(n)=(u+2)(4^n−1)−3n`, with `K=F_u(n)+1`.

Two independent elementary proofs are recorded: the original ascending-prime CRT/lifting construction and a shorter **Euler-totient-period strong induction on `q=M/(2^e3^j)`**. The latter requires no prime-power lifting and is the preferred basis for any future formalization. The companion modular algorithms [verify_odd_left_all_moduli.py](verify_odd_left_all_moduli.py) and [verify_odd_left_totient.py](verify_odd_left_totient.py) independently confirm 10,702 and 43,000 parameter pairs, respectively; 168 small examples also execute the exact source bounce branches to `none`. These are reproducible finite checks and an explanatory paper proof, **not** new unrestricted Lean kernel theorems. The previously source-verified stopping equation remains the exact formal-machine dependency. This result does not decide actual blank reachability or BB(6), and stays in `im-results/`.


## 2026-11-05 20:02 UTC: all-time source-certified 115-mod-128 no-reachability

The new Lean theorem [One115Source.lean](One115Source.lean) establishes, for every natural `r`, **`¬ BB6.Agent3.CReach 1 (128*r+115)`**, where `CReach` is reachability from the genuine blank Machine C zero-high section `(5,1)` at any finite section-return time. This uniform theorem uses three **exact source-certified predecessor iff lemmas**, with a final source-image impossibility:
```text
(1,128r+115)
   <- (64r+56,96r+84)
   <- (160r+138,48r+41)
   <- (104r+87,76r+63)
   <- no section source (odd-right>=5, sum=2 mod4)
```
The arrows are the complete source-predecessor fibers in these numeric regions. The final state cannot occur after a successful source section step; it is also different from the actual initial section point.

**Full unchanged-repository-source Lean 4.36.0-rc2 CI [run 42099366325](https://github.com/FlareZ123/bb6/actions/runs/42099366325) PASSED** on commit `e85cf41f7853d7fc6229a2a2d673f36766d73560`. The manual workflow [agent4-c-one115.yml](../../.github/workflows/agent4-c-one115.yml) compiles unchanged original Machine C `CLine`, `FastSectionDef`, `BounceCalc`, Agent3 exact inverse sources and Agent24 even-right inference, then the new theorem. Its `#print axioms` excludes `sorryAx` and reports only `[propext, Classical.choice, Quot.sound]`. Two earlier workflow attempts failed on ordinary dependency/proof-script issues; they do not affect the successful verification.

**Novelty boundary:** Agent46 previously Lean-certified `¬BB6CLine.Reach(1,k,0)` for `k%384=115`, equivalent to low-halting depth `m%128=3`. Our `k%128=115` family includes `k%384=115,243,371` and is all-time in the two-counter section semantics. For genuine low stopping inputs `k+3m+4=2^(2m+3)` with `m>=2`, this new cylinder intersects only the **already excluded** parameter class `m%128=3`. It therefore strengthens the structural reachability statement without yielding an additional unresolved low-gateway class. No complete Machine C halt decision or BB(6) improvement follows.
