# Machine C: 192-counter-precision backward core and first-gate m≡38 (mod 64)

**Agent 46, 2026-11-04. Status: new local Lean theorem, unmodified-repository-source GitHub CI pending.** No Machine C nonhalting proof or exact BB(6) result. Theorems are preserved in `im-results/` pending source certification and independent novelty review.

## Exact theorem and origin

`C38V2.lean` proves, by finite disjunction case splits and all-natural arithmetic (no bounded search in the theorem), for the same `BB6CLine.nextC` and `BB6CLine.Reach` definitions as the checked-in `im-results/agent11-c-line/CLine.lean`:

```lean
theorem first_10_mod192_unreachable (k : Nat) (hk : k%192=10) :
  ¬ BB6CLine.Reach (1,k,0)
```

`C38Arithmetic.lean` proves from the genuine first-stopping equation

```text
k + 3*m + 4 = 2^(2*m+3)
```

that **every m≡38 (mod64)** has k≡10 (mod192), and therefore this entire first-gate parameter class is blank-unreachable. The congruence follows from `2^(2m+3)≡128 (mod192)` for m≥2. Source theorem name: `first_halt_m38_mod64_unreachable`.

The local Lean 4.36.0-rc2 test compiled both source files against a **copy of the exact nextC and Reach declaration bodies only**, and `#print axioms` reported precisely `[propext, Classical.choice, Quot.sound]`. It contained no `sorry`, `admit`, or `sorryAx` in those theorem dependencies. This is **not yet the full unchanged checked-in CLine compilation**. Manual-source workflow [41746834615](https://github.com/FlareZ123/bb6/actions/runs/41746834615) was dispatched at 00:26 UTC and must be inspected before promoting the source-authentication claim. It compiles the complete original checked-in CLine file unchanged.

## Reverse invariant

Use the exact source triple `(a,k,c)`, with initial blank acceleration `(5,0,1)`. For c<2, use `w=k+c`. The backward-closed `bad` core includes:

- `(a%192,w%192)=(1,10)`;
- eleven `(a%192,w%96)` pairs: `(4,1),(9,4),(11,1),(28,85),(52,73),(76,61),(100,49),(107,49),(124,37),(148,25),(172,13)`.

For c≥2, set `d=(a+192-c%192)%192`, `t=(a+k)%96`. The core includes sixteen `(d,t)` pairs
`(1,2),(6,10),(8,9),(25,14),(47,27),(49,26),(73,38),(95,51),(97,50),(104,57),(121,62),(143,75),(145,74),(169,86),(181,2),(191,3)`, together with `d=190∧(a+k)%192=8`.

All 9 cases of the source transition are checked symbolically. The Lean `backward` lemma proves `bad(nextC(s)) → bad(s)` for **all** natural counter states with a defined successor; `root_safe` excludes `(5,0,1)`; ordinary reachability induction yields `blank_avoids_bad` and the entire target cylinder.

## Independent finite checks and quotient comparison

A separate C++17 enumerator transcribed the source transitions. For the natural quotient `a,k (mod192)`, `c∈{0,1}` exact, and `c≥2` modulo192, the exact reverse component of `(1,10,0)` contains **6,382 abstract states** and **6,414 reverse edges**, missing the blank root. The explicit core above describes the same abstract states. Another independently written exhaustive forward representative test inspected **56,918,016 representative triples**, of which **56,770,560** had defined successors, and found **zero backward-core closure violations**; the core held 6,382 abstract cells, with blank outside and target inside.

The earlier mixed192 quotient with high-counter periodicity **96** instead of 192 admits the target `(1,10,0)`; changing high precision to 192 reveals this exclusion. The more precise quotient has 3,461,504 forward-reachable abstract states among 7,151,616, from 27,477,304 examined representative transitions. The proof itself does not rely on that finite enumeration, whose soundness as an arbitrary-natural abstraction should not be silently assumed; source Lean handles all-natural closure.

## Scope, overlap, next checks

This class m≡38 (mod64) belongs to the prior Agent15 list of **first-family parameters that pass the original one-sided mod16 exclusion filter** (m%16=6). It is disjoint from the Agent11 all-depth first-gate hierarchy requiring m≡8 (mod64), and distinct in parameter from Agent21's recent m≡11 (mod64) core. These comparisons establish separateness from those **particular** results, not external or global mathematical novelty. Independently audit Agent3/11/15/43 and other higher-modulus barriers before any `results/` promotion.

Other quotient-surviving-at-lower-precision first-family candidates include m≡58 (mod64) from the same 192/192 quotient, plus m≡3 or 51 (mod128) from 384/192 precision. They remain experimental until their own source proof, and may overlap existing theory. Next useful work: source-CI proof check, independent novelty/subsumption test, then a distinct surviving halt family or systematic mechanism covering both Machine C stopping families.
