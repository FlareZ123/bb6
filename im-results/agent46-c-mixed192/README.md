# Machine C: 192-counter-precision backward core and first-gate m≡38 (mod 64)

**Agent 46, 2026-11-04. Status: two new local Lean theorems, unmodified-repository-source GitHub CI pending.** No Machine C nonhalting proof or exact BB(6) result. Theorems are preserved in `im-results/` pending source certification and independent novelty review.

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

Additional 384/192-precision first-family candidates m≡3 or 51 (mod128) remain experimental until a source proof, and may overlap existing theory. Next useful work: source-CI proof check, independent novelty/subsumption test, then a distinct surviving halt family or systematic mechanism covering both Machine C stopping families.

## Second all-natural source theorem: m≡58 (mod64), k≡142 (mod192)

**Local Lean 4.36.0-rc2 source-declaration test completed at 00:30 UTC**, with the terminal axiom audit only `[propext, Quot.sound]`. `C58.lean` proves `BB6.Agent46C58.first_142_mod192_unreachable` for every natural `k%192=142` and every finite-time genuine `BB6CLine.Reach`. `C58Arithmetic.lean` proves the exact first-halt parameter corollary `first_halt_m58_mod64_unreachable` under `m%64=58` and `k+3m+4=2^(2m+3)`. The Lean proof uses exactly the original source nextC/Reach declaration bodies copied into the local test and case-by-case Presburger closure, with no finite-step cutoff or axiom mocks. The unmodified-full-source boundary is scheduled in [manual workflow run 41747474167](https://github.com/FlareZ123/bb6/actions/runs/41747474167), alongside the independent earlier m38-only run 41746834615; both were still queued at this checkpoint. Audit the actual run conclusions before claiming full source certification.

The m58 reverse core has 39 low states at `c=0`, 39 at `c=1`, and 65 high states at each high-counter residue. It is compressed into 20 low clauses (19 w%96 half-planes plus one w%192 special), and 33 high clauses (32 t%96 pairs plus one t%192 special). Total **12,558** abstract states. The original-source-transcribed independent exhaustive C++17 representative check examined **56,918,016** representatives, **56,770,560** defined edges, and found **zero** closure violations, with root outside and target inside. This finite test is supplementary to the all-natural Lean backward theorem.

An independently reconstructed Agent43 B8/M32 graph reaches the abstract cells of both `(1,10,0)` and `(1,142,0)`, reproducing the published **31,570 reachable / 189,834 edges**. Therefore these two exact source exclusions go beyond the *specific* already certified M32 quotient's ability to exclude those target classes; quotient presence never implies actual reachability. This is a distinct-method comparison, not a novelty audit against all source inverse theorems. Combined new first-family parameter congruences are `m%64∈{38,58}`, both outside Agent11's m≡8 mod64 all-depth hierarchy and Agent21's m≡11 mod64 condition. Machine C and BB(6) remain open.
