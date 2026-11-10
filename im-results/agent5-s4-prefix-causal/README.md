# S4 root prefix dynamics: source-verified periodic projections and the survival gap

**Agent 5, 2026-11-05; intermediate theorem.** Target: S4 (`1RB0LD_1LC1RD_0LE1LA_0RB1RD_---0LF_1RA1LF`). This extends the three-digit prefix theorem in [S4 triple-drain dossier](../agent5-s4-octet/README.md) to **every finite prefix length**, independent of any tail assumptions beyond successful transitions. It does **not** decide S4 or BB(6). All iterated claims are conditional on genuine survival.

## Current synthesis (9 November 2026)

This dossier studies the original S4 candidate `1RB0LD_1LC1RD_0LE1LA_0RB1RD_---0LF_1RA1LF`. **BB(6) remains unresolved.** The strongest current S4 conclusions are:

1. **All-depth prefix causality:** every finite prefix evolves by the exact length-preserving `pp` map whenever the original source run succeeds. This is the general projection theorem described below.
2. **Source-verified first-eight-digit period:** the 5,120-return eighth-digit map has the exact four-cycle `25036 -> 109210 -> 109208 -> 109209 -> 109206 -> 109210`. The total first-eight-digit prefix trajectory has period 20,480. The root-transport theorem says every surviving genuine-root state at return `5457+n` has first eight digits `prefixRun (n % 20480) cycle8PeriodicStart`.
3. **Exact suffix mass drift:** at surviving block-boundary states `U` at return `5457+20480*m`,
   `stackMass cycle8PeriodicStart + stackMass (U.drop 8) = 2247 + 1024*(5457+20480*m)`.
   Therefore each pair of successive surviving block-boundary states carries exactly 20,971,520 additional stack-mass units in the suffix beyond digit eight.
4. **Authentic finite-root certificate:** The eighth-prefix and tail-mass modules passed original-source CI [42403158611](https://github.com/FlareZ123/bb6/actions/runs/42403158611). The later full-root generator [s5457_lean_certificate.py](s5457_lean_certificate.py) connects the original-source certified `s337` to the complete, explicit 18-digit `s5457` using 320 consecutive sixteen-return source proofs. Its `seed5457 : prun 5457 seed = some s5457` theorem and `#print axioms` audit passed within [CI 42416216490](https://github.com/FlareZ123/bb6/actions/runs/42416216490), which failed only in the subsequent ninth-prefix module. The separate [CI 42539261613](https://github.com/FlareZ123/bb6/actions/runs/42539261613) also passed the full-root step; ninth-prefix compilation is separate. Survival to return 5457 is therefore genuinely source certified, while all-time survival is open. The earlier direct reduction attempt [42401520955](https://github.com/FlareZ123/bb6/actions/runs/42401520955) was abandoned in favor of the successful chunked proof.
5. **Fully original-source-certified ninth-prefix period:** [S4PrefixNinthCycle.lean](S4PrefixNinthCycle.lean) proves `cycle9_period81920 : prefixRunFast 81920 cycle9Start = cycle9Start` and `root_nine_prefix_mod81920` for **every** surviving original reduced S4 root at return `5457+n`. The four 20,480-return numeric blocks, the genuine source-root 5457 bridge, and their periodicity composition all passed the pinned original-source [CI 42643801696](https://github.com/FlareZ123/bb6/actions/runs/42643801696) at commit `9778472b60dc2d23638a35b2fd900687f81f97f0`. `#print axioms` confirms only `[propext, Quot.sound]` for both final theorems, with no `sorryAx`. This establishes the previously pending periodic source bridge, conditional on actual success at each future return; it does not establish all-time survival.
6. **Root-connected necessary-phase sieve with exact-integer census:** The now original-source-proved 81,920-return nine-prefix periodicity, together with the source `G_none_iff_power` theorem and weighted concatenation identity, makes a finite arithmetic test of the three power gates sufficient to exclude any original-root stopping event outside its candidate phases. [ninth_gate_census.py](ninth_gate_census.py) evaluates the total 81,920 phases and reports **81,217 universally safe prefix phases** and **703 candidate phases**, disjointly split as **118** for `G 509`, **196** for `G 290`, and **389** for `G 219`. The cardinalities and exact phase list remain Python exact-integer computations, not Lean-kernel-enumerated or an entire-source packaged root halting theorem. The first candidate phase is 255. Every actual original-root halt after the certified 5457 checkpoint must occur at one of these phases modulo 81,920, provided the necessary prior root transitions succeed; candidate phases do not assert a halt.
7. **Mass-only obstruction is now constructive:** [S4MassCompletion.lean](S4MassCompletion.lean), [S4MassDyadicPower.lean](S4MassDyadicPower.lean), and [S4MassBridge.lean](S4MassBridge.lean) prove in local Lean 4.36.0-rc2 that for every suffix mass `m ≥ max(10,k)`, one can choose a suffix of **at most three digits** with exactly mass `m` and weighted value `W` satisfying `W+k=2^e`. For any nine-digit prefix `xs` with `W(xs)+509=512*k`, concatenation makes `W(xs++suffix)+509=2^(e+9)`, the exact first S4 binary-power stopping gate. [S4MassSourceGate.lean](S4MassSourceGate.lean) applies the pinned original `G_none_iff_power` criterion, and the original-source [CI 42543510207](https://github.com/FlareZ123/bb6/actions/runs/42543510207) **passed its complete mass-gate proof step**. The updated [ninth_gate_census.py](ninth_gate_census.py) computes that **all 118 first-stage candidate phases** of the 81,920 projected cycle have hypothetical rooted suffix mass exceeding `k`, with minimum margin **5,770,295**. This exact-integer cardinality requires no experimental infinite-horizon claim. Therefore total mass, even when fixed to the authentic root's linear drift, cannot eliminate any of these 118 synthetic first-stage stopping completions. A root-history invariant remains necessary. The stronger [exact-shape-gate.md](exact-shape-gate.md) provides an elementary constructive proof that one can additionally prescribe the **exact suffix length** when the mass is sufficiently large relative to that length and the gate offset. The executable [ninth_same_shape_witness.py](ninth_same_shape_witness.py) demonstrates at **all 118 first-gate candidate phases of the finite source-shaped trace** that a synthetic first-gate stopper shares the authentic simulated state's nine-digit prefix, full-stack mass, full-stack length, **and final two digit values**. Of those genuine simulated suffixes, 38 have length 9 and 80 have length 13. The later trace is computational evidence, separate from the formal root-through-5457 certificate.

8. **Higher projected root-cycle atlas (new finite arithmetic):** The first 18 entries of the *source-certified* 5,457-return stack generate a total-prefix trajectory with a computed period of **20,971,520 reduced returns** after **1,310,720 projected returns**. A [reproducible exact-integer C++20 census](DEEP-PREFIX-PERIODS.md) checks this 18-prefix return equality and counts **386 disjoint necessary gate phases per period** (93 / 110 / 183 for the three stages), excluding all possible suffix halts at the other 20,971,134 phases. The general source causality theorem makes this a conditional authentic-root sieve, but the new long numerical period itself is not yet Lean-kernel certified. Prefix periodicity still leaves infinitely many genuine-tail gate candidates.

9. **Root-connected 386-gate suffix return law (new mathematical reduction):** Over the computed 18-digit prefix period of 20,971,520 original reduced returns, exactly 386 source `G` gates cross the prefix into the unbounded suffix; another 402 boundary head-additions absorb into those gates. A universal source-equation factorization gives `P^T (p* ++ S) = Option.map (p* ++) (Q S)` for **every finite suffix S**, with `Q` the explicit word of 386 partial `G` operations (all effective offsets positive, total 21,474,835,708). The period and word have finite C++20 certificates, and one full source-shaped continuation agrees with the compressed word. The generic factorization is an exact mathematical derivation; its source Lean import and the 18-prefix numerical periodicity remain kernel-certification obligations. This reduces the genuine-history question to a recurring 386-operation tail map, while preserving all halting possibilities. See [suffix renormalization](SUFFIX-RENORMALIZATION.md) and [complete executable](s4_suffix_macro.cpp).

10. **Two-level exact suffix renormalization (new core direction):** The 386-gate first-level `Q` has a modeled genuine-root 10-digit suffix-prefix `r*` after 107 `Q` blocks; its **10-digit total prefix repeats exactly after 12,800 `Q` blocks**, with a universal second-level return identity on every appended finite suffix. It reduces **268,435,456,000 original `P` returns to just 4,603 effective partial `G` operations**, preserving halting semantics, with offset mass sum check `sum(e+2)=274877906944000`. A complete 4,940,800-gate first-level source-shaped simulation agrees with the compressed output. A separate 50,000-block `R` model scan advanced 13,421,772,800,000,000 additional reduced returns without an event, with 8-to-30 digit suffix growth, but provides finite evidence only. The all-suffix factorization follows the original source `H/G` equations; the 18-/10-prefix periods and starting section beyond return 5457 still need Lean-kernel certification. See [nested reduction](NESTED-SUFFIX-RENORMALIZATION.md) and [self-contained C++20 generator](s4_nested_macro.cpp).

11. **Third-level exact suffix return (new):** The 4,603-gate second-level `R` has a model-root seven-digit section `s*` whose total projection repeats exactly every **800 `R` blocks**. Its complete 3,682,400-operation word factors into **28,802 effective partial `G` operations** and 28,830 boundary head-adds absorbed with zero trailing addition. The third-level partial map advances **214,748,364,800,000** original `P` returns per call, preserving every possible halting event; `sum(e+2)=219902325555200000`. A direct full-stack `R^800` model run agrees with the compressed `G` word. The numerical period and finite section are still C++-certified. See [third-level derivation](THIRD-SUFFIX-RENORMALIZATION.md) and [reproducible C++20 extractor](s4_third_macro.cpp).

**Next decisive test:** Establish a true all-time source-rooted invariant, or a source-certified failing gate, for the genuine residual suffix under the [third-level 28,802-gate return word](THIRD-SUFFIX-RENORMALIZATION.md). The generic source `H/G` boundary lemma is confirmed by [pinned original-source CI run 42731119081](https://github.com/FlareZ123/bb6/actions/runs/42731119081), and the arbitrary positive-offset word lemma is locally Lean checked and queued for pinned-source CI. The 18-/10-/7-digit numeric section periods and finite rooted continuation beyond return 5457 remain C++-verified arithmetic. The exact machine fate still requires genuine history-sensitive reasoning.

## Detailed theorem and proof records

## Mathematical theorem

The existing exact original-source S4 map is
`P = G 509 >>= G 290 >>= G 219`, acting on finite natural-number stacks. Define a total, finite `hp(a,xs)` whose length equals `xs.length + 1`:
- `hp(a,[])=[a/2+2]` if `a` is even, otherwise `[a/2]`;
- for `xs=b::t`, if `a` is even return `(a/2+2)::(b+a/2)::t`;
- if `a` is odd return `(a/2)::hp(b+a/2+1,t)`.

Put `gp(c,[]) = []`, `gp(c,b::xs)=hp(b+c,xs)`, and `pp=gp(219) ∘ gp(290) ∘ gp(509)`. Thus `gp` and `pp` preserve prefix length.

**Causality theorem (all depths):** For every finite prefix `xs`, arbitrary suffix `S`, and successful source result `P(xs++S)=some U`,
```
U.take xs.length = pp xs.
```
By induction, for every successful rooted or synthetic orbit `prun n (xs++S)=some U`,
```
U.take xs.length = prefixRun n xs,
```
where `prefixRun` is the total iteration of `pp`. Hence the full unbounded map projects onto an exact finite-dimensional deterministic map at **every** length, provided the actual map survives. This gives a source-specific reusable certificate interface for fixed-depth prefix questions, including root classes and collision experiments.

**Exact genuine-seed six-digit period:** Define `seed=[301,650,645,322,163,160]`. The kernel-computable total prefix iteration satisfies
```
prefixRun 143 seed = [280,398,1257,5171,3976,3776] = phase
prefixRun 1024 phase = phase.
forall n, prefixRun (143+n+1024) seed = prefixRun (143+n) seed.
```
Thus, for every *successful* genuine `P` orbit at time `143+n`, its first six digits equal the corresponding period-1024 total prefix trajectory. This strengthens the previously proved period-32 three-digit cycle, with an explicit effective transient.

These theorems imply **no unrestricted survival**: synthetic tails can still produce `G` power-of-two stopping gates. They do not imply the real seed survives 1024 further calls or that the entire stack repeats. A repeated finite prefix is consistent with a strictly changing deeper stack.

## Proof, reproduction, verification boundary

[Lean source, XZ+Base64](S4PrefixCausal.lean.xz.b64). Decode using ordinary `base64` and `xz` tools. The decoded exact UTF-8 Lean 4.36.0-rc2 file has SHA256 `81400697e2e0dc35f9193c637eff49e0e1df8344986899a58fa121621a78ffef`. It imports unchanged repository `S4Toggle`, which imports `S4Octet` and `S4PowerGate`; these themselves are source-linked to the unchanged pinned Cryptids machine via the prior chain.

The proofs passed original-source [manual CI run 42091626268](https://github.com/FlareZ123/bb6/actions/runs/42091626268), importing the pinned unmodified Cryptids acceleration and all intermediate exact-map modules. Axiom audits: `prun_prefix`, `root_six_period`, `root_six_conditional` need only `[propext, Quot.sound]`; the period-1024 equality and 143-step finite prefix are axiom-free. The same manually dispatched workflow(../../.github/workflows/agent7-s4-original.yml) will compile the new file after `S4Toggle.olean`. Record the specific successful CI run before upgrading verification scope.

## Next decisive test

The period-1024 prefix can be used as a finite sound guard against a large fraction of the possible `W+c=2^k` stopping gates by checking residues modulo 64 at the three successive G substeps, but it cannot on its own exclude every possible synthetic suffix. A full root decision requires a history-sensitive whole-stack or all-depth argument controlling the surviving stopping sectors. Distinguish such an argument from merely making the prefix deeper.

Prior related results: [Agent 7 finite-prefix compatibility theorem](../agent7-s4-prefix/README.md) is a power-gate completion criterion; [Agent 5 three-digit theorem](../agent5-s4-octet/README.md) established the analogous dynamics only for the first three digits. The present contribution is a general all-depth *dynamical semiconjugacy*, plus a six-digit genuinely seeded cycle.


## Uniform power-gate sieve from the rooted six-digit cycle

[Second Lean module](S4PrefixGate64.lean.xz.b64), decoded UTF-8 SHA256 `5a0dba9b3dbc8a0bca50c7ae9e9aba6a9bf8ed652780c132d80bb78e32046065`, formalizes an all-suffix modular sieve for each of the three source-exact odd-drain operations in `P`. Let `guard6 xs` assert the nonzero remainders modulo 64 of `W xs+509`, `W(gp 509 xs)+290`, and `W(gp 290 (gp 509 xs))+219`. For any six-digit `xs` and arbitrary `S`:

```
xs.length=6 and guard6 xs=true  ⇒  P(xs++S)≠none.
```

The proof uses `W(xs++S)=W xs+2^6 W S` and the existing original-source theorem `G c R=none ↔ W R+c` is a power of two. Powers strictly above 64 vanish modulo 64; every `c∈{509,290,219}` already exceeds that threshold. The exact prefix projection transports this guard through all three successive drains and is valid even if the deeper stack changes unpredictably.

A separate **kernel-evaluated, axiom-free** finite calculation establishes that precisely **956 of the 1,024** cyclic six-digit phases satisfy `guard6`. Consequently, a first failure of the *genuine seeded P recurrence* after the 143-step prefix transient requires one of the **68** remaining phase residues modulo 1024. This is a **necessary condition only**. The guard-unknown phases may be safe for other reasons, and even a synthetically stopping completion does not imply actual-root reachability.

The theorem `rooted_failure_implies_bad_guard` and `safeCount1024` compiled locally under Lean 4.36.0-rc2. The local imports were definitionally matching stand-ins; one stand-in declared `G_none_iff_power` as an axiom, whose genuine theorem is already implemented and verified in [S4Octet.lean](../agent5-s4-octet/S4Octet.lean). The complete source-level source-to-gate audit passed [run 42091626268](https://github.com/FlareZ123/bb6/actions/runs/42091626268): the SHA256 checks matched, both Lean modules compiled with unmodified pinned Cryptids imports, `safeCount1024` had no axioms, and `P_safe64` and `rooted_failure_implies_bad_guard` reported only `[propext, Classical.choice, Quot.sound]`.

The potentially fatal modulo-1024 phases are completely periodic **after synchronization**, whereas the actual suffix retains unbounded information. Extending the prefix depth could sharpen the finite guard but does not by itself close the stopping condition. The same binary-power tail-completion obstruction studied by [Agent 7](../agent7-s4-prefix/README.md) warns against treating any fixed-depth guard as a complete nonhalting proof.

## Seven-digit root certificate and the first odd cycle factor

The third module [S4PrefixSeven.lean.xz.b64](S4PrefixSeven.lean.xz.b64), decoded SHA256 `c4602d569435a0aea4674752e84a1c830576263be3d2712982479e1832da13d9`, extends the exact finite-prefix projection to a concrete genuine seventh stack entry. It kernel-certifies the full actual root at recurrence step 143:

```
prun 143 [301,650,645,322,163,160]
  = some [280,398,1257,5171,3976,3776,20445,38331,53457,21578].
```

That *finite* statement was proved using nine separate source-shaped 16/15-step computations and a proved associative run-composition lemma. It gives a real rooted 7-prefix `phase7=[280,398,1257,5171,3976,3776,20445]` at step143. After 194 additional **total prefix** transformations, the seven-digit projection reaches `cycle7=[283,906,982,3490,3734,5935,13580]`, and `prefixRun 5120 cycle7=cycle7`. The latter equality was verified by 20 individually kernel-checked 256-step chunks, composed by the general `prefixRun_add` theorem. Conversely, `prefixRun 1024 cycle7≠cycle7` is kernel-checked, so this 5120-period witness cannot be an accidental reuse of the six-digit period.

For every `n` and every **surviving genuine** recurrence stack at time `337+n`, the first seven digits therefore equal `prefixRun (194+(n%5120)) phase7`. The true root's survival for all `n` is **not asserted**. Seven-digit projected periodicity includes an additional factor `5` beyond the previous 1024-period six-digit projection. This is an internal mathematical structural discovery, with no external novelty audit and no claim of a universal root decision.

The complete theorem file locally compiled with Lean 4.36.0-rc2 and only `[propext, Quot.sound]` axioms; all finite cycle equalities used no axioms. An unchanged-original-Cryptids import is added to the same manual workflow and its successful outcome should be checked before upgrading its original-source provenance.


## Exact eighth-prefix four-cycle and 20,480-return projection period

**Agent 5, 2026-11-07; intermediate result.** The new source-importing module [S4PrefixEighthCycle.lean](S4PrefixEighthCycle.lean) computes the exact eighth-digit return map over one 5,120-return block, using the existing `S4PrefixEighthMass` prefix-contraction and root-transport theorems:

```
return8 25036 = 109210
return8 109210 = 109208
return8 109208 = 109209
return8 109209 = 109206
return8 109206 = 109210
```

Thus, after the first block, the eighth digit follows the four-cycle
`109210 -> 109208 -> 109209 -> 109206 -> 109210`. The corresponding eight-digit prefix start is
`cycle8PeriodicStart = [283,906,982,3490,3734,5935,13580,109210]`, and its total prefix trajectory has exact period 20,480:

```
prefixRun 20480 cycle8PeriodicStart = cycle8PeriodicStart
```

More strongly, the root-transport theorem proves that for every `n` and every stack `U` satisfying the genuine source-map survival hypothesis `prun (5457+n) seed = some U`,

```
U.take 8 = prefixRun (n % 20480) cycle8PeriodicStart.
```

This is an exact period for the first eight digits of every *surviving* genuine-root configuration from accelerated return 5457 onward. It does not prove survival to 5457, survival thereafter, or repetition of the complete stack. The five return-map values are kernel-computed with `by decide` and have no extra axioms; the period and root-transport proofs reuse the existing prefix-block and root-causality theorems. Local Lean 4.36.0-rc2 computation and proof-body checks passed. Original-Cryptids source-import CI run [42399978421](https://github.com/FlareZ123/bb6/actions/runs/42399978421) passed on the first source-connected version of this module. The subsequent tail-mass extension also passed original-source CI in run [42400834321](https://github.com/FlareZ123/bb6/actions/runs/42400834321).


### Exact mass drift into the suffix beyond digit eight

The same module now adds a source-level consequence of the 20,480-return prefix period. At every block boundary, the first eight digits are exactly `cycle8PeriodicStart`. Combining this with the existing root mass law `stackMass U = 2247 + 1024*n` gives, for every surviving root state `U` at accelerated return `5457 + 20480*m`,

```
stackMass cycle8PeriodicStart + stackMass (U.drop 8)
  = 2247 + 1024*(5457 + 20480*m).
```

Consequently, whenever two successive block-boundary states `U,V` both exist,

```
stackMass (V.drop 8) = stackMass (U.drop 8) + 20,971,520.
```

Thus the entire exact 20,971,520-unit mass increment per 20,480-return block is carried by the suffix after the periodic eight-digit prefix. This is conditional on the relevant root states existing; it does not establish that the machine survives indefinitely. The additive mass identities are Lean-proved and passed the same source-import run.


### Source-certified finite survival through return 5457; superseded direct computation

A tail-recursive evaluator `prunFast` and a Lean theorem `prunFast_eq` proving equivalence with the original `S4Toggle.prun` via `Option.bind` associativity remain in `S4PrefixEighthCycle.lean`. An attempted kernel computation of `prunFast 5457 seed` with `by decide` did not reduce: original-source CI run [42401520955](https://github.com/FlareZ123/bb6/actions/runs/42401520955) became stuck at the full `P/H` computation. The direct reduction failed and its theorem was removed from the verified module. A *different* proof now establishes the full-root 5457 state: [s5457_lean_certificate.py](s5457_lean_certificate.py) produces 320 short source-importing Lean segment proofs, composed with the earlier certified `seed337`. The complete source theorem passed the finite-root CI steps of [42416216490](https://github.com/FlareZ123/bb6/actions/runs/42416216490) and [42539261613](https://github.com/FlareZ123/bb6/actions/runs/42539261613).

The candidate state from the Python full-root simulator is

```
[283,906,982,3490,3734,5935,13580,109210,171050,
 366446,435688,443554,1702180,1770018,211301,281569,35137,35134]
```

The independent Python checker agrees with this state after 5,120 returns from `s337`. This exact stack is now a source-certified finite result via the composed 16-step certificate. Its nine-prefix is the initial state of the proposed periodic nine-digit projection. The certificate is finite and makes no all-time survival claim. The exact prefix-period theorem remains conditional on survival at the relevant return.


A further local experiment used a tail-recursive `prefixRunFast` with a proved equivalence to the standalone recursive `prefixRun`. Each of the four concrete ninth-digit return equalities was separately kernel-checked with `by decide` in Lean 4.36.0-rc2, with no extra axioms (about 33 seconds per value). The combined four-theorem file timed out, while separate modules succeeded. The reproducible Lean files are under [`standalone/`](standalone/). The source-linked root transport and cycle composition are now committed as `S4PrefixNinthBase.lean` and `S4PrefixNinthCycle.lean`; verify the result of [CI 42539261613](https://github.com/FlareZ123/bb6/actions/runs/42539261613) before regarding them as source certified.


The full-root simulation is now reproducible with [s5457_chunk_states.py](s5457_chunk_states.py). It starts from the Lean-certified `s337`, runs the original Python `checker.chain` for 5,120 returns, asserts the candidate `s5457`, and exposes 320 intermediate 16-return checkpoints through `chunk_states()`. Those checkpoints were used by [s5457_lean_certificate.py](s5457_lean_certificate.py) in the source-proved 320-chunk finite survival certificate.
