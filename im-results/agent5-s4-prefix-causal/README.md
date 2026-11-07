# S4 root prefix dynamics: source-verified periodic projections and the survival gap

**Agent 5, 2026-11-05; intermediate theorem.** Target: S4 (`1RB0LD_1LC1RD_0LE1LA_0RB1RD_---0LF_1RA1LF`). This extends the three-digit prefix theorem in [S4 triple-drain dossier](../agent5-s4-octet/README.md) to **every finite prefix length**, independent of any tail assumptions beyond successful transitions. It does **not** decide S4 or BB(6). All iterated claims are conditional on genuine survival.

## Current synthesis (7 November 2026)

This dossier studies the original S4 candidate `1RB0LD_1LC1RD_0LE1LA_0RB1RD_---0LF_1RA1LF`. **BB(6) remains unresolved.** The strongest current S4 conclusions are:

1. **All-depth prefix causality:** every finite prefix evolves by the exact length-preserving `pp` map whenever the original source run succeeds. This is the general projection theorem described below.
2. **Source-verified first-eight-digit period:** the 5,120-return eighth-digit map has the exact four-cycle `25036 -> 109210 -> 109208 -> 109209 -> 109206 -> 109210`. The total first-eight-digit prefix trajectory has period 20,480. The root-transport theorem says every surviving genuine-root state at return `5457+n` has first eight digits `prefixRun (n % 20480) cycle8PeriodicStart`.
3. **Exact suffix mass drift:** at surviving block-boundary states `U` at return `5457+20480*m`,
   `stackMass cycle8PeriodicStart + stackMass (U.drop 8) = 2247 + 1024*(5457+20480*m)`.
   Therefore each pair of successive surviving block-boundary states carries exactly 20,971,520 additional stack-mass units in the suffix beyond digit eight.
4. **Verification scope:** the eighth-cycle and tail-mass modules passed original-source CI runs [42399978421](https://github.com/FlareZ123/bb6/actions/runs/42399978421) and [42400834321](https://github.com/FlareZ123/bb6/actions/runs/42400834321). A later clean-up run [42402468287](https://github.com/FlareZ123/bb6/actions/runs/42402468287) stopped at a redundant SHA256 check before compiling the module; that check has been removed because the Git commit already pins the source. Replacement source-import run [42403158611](https://github.com/FlareZ123/bb6/actions/runs/42403158611) is queued. The root-transport and mass theorems are conditional on the relevant `prun` states existing. There is no formal proof yet that the root reaches return 5457 or survives indefinitely. A direct `prunFast 5457 seed` kernel computation got stuck in run [42401520955](https://github.com/FlareZ123/bb6/actions/runs/42401520955); the failed theorem was removed.
5. **Ninth-digit lead:** a reproducible Python prefix-map experiment and four standalone Lean computations suggest the ninth digit has the 20,480-return cycle `171050 -> 171052 -> 171051 -> 171049 -> 171050`, giving a candidate 81,920 period for the first nine digits. This is not yet source-imported or a theorem about the root.

**Next decisive test:** use [s5457_chunk_states.py](s5457_chunk_states.py) to obtain the 320 intermediate 16-return full-root checkpoints from the Lean-certified `s337`, then build a chunked source-Lean survival certificate. The existing `seed337` proof already uses this 16-step `simp [prun,P,G,H]` pattern. Once return 5457 is formally reached, source-import the ninth-digit prefix iteration and its four separate return-map computations. A fixed-depth period remains insufficient to prove nonhalting; the eventual objective is to control every possible stopping gate in the evolving suffix.

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


### Finite survival through return 5457: unresolved kernel computation

A tail-recursive evaluator `prunFast` and a Lean theorem `prunFast_eq` proving equivalence with the original `S4Toggle.prun` via `Option.bind` associativity remain in `S4PrefixEighthCycle.lean`. An attempted kernel computation of `prunFast 5457 seed` with `by decide` did not reduce: original-source CI run [42401520955](https://github.com/FlareZ123/bb6/actions/runs/42401520955) became stuck at the full `P/H` computation. No formal survival theorem through return 5457 is claimed, and the failed computation was removed from the verified module.

The candidate state from the Python full-root simulator is

```
[283,906,982,3490,3734,5935,13580,109210,171050,
 366446,435688,443554,1702180,1770018,211301,281569,35137,35134]
```

The independent Python checker agrees with this state after 5,120 returns from `s337`. This remains computational evidence. A next formal attempt should split the run into 16-step source-map chunks using the existing `seed337` proof pattern (`simp [prun,P,G,H]`), or define a structurally recursive evaluator for `H/P` and prove its equivalence to the original well-founded definitions. The exact prefix-period theorem remains conditional on survival at the relevant return.


A further local experiment used a tail-recursive `prefixRunFast` with a proved equivalence to the standalone recursive `prefixRun`. Each of the four concrete ninth-digit return equalities was separately kernel-checked with `by decide` in Lean 4.36.0-rc2, with no extra axioms (about 33 seconds per value). The combined four-theorem file timed out, while separate modules succeeded. The reproducible Lean files are now preserved under [`standalone/`](standalone/). They are still not source-imported; the ninth-digit cycle remains a candidate until that bridge and its root transport are formalized.


The full-root simulation is now reproducible with [s5457_chunk_states.py](s5457_chunk_states.py). It starts from the Lean-certified `s337`, runs the original Python `checker.chain` for 5,120 returns, asserts the candidate `s5457`, and exposes 320 intermediate 16-return checkpoints through `chunk_states()`. Those checkpoints are intended as input for a future chunked source-Lean survival certificate.
