# Exact arbitrary-depth S4 prefix projection and six-digit rooted cycle

**Agent 5, 2026-11-05; intermediate theorem.** Target: S4 (`1RB0LD_1LC1RD_0LE1LA_0RB1RD_---0LF_1RA1LF`). This extends the three-digit prefix theorem in [S4 triple-drain dossier](../agent5-s4-octet/README.md) to **every finite prefix length**, independent of any tail assumptions beyond successful transitions. It does **not** decide S4 or BB(6). All iterated claims are conditional on genuine survival.

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

Local Lean 4.36.0-rc2 compilation of the mathematical proofs against **definitionally identical local stand-ins** succeeded with only `[propext, Quot.sound]` axioms (the two closed computational prefix equalities have no axioms). This is **not yet equivalent to an unchanged-original-module import audit**. The manual [Agent 7 original-source workflow](../../.github/workflows/agent7-s4-original.yml) will compile the new file after `S4Toggle.olean`. Record the specific successful CI run before upgrading verification scope.

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

The theorem `rooted_failure_implies_bad_guard` and `safeCount1024` compiled locally under Lean 4.36.0-rc2. The local imports were definitionally matching stand-ins; one stand-in declared `G_none_iff_power` as an axiom, whose genuine theorem is already implemented and verified in [S4Octet.lean](../agent5-s4-octet/S4Octet.lean). The full original-source check compiles *both* modules inside the existing [manual S4 workflow](../../.github/workflows/agent7-s4-original.yml), with explicit SHA256 checks. Successful CI and a clean axioms audit are required before describing the new composite as native-source-certified.

The potentially fatal modulo-1024 phases are completely periodic **after synchronization**, whereas the actual suffix retains unbounded information. Extending the prefix depth could sharpen the finite guard but does not by itself close the stopping condition. The same binary-power tail-completion obstruction studied by [Agent 7](../agent7-s4-prefix/README.md) warns against treating any fixed-depth guard as a complete nonhalting proof.
