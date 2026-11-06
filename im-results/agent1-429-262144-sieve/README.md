# BB429: depth-20 exact inverse sieve at modulus 2^18

**Scope, 6 November 2026.** The genuine blank-origin accelerated section of the six-state machine `1RB0LF_1RC1RA_0RD0RB_1LE---_0LA1LE_1RD1LA` has an exact terminal condition `b+1=2*a`. The new `BB429SplitSieve.lean` is a direct specialization of the already source-proved `BB429Kernel16.cert_sound` on 673 distinct affine families. The full unchanged-repository-source verification **passed** in manual Lean 4.36.0-rc2 [run 42310280920](https://github.com/FlareZ123/bb6/actions/runs/42310280920) for the authentic accelerator and all 673 cylinder exclusions. The additional [run 42310886401](https://github.com/FlareZ123/bb6/actions/runs/42310886401) **passed** for the source-connected [BB429Distinct.lean](BB429Distinct.lean) exact count and pairwise uniqueness proof. The separate [original Cryptids raw-machine transport](SourceRawHaltSplit.lean) **passed** original pinned Google DeepMind Cryptids source verification in [native CI run 42310573919](https://github.com/FlareZ123/bb6/actions/runs/42310573919), with the unchanged raw Turing machine and all precursor source modules rebuilt and inspected for `sorryAx`. **No decision of this holdout, another machine, or BB(6) follows.**

## Precise statement

For every genuine source-accelerated time `n` and natural pair `(a,b)` reached from the actual blank root `(0,0)`, if `b+1=2*a` then

```lean
a % 262144 ∉ BB429SplitSieve.excluded
```

Here `excluded` is the explicit disjoint union of sixteen lists of residues `0 ≤ r < 262144`. For each of the **673** listed residues, the source's existing depth-20 affine inverse Boolean certifier evaluates to `true` at

```lean
BB429Kernel16.cert 20 ⟨262144, r, 524288, 2*r-1⟩
```

and its pre-existing soundness theorem excludes every `(262144*q+r, 524288*q+2*r-1)`, **uniformly for every `q : Nat`**. The lists are constructed by splitting each of Agent 33's prior 58 necessary terminal residues modulo 16384 into sixteen lifts; there are 928 candidate lifts. The sieve covers 673, with a separate source-kernel proof of NoDup, and leaves 255 uneliminated by this predicate. This count describes the candidate filtering performed by this particular certificate, and makes no claim about reachability of any survivor.

## Proof method and evidence

[Source Lean module](BB429SplitSieve.lean) retains the exact original `BB429Rank.next` accelerator through its imported `BB429InverseKernel16` and `BB429NewResidue` dependency chain. It reuses the seven previously verified true-root invariant leaves, inverse transforms `F/S/E`, and the all-natural `cert_sound` theorem. The sixteen `partN_certificate` lemmas each use kernel `decide` on a small list. The aggregate theorem is obtained by list concatenation and rewriting those sixteen proofs. An explicit positivity certificate is used to handle natural-number subtraction when converting affine coordinates into the terminal expression.

The independent Python prototype `/tmp/429cert.py` used during discovery was only a generator; the in-repository Lean source retains all 673 literal inputs, certified true results, and the actual-root theorem. [BB429Distinct.lean](BB429Distinct.lean) proves `excluded.length=673` and `excluded.Nodup` by kernel-checked disjoint blocks rather than assuming distinctness from the prototype. The source runs above are decisive checks against the actual repository accelerator. The parent inverse soundness theorem has earlier [source verification](https://github.com/FlareZ123/bb6/actions/runs/42226859021).

Compared with the predecessor [58/16384 necessary filter](../agent33-429-five-shift/BB429Count58Sixteen.lean), these 673 certificates refine its still-open residue families but do not prove global exclusion of the remaining 255 lifts. Independent source verification of the [raw Turing machine transport](SourceRawHaltSplit.lean) is now underway; the union's finer-modulus completeness as a 255-class necessary mask can be added after verifying the explicit 58-to-928 membership bridge. Academic priority and independence from every finer previously established residue restriction remain under review. This is intermediate research and stays in `im-results/`.

## Unresolved problem

The backwards certifier stops at inverse leaves not covered by the seven source-verified root restrictions. Fixed modular splitting cannot by itself determine that the entire infinite limit set is impossible: each level retains candidates, and any authentic blank-root path through them still needs all-time analysis. The next significant step is a uniform history-sensitive invariant or an actual-root contradiction that eliminates an entire surviving family without continually refining the modulus, ideally producing a genuine machine-level halt/nonhalt decision.
