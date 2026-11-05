# P1 source-certified exceptional input-one inverse exclusion (Agent 45)

**Status 2026-11-05 17:07 UTC:** Exact Lean 4.36.0-rc2 compilation locally against *unchanged, Git-blob-hash-verified* original modules. This is a reusable source-connected inverse-exit obstruction; it is **not** a P1 blank-root decision, an isolated critical-index closure, or a BB(6) bound. No original-source GitHub Actions CI run is asserted. The locally compiled final theorems report exactly `[propext, Classical.choice, Quot.sound]`, with no `sorryAx`.

## Original-source theorem

Modules `Exceptional.lean`, `NoC1Arithmetic.lean`, `NoC1Source.lean`, `NoC1AllQ.lean`, `NoC1Q29.lean` prove the following.

Let `q≥12`, `N=16q`, `L≤16q+9`, `m≤15q`, and a positive-left, even-left original P1 G output `(b,d)` have authentic shadow coordinates `w,z,alpha`, with `w≥4,z>0` and equations

```
b+d+2m+2L+3 = 56*2^N
L+m=w+z
b+4w=alpha*2^(N-m).
```

Then for **every** natural `k` the original source recursive drain satisfies `G(k,1) ≠ (b,d)`. This is theorem `BB6.Agent45Exception.no_special_G_one_above_12`, quantified over *all* q and k satisfying the premises. It makes no reachability assumption beyond those exact constraints; an authentic P1 odd-inverse node with the established shadow encoding can instantiate it.

Core proof mechanism:

1. Original `G_input_power` says a `G(k,1)` output requires shifted right input `s=d+b/2+3=4*2^t`, a power of two.
2. Original source arithmetic `encoded_shift_divisible` implies `2^(N-m-2) | s+2z`.
3. The source coordinate and `w` bound imply `s≥2^(N-m-2)`, while `0<2z<2^(N-m-2)`.
4. A power of two of size at least `2^(N-m-2)` is divisible by that power; subtracting its divisibility from the sum forces an impossible nonzero, smaller multiple.
5. The only uniform analytic estimate needed is `2(31q+9)<2^(q-2)` for `q≥12`, proved by exact induction in Lean. It yields `2(L+m)<2^(N-m-2)` throughout the full preexisting **15q cost budget**.

The separate `q29_no_special_G_one` specialization dispenses with the q≥12 general construction and uses `N=464,L≤473,m≤10`, matching the already source-checked Agent9 q29 full odd-cone invariant. It remains conditional on the exact source encoding of the queried hub; it is available to the independent q29 terminal-closure effort.

## Verifier provenance

The following existing repository originals were copied byte-for-byte for local compilation and verified using Git blob SHA-1:

| Source | Original blob SHA |
| --- | --- |
| `im-results/agent1-p1-map/GParity.lean` | `83ab5fbe1b23c14a8155283b0f203e83236d1fb9` |
| `im-results/agent1-p1-map/GInverse.lean` | `f820b28010ca4b7d7ed4dc5af8e6fcb08d1b7b6d` |
| `im-results/agent9-p1-shadow/ShadowDepthArithmetic.lean` | `07fe6e6511cbd454d55ff5cb3a6d3d666c609988` |

Local originals were compiled in dependency order with Lean 4.36.0-rc2, commit `b35cb10cf2ced51a2fd1880cfdbf75c71ab7a35a`. The five current new file blob hashes are `1b10ca62ef568d3d400d79c4245eacc06592f0a3` (`Exceptional`), `08d919e8df084e379f2873c139009c102ac80e7e` (`NoC1Arithmetic`), `eff7fe17b567eb5a308157f36ad8398c3119ac29` (`NoC1Source`), `b02bd252499ea512c90ee3210bfdd043392718b5` (`NoC1AllQ`), `aec5d1d4c932956b0e0408409a32c7a62f44a17c` (`NoC1Q29`). All hashes were checked against current GitHub content. Early **local debug stubs** for `G_input_power` and `encoded_shift_divisible` were discarded from the final verification path; the reported final axiom audit was compiled against exact original upstream files.

## What is still required

This excludes the special `c=3` source T branch through `G(k,1)` for shadow-encoded nodes in the stated range. It does **not** exclude ordinary positive-G inverse exits with odd child, even-right child, a left counter not divisible by four, or the genuine reset case. Existing [Agent1 cost-gap](../agent1-p1-quarter/README.md) addresses even-right terminal leaves with m+t+1≤15q, and [Agent9 shadow source certification](../agent9-p1-shadow/README.md) establishes exact encoded odd cones for the q29 graph, but complete actual-blank-root exclusion still requires all source predecessor cases and an integrated theorem. In particular, the new result does not prove `¬Reach 2 H(466)`. Avoid treating a necessary source exclusion as an actual machine decision.

Next useful step: integrate this uniform theorem with the source-complete original Reach predecessor dichotomy and Agent1's existing even-right cost barrier, then use a complete closed shadow certificate (q29 is a small candidate). Check Agent8 and Agent9 correspondence to avoid duplication.

## Overlap correction (2026-11-05 17:20 UTC)

After this original-source proof was committed, I found Agent 9's previously existing `ShadowNoExceptionalGeneral.lean` and `ShadowNoExceptionalSource.lean`, which already certify a **general binary-carry obstruction** for authentic `inverseAt b d t=some(k,1)` under an explicit shadow-width and cost budget. The mechanism and quantified obstruction closely overlap this note's `encoded_no_special_G_one`. Agent 9's theorem is original-source verified and may already discharge exceptional outputs in applications that have a complete `inverseAt` enumeration. Our present source proof packages the obstruction directly for `G k 1=(b,d)` and supplies a concrete all-q q>=12, m<=15q bound, but **it should not be presented as an independently novel mathematical breakthrough** without a stronger comparison. Both proofs remain intermediate, no machine decision. New structural projects should reuse the strongest existing Agent9/Agent8 generic blocked-cone apparatus rather than expand this duplicate mechanism.
