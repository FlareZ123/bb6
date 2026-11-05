# #746 exact reset graph: quadratic inverse-depth ranking

**Agent 44, 2026-11-05. Intermediate structural result; not an original blank-root halt/nonhalt decision.** This dossier proves that every directed *backward* chain in Agent 10's exact first-reset inverse graph has length quadratic in the bit length of its target. It improves the prior termination rank `h<u` in `im-results/agent10-cascade/ResetParentStrict.lean`, which alone yields an exponential-in-bitlength depth bound. Its external novelty has not been audited. Preserve under `im-results/`.

## Statement and mathematics

Let `ResetParent h u` be the unchanged two-arm exact first-reset predecessor relation defined in `im-results/agent10-cascade/FirstInverseComplete.lean`. For a positive reset height `u`, let

```text
m(u) = floor(log2(u)),
D(u) = 2^(m(u)+1) - u,
rho(u) = (m(u)+1)^2 - floor(log2(D(u))).
```

As `1 <= D(u) <= 2^m`, its rank satisfies `m^2+m+1 <= rho(u) <= (m+1)^2`. Define `rho(0)=0` by the same Lean `Nat.log2` expression. The main theorem is

```lean
CascadeRank.reset_parent_rank_decreases (h u : Nat)
  (hp : CascadeResetInverse.ResetParent h u) :
  CascadeRank.reverseRank h < CascadeRank.reverseRank u
```

**Even inverse arm.** For `p=2^k`, `6p-1 <= u <= 8p-3` and `2u = 8p+h+k`. Hence `m(u)=k+2` and `h<u`. If `m(h)<m(u)`, the disjoint rank intervals at consecutive binary scales imply strict decrease. Otherwise `m(h)=m(u)`, and the upper-boundary deficits satisfy the exact identity `D(h)=2 D(u)+k`. Thus the deficit logarithm increases by at least one, so `rho(h)<rho(u)`.

**Odd inverse arm.** Put `q=2^t d`, with `6p+1<=q<=8p-1`, `2u+5=3^(t+1)d`, and `2q=8p+h+k+5`. Since `3^(t+1)d >= 3q >= 18p+3`, we obtain `u>=8p`. But `h<8p`, so `m(h)<m(u)` and the rank decreases regardless of the exact valuation or dyadic band.

Define the inductive source-relative `ReversePath u v length` by zero steps at `u=v` and a predecessor edge `ResetParent h u` followed by a shorter backward path from `h`. Induction on the path gives the uniform theorem

```lean
CascadeRank.reverse_path_length_le_log_square (u v length : Nat)
  (hp : CascadeRank.ReversePath u v length) :
  length <= (Nat.log2 u + 1)^2
```

As the existing source theorem `CascadeFastShield.fatal_log2` proves `log2(fatal n)=n+1` for `n>=2`, the specialization `FatalRank.lean` proves that **every inverse reset chain from any #746 candidate fatal height `fatal n=4*2^n-n-4` has length at most `(n+2)^2`**, uniformly over n and without an inverse-search cutoff.

## Proof files and verification

- [ReverseRank.lean](ReverseRank.lean): standalone binary rank arithmetic, depending only on Lean `Std`.
- [ResetRank.lean](ResetRank.lean): genuine two-arm `ResetParent` descent; chain-length bound.
- [FatalRank.lean](FatalRank.lean): specialization using the **existing** `CascadeFastShield.fatal_log2` from original source.

**Local check:** Lean 4.36.0-rc2 compiled `ReverseRank.lean` and `ResetRank.lean` against a local verbatim copy of the checked-in `ResetParent` *definition*. The two final rank and chain statements emitted axioms `[propext, Classical.choice, Quot.sound]` without `sorryAx`. This local check is weaker provenance than a complete original-dependency source check. The fatal specialization was locally typechecked against the existing theorem signature, with the source logarithm theorem temporarily declared as an axiom. **Do not treat the fatal specialization as a completed source check until its unchanged-source manual CI passes.**

Manual workflow [agent44-746-fanin.yml](../../.github/workflows/agent44-746-fanin.yml) now compiles the first two modules after all unchanged original first-return dependencies. Source CI [run 42060343954](https://github.com/FlareZ123/bb6/actions/runs/42060343954) was dispatched at 15:58 UTC; its outcome must be checked before claiming full original-source verification. The same workflow needs to be extended and rerun for `FatalRank.lean` after that first audit.

## What this changes and what it leaves open

The predecessor grammar is still **unboundedly branching** across surviving fatal indices, as source-certified in [Agent 44's fan-in dossier](../agent44-746-fanin/README.md). Quadratic chain *depth* does not bound the complete reverse cone's number of nodes by a polynomial. The source-root equivalence `CascadeResetInverse.root_reset_chain_iff` remains the actual connection to the post-initial blank reset `(2,0)`; this new bound does not exclude the root from a single new fatal inverse cone. The original machine's halting decision and the global BB(6) exact value remain open.

**Useful next experiment:** integrate the rank as an explicit depth/fuel certificate in Agent10's `ReachDecide.lean` or `ClosedCert.lean` to accelerate checked inverse-cone search, and seek a cross-index blank-root obstruction that survives synthetic fan-in. A proof of this depth bound should never be presented as a proof of global nonhalting.
