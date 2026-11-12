# #746 exact reset graph: quadratic inverse-depth ranking

**Agent 44, source proofs verified 5–6 November 2026. Source-level inverse-depth bounds and authentic raw-machine necessary fatal-index exclusions; no full blank-root halt/nonhalt decision.** This dossier proves that every directed *backward* chain in Agent 10's exact first-reset inverse graph has length quadratic in the bit length of its target. It improves the prior termination rank `h<u` in `im-results/agent10-cascade/ResetParentStrict.lean`, which alone yields an exponential-in-bitlength depth bound. Its external novelty has not been audited. Preserve under `im-results/`.

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

**Original-source verification:** All four modules now compile in the complete unchanged checked-in source dependency workflow under Lean 4.36.0-rc2, with `#print axioms` showing only `[propext, Classical.choice, Quot.sound]`, and no `sorryAx`. The rank source audit passed [CI 42060343954](https://github.com/FlareZ123/bb6/actions/runs/42060343954). The fatal-index specialization and exact root-chain-to-bounded-path equivalence passed [CI 42061977162](https://github.com/FlareZ123/bb6/actions/runs/42061977162), commit `18a7cec5741ca163017b64bd2895485c7d3bdf0e`. Earlier runs [42060933442](https://github.com/FlareZ123/bb6/actions/runs/42060933442) and [42061407428](https://github.com/FlareZ123/bb6/actions/runs/42061407428) failed due missing Lean namespace openings `CascadeManyShield` and `CascadeSweep`; both were corrected before the successful unchanged-source run. This proves source-level reset facts. Raw physical TM semantics remain the earlier independently audited upstream bridge.

Manual-only workflow [agent44-746-fanin.yml](../../.github/workflows/agent44-746-fanin.yml) compiled the complete unchanged original source chain and all four new modules in successful [run 42061977162](https://github.com/FlareZ123/bb6/actions/runs/42061977162). The strongest root-facing theorem `CascadeRank.root_fatal_iff_bounded_reverse_path` is in [RootDepth.lean](RootDepth.lean): for every `n>=2`, genuine post-initial blank source root `ReachC (2,0) (fatal n,0)` iff there exists an exact backward `ReversePath (fatal n) 2 steps` with `steps<=(n+2)^2`. Its proof composes source-certified `root_reset_chain_iff`, the new reverse-path conversion, and the fatal depth theorem. This equivalence does not decide whether any such witness exists for all n.

## What this changes and what it leaves open

The predecessor grammar is still **unboundedly branching** across surviving fatal indices, as source-certified in [Agent 44's fan-in dossier](../agent44-746-fanin/README.md). Quadratic chain *depth* does not bound the complete reverse cone's number of nodes by a polynomial. The source-root equivalence `CascadeResetInverse.root_reset_chain_iff` remains the actual connection to the post-initial blank reset `(2,0)`; this new bound does not exclude the root from a single new fatal inverse cone. The original machine's halting decision and the global BB(6) exact value remain open.

**Useful next experiment:** integrate the rank as an explicit depth/fuel certificate in Agent10's `ReachDecide.lean` or `ClosedCert.lean` to accelerate checked inverse-cone search, and seek a cross-index blank-root obstruction that survives synthetic fan-in. A proof of this depth bound should never be presented as a proof of global nonhalting.

## Executable first-return and complete finite fatal-index exclusion through 299

**Verified against original checked-in source:** the unchanged-source Lean 4.36.0-rc2 [run 42067745718](https://github.com/FlareZ123/bb6/actions/runs/42067745718), commit `f7b5f52ae4d5481d774d466036c97c4edea42beb`, completed successfully. The run compiled all modules in this dossier, including `FullThrough299.lean`, and printed only `[propext, Classical.choice, Quot.sound]` for `CascadeFastReturn.fatal_unreachable_through_299`. This supersedes the earlier local-only and queued labels.

The verified source-connected proof chain has three substantive parts:

1. `ScanFail.lean` proves that a primitive-recursive scan finds the exact first failed dyadic sweep guard; `StripTwos.lean` proves exact primitive-recursive factorization into a power of two and an odd remainder.
2. `ExecutableReturn.lean` defines the total computable successor `fastOutcome`, including its terminal `none` branch, and proves `fastOutcome_sound` using the original `closed_outcome`, `even_outcome`, `odd_outcome` and `first_low` source theorems. `FastForward.lean` identifies every finite iteration with the source trajectory. `FastDecision.lean` proves `root_fatal_iff_fatalHitBool`: for every `n≥2`, a deterministic Boolean run of at most `(n+2)^2` first-reset transitions decides reachability of that candidate fatal reset from `(2,0)`. Strict monotonicity allows early exit once the orbit exceeds its target. This proves **fixed-index** decidability, with no decision of the unbounded existential.
3. Ordinary Lean kernel reduction (`by decide`, never `native_decide`) eliminates the 15 surviving indices `257, 262, 263, 268, 269, 274, 275, 280, 281, 286, 287, 292, 293, 298, 299`. `NewFiniteGates.lean`, `Gates270to281.lean`, `Gates282to299.lean`, `GatesTo299.lean` prove the finite range. `FullThrough299.lean` composes these with the previously source-verified `CascadeFastShield.blank_excludes_surviving_through_256`, and proves `fatal_unreachable_through_299`: every post-initial source-root reset target `fatal n` with `4≤n≤299` and `n%6∈{4,5}` is unreachable at **all** times.

**Original physical-machine bridge, now source-certified:** [OriginalGate304.lean](OriginalGate304.lean) composes this full checked-in-source exclusion with Agent 10's genuine original six-state-machine theorem and its verified `rootReachBool_source_iff` bridge. It proves `Agent44Raw746.original_machine_halts_iff_surviving_304`: the exact original blank-tape Turing machine halts iff there exists a candidate `n≥304` with `n%6∈{4,5}` whose `rootReachBool(fatal n)` is true. **Successful unchanged pinned upstream Cryptids [manual CI 42310849868](https://github.com/FlareZ123/bb6/actions/runs/42310849868)**, source revision `c86f15861709b76042998c5211c7b2f83991621b`, proof commit `e09dcd3e0dc6c3b090971a98d46569f3cc31a074`. The final `#print axioms` reports exactly `[propext, Classical.choice, Quot.sound]`, without `sorryAx`; the workflow compiled the original unmodified physical-machine source, source-reset bridge, executable reset grammar and finite gates. This upgrades the previously established authentic-machine necessary index cutoff 268 to 304. The full original-source successful run is distinct from the earlier 4.36 checked-in-source run and confirms the physical-machine theorem in Lean 4.35.0-rc4.
The remaining quantifier is infinite. Neither the stronger finite cutoff nor the polynomial fixed-target checker establishes global nonhalting or determines BB(6). The valuable next direction is a uniform genuine-root exclusion for all surviving indices, or a genuine root-to-fatal witness.


## Additional exceptional t=1 feeder classes (intermediate draft)

[FeederExceptional1085-1372.md](FeederExceptional1085-1372.md) records a proposed seven-edge exact inverse chain for the two remaining residue classes n mod 1458 = 1085, 1372. The associated Lean modules are **not yet CI-verified**. This is a root exclusion for the odd feeder only, not a fatal-target or BB(6) decision; see the note for the exact affine identities, modular residues, uniqueness arguments, and required next verification.
