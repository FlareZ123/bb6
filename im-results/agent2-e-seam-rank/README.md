# E3 source-seam rank: a uniform bound on returns to the left-hand region

**Agent 2, 9 November 2026. Successful original-table Lean 4.36.0-rc2 graph certificate:** [manual GitHub Actions run 42613771758](https://github.com/FlareZ123/bb6/actions/runs/42613771758). **Intermediate mathematical result.** No claim of original D blank-root halting, E3 event totality, exact BB(6), or improved BB(6) bounds.

## Precise unconditional graph theorem

Use the source-verified [Agent25 E-seam certificate](../agent25-e-seam-kernel/README.md), whose abstract state records the original D machine's control state, signed head position, and 18 actual tape bits at coordinates **−10 through +7**. The certificate overapproximates any right excursion beyond +7 by allowing *all six* possible live control states on reentry at +7. All 128 initial seven-bit right prefix choices of the **fixed E3 core** are covered. Its source-level physical refinement and exact relation to the original six-state machine are upstream original-source-verified theorems.

The machine-specific certified directed graph has exactly **6,399 states and 7,306 successor edges**, and all its seeds are members. Define

```text
w(v) = 1 if the current head coordinate is at most +3;
       0 otherwise.
```

The new integer rank `R(v)` is the least nonnegative solution produced by monotone relaxation of

```text
R(v) >= w(v) + R(u)  for every abstract successor v -> u.
```

It is well-defined even though the graph has cycles: the graph's **11 cyclic strongly connected components each consist of 78 states**, and every such state is located at coordinates +4 through +7. Thus every cycle has weight zero. The generator finds `max R(seed)=82` for the 128 initial E3 seeds and `max R(v)=82` over all certificate states.

**Main theorem:** `BB6.ESeamRank.all_e3_low_visits` in the generated `ESeamRankMaster.lean` says that **for any finite abstract path** beginning at any certified E3 seven-bit seed, the total number of departure states at head coordinate at most +3 is **at most 82**. The path length is an unrestricted natural number. It may contain arbitrarily many cycles, nondeterministic right-excursion reentries and arbitrary right-tape contents. The proof is a mathematical edge-potential induction: summing `w(v)+R(u)≤R(v)` along a path telescopes, and the initial rank is at most 82.

The rigorous conclusion pertains to the entire kernel-certified physical-window transition graph, so it covers *every abstract path*, not only traces sampled from particular finite suffixes. Existing source-to-physical-window refinement gives the intended original D E3 reading: a nonterminating E3 core cannot visit coordinates ≤+3 infinitely many times, because every such original visit before first event corresponds to a counted window path state. **The complete source-level visit-count corollary is not separately composed into one Lean theorem in this directory.** That is a remaining transport/statement packaging task; original-source correctness of the reused window refinement is certified upstream.

## Why this moves the E3 no-event question

The source-certified all-parameter F/E first-event theorem in [Agent2's F/E dossier](../agent2-e-seam-root/README.md) still permits a branch where the E3 core never reaches its protected marker and never returns F/0. The new rank excludes **any such branch that repeatedly visits the fixed left-hand working area**. A hypothetical endless path must eventually be confined to the right-hand area, with arbitrary farther-right excursions. The only remaining unbounded behavior relevant to E3 event *totality* is rightward escape or right-local indefinite computation.

This does **not** prove that a finite right suffix forces E3 termination; finite initial data can be rewritten, and an all-blank ray need not preclude infinite rightward motion without a separate structural argument. A useful next theorem would show that every finite-suffix rightward branch returns to coordinates ≤+3, hits F/1, or else has some explicit nontermination certificate. Composing such a theorem with the 82-visit bound would give a concrete route to eliminating the prepared-E no-event alternative.

## Reproduction and verification boundary

[make_e_seam_rank.py](make_e_seam_rank.py) is a small, untrusted Python 3.10+ generator. It consumes the pre-existing, source-checked `agent31-d-exceptional/ESeamClosedStates.txt`, recomputes the exact 7,306 graph edges and integer ranks, and writes one `ESeamRankBase.lean`, 200 independent leaf proofs `ESeamRankBlock{0..199}.lean`, and one `ESeamRankMaster.lean`. The generator uses fsynced atomic replacement of output files.

Lean, independently of the generator, checks every rank inequality against the already certified original D abstract successor function, every seed bound, and the unbounded `CountPath` induction. The existing Agent25 generator builds its 200 graph closure proof blocks before the rank proof. A generated rank value omitted from the tree, a bad edge, missing graph node, or an incorrect seed rank would cause the corresponding kernel proof to fail.

The manual-only workflow [agent2-e-seam-rank.yml](../../.github/workflows/agent2-e-seam-rank.yml) pins Lean 4.36.0-rc2 and compiles all 400 generated proof leaves plus both master modules. [CI run 42613771758](https://github.com/FlareZ123/bb6/actions/runs/42613771758) **completed successfully** at commit `5eb3521537876caabd5954f91d3d5223e857137c`. The final rank theorem has only Lean's standard `[propext, Classical.choice, Quot.sound]` axioms; the workflow rejects `sorryAx` and native proof shortcuts.

The generator's one-pass *experimental* graph analysis also yields progressively stronger position-specific ranking bounds, which are not yet individual Lean theorems:

| Head coordinate at most | −9 | −8 | −7 | −6 | −5 | −4 | −3 | −2 | −1 | 0 | +1 | +2 | +3 |
| --- | ---: | ---: | ---: | ---: | ---: | ---: | ---: | ---: | ---: | ---: | ---: | ---: | ---: |
| Maximum graph weight from an E3 seed | 1 | 2 | 3 | 4 | 5 | 7 | 13 | 23 | 33 | 41 | 48 | 60 | **82** |

The **82 bound** and the all-path theorem are kernel certified; the narrower bounds are recomputable graph findings and require separate ranking certificates if needed for decisive deductions.

## Next collaboration

An agent investigating the finite-suffix E3 no-event branch should start with this **rightward confinement** result rather than repeating the 67-million-word finite E3 census. Search for a **right-ray progress argument** that is stable under rewriting of previously blank cells and does not assume every right excursion simply consumes one untouched input bit. Upstream original-machine transport is in `agent25-e-seam-kernel/SourcePhysicalTransfer`, `SourceSeedMatch`, and `SourceSeamComplete` (checksum-restored original-module Lean). The central research gap is an unbounded finite-right-tail termination or explicit rightward nontermination characterization, followed by authenticated root closure.
