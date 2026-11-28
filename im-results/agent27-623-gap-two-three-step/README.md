# All-scale necessary terminal strips for machine #623

**Source accepted.** The genuine blank-root section iteration can terminate only if it visits a state D(u,v) with m=min(u,v), L=max(u,v), and an integer n>=10 such that
`3^(n-1)-3 <= m < 3^n-3`, and either
`|L-13m| <= 35n+93` or `|4L-7m| <= 35n+93`.
A stronger **source-accepted** orientation-specific statement now replaces the common width:
`|L-13m| <= 35n+89` **or** `|4L-7m| <= 23n+51`. It follows by preserving the tighter original-source right-output errors (maximal 14n+12) while the left-output errors can be as large as 26n+46. The authentic six-state nonhalting reduction is `target_halt_implies_thin_strip`. This is still a necessary condition only: root avoidance is not proved.

In particular, avoiding either pair of source-certified strips at all such root visits would imply nontermination.

## Proof chain

1. For a successful even-first-counter source step D(u,v)→D(x,y), n>=4 and min(u,v)+3<3^n imply y<=3min(u,v)+6n+9. This covers ordinary and exceptional sectors.
2. For a three-step terminal chain q→p→h→none, min(q)<=19679 implies mass(q)<=1004761. The root checkpoint at 47 has mass 1423655, and run(49) succeeds; strict mass growth and forward persistence of failure give a contradiction.
3. The exceptional q=(a,a-2) branch is impossible at every scale: for a>=32, use k=floor(a/8), a<3^k, x<=k and y>=3a+2 for the successor p. Thus y>=16x+24, contradicting the penultimate corridor. The small case reduces to root visits 0..7. Zero-coordinate q is already excluded by step 2.
4. On the four ordinary sectors at n>=10, the successor bound and penultimate corridor supply the two scale budgets for Agent49's terminal ratio-four source theorems. The source old-ray signed gap estimates and the terminal ratio-four windows cancel to the two strip inequalities above. Both orientations are included, and the near-sector orientation transfer is proved using the lower scale bound.
5. Every finite section failure yields such a three-step terminal chain, because the first three visits survive. The scale existence lemma covers every integer m>=19680.

## Verification

- [AllScaleSuccessorBoundSource.lean](AllScaleSuccessorBoundSource.lean) and [GapTwoThreeStepSource.lean](GapTwoThreeStepSource.lean): full original-source [CI 45744605999](https://github.com/FlareZ123/bb6/actions/runs/45744605999).
- [ThreeStepStripArithmetic.lean](ThreeStepStripArithmetic.lean): standalone kernel-checked arithmetic in Lean 4.36.0-rc2.
- [ThreeStepStripSource.lean](ThreeStepStripSource.lean): the stronger `target_halt_implies_thin_strip` has been accepted by [CI 46087395455](https://github.com/FlareZ123/bb6/actions/runs/46087395455), from commit 4ffd343e, against the unchanged original machine and pinned Lean; no `sorryAx`.
- [ThreeStepStripN11Source.lean](ThreeStepStripN11Source.lean) and [ThreeStepStripN13Source.lean](ThreeStepStripN13Source.lean): independent first three root depth-band exclusions composed with this gate, **source CI pending**; the n=11,12 witness file from Agent48 was an uncompiled draft when imported.
- [ThreeStepStripWeightedSource.lean](ThreeStepStripWeightedSource.lean): stronger **original-source verified** weighted-cocycle necessary halting gate `26n+118 / 17n+78` accepted by [CI 46088110538](https://github.com/FlareZ123/bb6/actions/runs/46088110538), commit 10fdc2f0. This proof activates the exact ternary budget using the previous source-certified coarse root strip. No `sorryAx`.
- [DrainWeightedFirstCoupledSource.lean](DrainWeightedFirstCoupledSource.lean): **unverified candidate** strengthening of Agent22's exact weighted depth theorem, coupling the *same* outer count `r` to both `aa≤a+r` and conservation. Enables one-sided reduction. Source CI pending.
- [ThreeStepStripTerminalSharpSource.lean](ThreeStepStripTerminalSharpSource.lean), [ThreeStepStripTerminalUltraSource.lean](ThreeStepStripTerminalUltraSource.lean), [ThreeStepStripWeightedUltraSource.lean](ThreeStepStripWeightedUltraSource.lean), and [ThreeStepStripWeightedSkewSource.lean](ThreeStepStripWeightedSkewSource.lean): successive **unverified** mass-sensitive and one-sided sharper candidates. Proposed uniform `23n+124 /14n+67`, and asymmetric `[-7n-48,23n+114] / [-10n-43,14n+67]` (shared outer-count refinement). CI is pending; do not cite these widths as theorems yet.
- [ThreeStepStripSource.lean](ThreeStepStripSource.lean): theorem `run_none_implies_strip` and contrapositive `run_nontermination_of_strip_avoidance` accepted by [CI 45745521684](https://github.com/FlareZ123/bb6/actions/runs/45745521684), pin fdda65ed4197a0c32fbb7420a749d134f5aa5bf2. Original machine revision c86f15861709b76042998c5211c7b2f83991621b, Lean 4.35.0-rc4. CI checks absence of sorryAx. The exact run47/run49 numerical checkpoints use native_decide (explicit trusted computation), not ordinary kernel evaluation.

## Remaining mathematical obligation

Prove avoidance on the actual infinite root orbit, not just finite replay. The source already supplies the bridge from the authentic six-state machine's halting to the terminal-strip condition. The strips are exactly the old-ray cancellation directions g-9m and 4g+9m for g=L-4m. This permits the synchronization approach in Agent1's dossier to use the checked asymmetric widths above rather than an assumed sharper bound. No global BB(6) result follows without root avoidance.
