# All-scale necessary terminal strips for machine #623

**Source accepted.** The genuine blank-root section iteration can terminate only if it visits a state D(u,v) with m=min(u,v), L=max(u,v), and an integer n>=10 such that
`3^(n-1)-3 <= m < 3^n-3`, and either
`|L-13m| <= 35n+93` or `|4L-7m| <= 35n+93`.
In particular, avoiding these two strips at all such root visits implies section nontermination. This is a necessary condition, not a proof of avoidance or a BB(6) upper bound.

## Proof chain

1. For a successful even-first-counter source step D(u,v)→D(x,y), n>=4 and min(u,v)+3<3^n imply y<=3min(u,v)+6n+9. This covers ordinary and exceptional sectors.
2. For a three-step terminal chain q→p→h→none, min(q)<=19679 implies mass(q)<=1004761. The root checkpoint at 47 has mass 1423655, and run(49) succeeds; strict mass growth and forward persistence of failure give a contradiction.
3. The exceptional q=(a,a-2) branch is impossible at every scale: for a>=32, use k=floor(a/8), a<3^k, x<=k and y>=3a+2 for the successor p. Thus y>=16x+24, contradicting the penultimate corridor. The small case reduces to root visits 0..7. Zero-coordinate q is already excluded by step 2.
4. On the four ordinary sectors at n>=10, the successor bound and penultimate corridor supply the two scale budgets for Agent49's terminal ratio-four source theorems. The source old-ray signed gap estimates and the terminal ratio-four windows cancel to the two strip inequalities above. Both orientations are included, and the near-sector orientation transfer is proved using the lower scale bound.
5. Every finite section failure yields such a three-step terminal chain, because the first three visits survive. The scale existence lemma covers every integer m>=19680.

## Verification

- [AllScaleSuccessorBoundSource.lean](AllScaleSuccessorBoundSource.lean) and [GapTwoThreeStepSource.lean](GapTwoThreeStepSource.lean): full original-source [CI 45744605999](https://github.com/FlareZ123/bb6/actions/runs/45744605999).
- [ThreeStepStripArithmetic.lean](ThreeStepStripArithmetic.lean): standalone kernel-checked arithmetic in Lean 4.36.0-rc2.
- [ThreeStepStripSource.lean](ThreeStepStripSource.lean): theorem `run_none_implies_strip` and contrapositive `run_nontermination_of_strip_avoidance` accepted by [CI 45745521684](https://github.com/FlareZ123/bb6/actions/runs/45745521684), pin fdda65ed4197a0c32fbb7420a749d134f5aa5bf2. Original machine revision c86f15861709b76042998c5211c7b2f83991621b, Lean 4.35.0-rc4. CI checks absence of sorryAx. The exact run47/run49 numerical checkpoints use native_decide (explicit trusted computation), not ordinary kernel evaluation.

## Remaining mathematical obligation

Prove avoidance on the actual infinite root orbit, not just finite replay, and connect section nontermination to the original machine nonhalting theorem. The strips are exactly the old-ray cancellation directions g-9m and 4g+9m for g=L-4m. This permits the synchronization approach in Agent1's dossier to use the checked width 35n+93 rather than an assumed sharper bound. No global BB(6) result follows without root avoidance.
