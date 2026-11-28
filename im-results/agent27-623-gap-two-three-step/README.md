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
- [ThreeStepStripTerminalSharpSource.lean](ThreeStepStripTerminalSharpSource.lean), [ThreeStepStripTerminalUltraSource.lean](ThreeStepStripTerminalUltraSource.lean), and [ThreeStepStripWeightedUltraSource.lean](ThreeStepStripWeightedUltraSource.lean): **source-verified** mass-sensitive halting gate `23n+124 / 14n+67`, accepted by [CI 46088823348](https://github.com/FlareZ123/bb6/actions/runs/46088823348) at commit `8c4c9b7a` against pinned original source; no `sorryAx`. Critically, the terminal parent's even-near sector can use `a≥n+3` to recover a 6n+27 right-output window.
- [ThreeStepStripWeightedSkewSource.lean](ThreeStepStripWeightedSkewSource.lean), [ThreeStepStripTerminalSkewSource.lean](ThreeStepStripTerminalSkewSource.lean), and [ThreeStepStripWeightedTightSkewSource.lean](ThreeStepStripWeightedTightSkewSource.lean): **not yet source-verified** asymmetric signed-gate candidate. Intermediate `[-7n-48,23n+114] /[-10n-43,14n+67]`; strongest target `[-3n-5,23n+111] /[-10n-40,10n+55]`. The common outer drain count `r` also controls the output first-counter raise; unlike independent width bounds, this is an exact coupling. Pending CI target `weighted-tight-skew`. Do not cite these as theorems before accepted.
- [ThreeStepStripSource.lean](ThreeStepStripSource.lean): theorem `run_none_implies_strip` and contrapositive `run_nontermination_of_strip_avoidance` accepted by [CI 45745521684](https://github.com/FlareZ123/bb6/actions/runs/45745521684), pin fdda65ed4197a0c32fbb7420a749d134f5aa5bf2. Original machine revision c86f15861709b76042998c5211c7b2f83991621b, Lean 4.35.0-rc4. CI checks absence of sorryAx. The exact run47/run49 numerical checkpoints use native_decide (explicit trusted computation), not ordinary kernel evaluation.

## Remaining mathematical obligation

Prove avoidance on the actual infinite root orbit, not just finite replay. The source already supplies the bridge from the authentic six-state machine's halting to the terminal-strip condition. The strips are exactly the old-ray cancellation directions g-9m and 4g+9m for g=L-4m. This permits the synchronization approach in Agent1's dossier to use the checked asymmetric widths above rather than an assumed sharper bound. No global BB(6) result follows without root avoidance.


## Fourth-predecessor inverse-ray reduction (new Lean candidates; CI acceptance pending)

The exact original-source B-drain identity gives a useful *one-step inverse
transport* of the source-accepted necessary three-predecessor gate. Let
\`m=min(u,v)\`, \`L=max(u,v)\` for a genuine root predecessor
\`D(u,v) -> D(x,y)\`, and let \`N\` bound the input ternary block. When the
ordinary-sector budget is available, the source Lean proof constructs **one
shared drain count** \`r\` and an exact sector constant \`c ∈ {4,5,8}\`:
\`\`\`
r <= N
x+m <= L+r+4
L <= x+m+N+6
2*x+y = 2*L+m+c+2*r
\`\`\`
Thus \`x≈L-m\`, \`y≈3m\` with signed, *coupled* errors; the proof does
not multiply independent one-sided worst cases. Pulling the tight terminal
rays \`max(x,y)≈13min(x,y)\` and \`4max(x,y)≈7min(x,y)\` backwards
yields exactly four possible predecessor centre ratios
\`L/m ≈ 40, 16/13, 25/4, 19/7\`.

The strongest candidate \`coupledFourRayCone N n u v\` is a disjunction
of the following **one-sided** inequalities (unverified as a complete Lean
source theorem until its workflow succeeds):

| Ray | Upper inequality | Lower inequality |
| --- | --- | --- |
| 40 | \`L <= 40m + 53N+23n+377\` | \`40m <= L + N+3n+61\` |
| 16/13 | \`13L <= 16m + 17N+3n+103\` | \`16m <= 13L + 13N+23n+167\` |
| 25/4 | \`4L <= 25m + 32N+10n+219\` | \`25m <= 4L + 4N+10n+84\` |
| 19/7 | \`7L <= 19m + 23N+10n+162\` | \`19m <= 7L + 7N+10n+99\` |

The new **fourth-predecessor physical-source candidate** attempts to
discharge the budget, sector, gap-two, and scale prerequisites for
*every* real root predecessor. Its key unconditional source inequalities
are \`x <= max(u,v)+3\` and \`min(u,v)+4 <= y\` for any successful even-first
source transition, while the upper logarithmic estimate is
\`y <= 3min(u,v)+4N+20\`. The conclusion, **if accepted**, is

\`\`\`
BusyBeaver.IsHalt target →
  ∃ t u v n, run t = some (.D u v) ∧
    n >= 13 ∧ coupledFourRayCone (n+3) n u v
\`\`\`

The published \`n>=13\` depth premise depends on repairing nine originally
non-reducing finite \`decide\` root checkpoints to \`native_decide\` in
[RootMassGapN11N12.lean](../agent48-623-budget-composition/RootMassGapN11N12.lean).
Unlike kernel-only \`decide\`, those finite source oracles introduce native
reflection axioms; report them explicitly rather than calling the entire
end-to-end chain pure kernel computation.

Lean modules: [FourRayInverseConeSource.lean](FourRayInverseConeSource.lean),
[FourRayPhysicalSource.lean](FourRayPhysicalSource.lean), and
[FourRayCoupledSource.lean](FourRayCoupledSource.lean).
CI: existing parameterized original-Cryptids-source workflow
[agent27-623-n10-mass-gap.yml](../../.github/workflows/agent27-623-n10-mass-gap.yml),
target \`four-ray-full\`, against pinned Cryptids
\`c86f15861709b76042998c5211c7b2f83991621b\`.
**No #623 nonhalting theorem or BB(6) maximality proof follows without
showing all-time blank-root avoidance of these four cones.**


## Fifth-predecessor scale-corrected eight-ray reduction (candidate; CI pending)

The new [GenericSourceRayTransport.lean](GenericSourceRayTransport.lean),
[EightRaySource.lean](EightRaySource.lean), and
[FifthRayPhysicalSource.lean](FifthRayPhysicalSource.lean) extend the coupled
four-ray reduction by one authentic blank-root predecessor. The eight
candidate ray centres are
\`121, 43/40, 61/13, 55/16, 79/4, 37/25, 64/7, 40/19\`.
Their exact one-sided inequalities and the equivalent signed-coordinate
covector tree are recorded in
[EightRaySignedCovectorTree.md](EightRaySignedCovectorTree.md).

A review found that an unscaled statement
\`∀ n≥13, ¬ eightRayCone (n+3) n u v\` would be vacuous for a fixed state:
all cone error widths grow with n. The physical theorem has therefore been
corrected to retain the scale at the same authentic fifth predecessor:
\`\`\`
n ≥ 13
3^(n-4) ≤ min(u,v)
min(u,v)+3 < 3^(n+3)
\`\`\`
The lower bound is derived from the terminal predecessor's
\`3^(n-1)-3 ≤ min(x,y)\` and the two exact-source bounds
\`y ≤ 3*min(source)+4*(n+3)+20\`, giving
\`3^(n-1) ≤ 9*min(u,v)+16*(n+3)+83\`.
The n≥13 growth lemma supplies
\`18*3^(n-4) ≥ 16*(n+3)+83\`, hence
\`3^(n-4) ≤ min(u,v)\`. The upper scale bound is transported from the
existing strict-mass and terminal upper-scale estimates.

The avoidance corollary now quantifies only over this scale-corrected
interval, rather than arbitrary n. This repairs the logical vacuity but
does **not** establish all-time avoidance. The end-to-end target
\`eight-ray-full\` in the existing
[agent27-623-n10-mass-gap.yml](../../.github/workflows/agent27-623-n10-mass-gap.yml)
compiles the full original-source dependency chain and the three new modules;
source CI is pending. Do not cite the eight-ray theorem as accepted until
that run succeeds.


The generic coupled transport now carries an explicit source-positivity
hypothesis \`0<u\`. This is not redundant with the current \`OrdinaryStep\`
inductive: its \`oddNear\` constructor does not itself encode positivity,
while the weighted drain identity uses \`u-1\`. The physical blank-root
bridge supplies \`0<u\` from the transported positive minimum; the
conditional generic lemmas do not silently assume it.
